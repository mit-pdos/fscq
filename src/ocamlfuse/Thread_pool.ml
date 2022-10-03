(*
  This file is part of the "OCamlFuse" library.

  OCamlFuse is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation (version 2 of the License).
  
  OCamlFuse is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with OCamlFuse.  See the file LICENSE.  If you haven't received
  a copy of the GNU General Public License, write to:
  
  Free Software Foundation, Inc.,
  59 Temple Place, Suite 330, Boston, MA
  02111-1307  USA

  Alessandro Strada

  alessandro.strada@gmail.com
*)

type t = {
  max_threads : int;
  lock : Mutex.t;
  condition : Condition.t;
  table : (int, Thread.t) Hashtbl.t;
}

let create ?(max_threads = 128) () =
  {
    max_threads;
    lock = Mutex.create ();
    condition = Condition.create ();
    table = Hashtbl.create max_threads;
  }

let signal_work_done thread_id pool =
  Mutex.lock pool.lock;
  try
    Hashtbl.remove pool.table thread_id;
    Condition.signal pool.condition;
    Mutex.unlock pool.lock
  with _ -> Mutex.unlock pool.lock

let add_work f x pool =
  Mutex.lock pool.lock;
  try
    while Hashtbl.length pool.table >= pool.max_threads do
      Condition.wait pool.condition pool.lock
    done;
    let f' x =
      let thread = Thread.self () in
      let thread_id = Thread.id thread in
      let _ = f x in
      signal_work_done thread_id pool
    in
    let thread = Thread.create f' x in
    let thread_id = Thread.id thread in
    Hashtbl.add pool.table thread_id thread;
    Mutex.unlock pool.lock
  with _ -> Mutex.unlock pool.lock

let shutdown pool = Hashtbl.iter (fun _ thread -> Thread.join thread) pool.table
