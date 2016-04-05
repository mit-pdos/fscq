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

  Vincenzo Ciancia

  applejack@users.sf.net
  vincenzo_ml@yahoo.it
*)

open Result

external read_noexn : Unix.file_descr -> (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t -> int result = "unix_util_read"
external write_noexn : Unix.file_descr -> (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t -> int result = "unix_util_write"

external int_of_file_descr : Unix.file_descr -> int = "unix_util_int_of_file_descr"
external file_descr_of_int : int -> Unix.file_descr = "unix_util_file_descr_of_int"

(* Statvfs code inspired by statfs code by Richard Jones and Damien Doligez, see:

   http://caml.inria.fr/pub/ml-archives/caml-list/2005/07/bb434b103b1cdbbec3c832d9a72af9a3.fr.html

   http://caml.inria.fr/pub/ml-archives/caml-list/2005/07/49ee60ceadbcbbc84b0bce54ad5949b6.fr.html
   
   TODO: learn about caml_failwith (see their code)
*)

type statvfs = {
  f_bsize : int64;
  f_frsize : int64;
  f_blocks : int64;
  f_bfree : int64;
  f_bavail : int64;
  f_files : int64;
  f_ffree : int64;
  f_favail : int64;
  f_fsid : int64;
  f_flag : int64;
  f_namemax : int64;
}

external statvfs_noexn : string -> statvfs result = "unix_util_statvfs"

let statvfs path = 
  match statvfs_noexn path with
      Ok res ->  res
    | Bad err -> raise (Unix.Unix_error (err,"statvfs",""))

external fchdir : Unix.file_descr -> unit = "unix_util_fchdir"

let read fd buf =
  match read_noexn fd buf with
      Ok res -> res
    | Bad err -> raise (Unix.Unix_error (err,"read",""))

let write fd buf =
  match write_noexn fd buf with
      Ok res -> res
    | Bad err -> raise (Unix.Unix_error (err,"read",""))
