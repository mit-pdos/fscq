open Log
open Printf
open Sys
open Word
open Interp
open Unix

let mem_state = ref (Log.ms_empty, (Cache.cache_empty, ()))

let run_fs ds prog =
  let (ms', r) = run_prog ds (prog !mem_state) in
  mem_state := ms';
  r

let do_fopen path flags =
  raise (Unix_error (ENOENT,"open",path))

let _ =
  if (Array.length Sys.argv < 2) then Printf.printf "Usage: %s disk -f /mnt/fscq\n" Sys.argv.(0);
  let diskfn = Sys.argv.(1) in
  let ds = init_disk diskfn in
  let (mscs, fsxp) = run_prog ds FS.recover in
  Printf.printf "Recovery OK\n%!";
  mem_state := mscs;
  let fuseargv = Array.append [| Sys.argv.(0) |] (Array.sub Sys.argv 2 ((Array.length Sys.argv) - 2)) in
  Fuse.main fuseargv
    {
      Fuse.default_operations with
        fopen = do_fopen;
    }
