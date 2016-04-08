open Log
open Printf
open Sys
open Word
open Interp
open Unix

let finish = function
  | () ->
    Printf.printf "Done\n";
    Prog.Done ();;

Printf.printf "Running..\n";;
run_dcode (Prog.Done ())

let do_fopen path flags =
  raise (Unix_error (ENOENT,"open",path))

let _ =
  Fuse.main Sys.argv
    {
      Fuse.default_operations with
        fopen = do_fopen;
    }
