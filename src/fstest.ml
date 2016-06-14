open Log
open Printf
open Sys
open Word
open Interp

let finish = function
  | () ->
    Printf.printf "Done\n";
    Prog.Done ();;

Printf.printf "Running..\n";;
run_dcode (Prog.Done ())

