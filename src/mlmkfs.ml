open Log
open Printf
open Sys
open Word
open Interp
open Unix

let do_mkfs fn =
  init_disk fn;
  Printf.printf "Initializing filesystem in %s\n" fn;
  (* let res = run_dcode (FS.mkfs  ... *)
  close_disk

let _ =
  match Sys.argv with
  | [| _ ; fn |] ->
    do_mkfs fn
  | _ ->
    Printf.printf "Usage: %s diskpath\n" Sys.argv.(0)
