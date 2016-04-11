open Log
open Printf
open Sys
open Word
open Interp
open Unix

let do_mkfs fn =
  let ds = init_disk fn in
  Printf.printf "Initializing filesystem in %s\n" fn;
  let res = run_prog ds (FS.mkfs (W (Big.of_int 1)) (W (Big.of_int 1))) in
  ( match res with
    | Err _ -> Printf.printf "mkfs failed"
    | OK (_, (fsxp, ())) ->
      let (W nblocks) = FSLayout.coq_FSXPMaxBlock fsxp in
      Printf.printf "Initialization OK, %d blocks\n" (Big.to_int nblocks);
      try
        set_size_disk ds (Big.to_int nblocks)
      with
        e -> Printf.printf "Error resizing disk image: %s\n" (Printexc.to_string e)
      );
  close_disk ds

let _ =
  match Sys.argv with
  | [| _ ; fn |] ->
    do_mkfs fn
  | _ ->
    Printf.printf "Usage: %s diskpath\n" Sys.argv.(0)
