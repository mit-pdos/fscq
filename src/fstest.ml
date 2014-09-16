open Log
open Printf
open Sys
open Word

let disk_fn = "disk.img"

let read_disk b =
  let ic = open_in_gen [Open_rdonly;Open_creat] 0o666 disk_fn in
  seek_in ic b;
  try
    let v = input_byte ic in
    close_in ic;
    v
  with
    End_of_file -> close_in ic; 0

let write_disk b v =
  let oc = open_out_gen [Open_wronly;Open_creat] 0o666 disk_fn in
  seek_out oc b;
  output_byte oc v;
  close_out oc

let rec run_dcode = function
  | Prog.Done t ->
    ()
  | Prog.Read (a, rx) ->
    let v = read_disk (wordToN 64 a) in
    Printf.printf "read(%d): %d\n" a v;
    run_dcode (rx v)
  | Prog.Write (a, v, rx) ->
    Printf.printf "write(%d, %d)\n" a v;
    write_disk a v;
    run_dcode (rx ());;

let xp =
  { coq_LogLength = 20;
    coq_LogCommit = 21;
    coq_LogStart = 22;
    coq_LogLen = 20 };;

let finish = function
  | () ->
    Printf.printf "Done\n";
    Prog.Done ();;

try Sys.remove disk_fn with Sys_error _ -> ();;

Printf.printf "Running..\n";;
run_dcode
  (Log.init xp (fun _ ->
   Log.coq_begin xp (fun _ ->
   Log.abort xp finish)));;

