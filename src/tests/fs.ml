open HoareLogicN
open Printf
open Sys

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
  | HoareLogicN.Halt_ r ->
    r
  | HoareLogicN.Crash_ ->
    Printf.printf "crash\n";
    raise Exit
  | HoareLogicN.Read b ->
    let v = read_disk b in
    Printf.printf "read(%d): %d\n" b v;
    Obj.magic v
  | HoareLogicN.Write (b, v) ->
    Printf.printf "write(%d, %d)\n" b v;
    write_disk b v;
    Obj.magic ()
  | HoareLogicN.Seq (p1, p2) ->
    let v = run_dcode (Obj.magic p1) in
    run_dcode (Obj.magic p2 v);;

let xp =
  { coq_DataStart = 0;
    coq_DataLen = 20;
    coq_LogLength = 20;
    coq_LogCommit = 21;
    coq_LogStart = 22;
    coq_LogLen = 20 };;

Printf.printf "Running write_two_blocks on disk..\n";;

try Sys.remove disk_fn with Sys_error _ -> ();;

run_dcode (write_two_blocks xp 3 4 5 6);;

