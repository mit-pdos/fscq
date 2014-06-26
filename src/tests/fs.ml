open Bank
open DiskLog
open Trans
open Printf
open Datatypes

let run_dcode_coq dcode =
  DiskLog.dexec dcode { coq_DSProg = dcode;
                        coq_DSDataDisk = Storage.st_init;
                        coq_DSLogDisk = Storage.st_init }

let choose_disk d =
  match d with
  | NDataDisk -> "disk-data"
  | NLogDisk  -> "disk-log"

let read_disk d b =
  let ic = open_in_gen [Open_rdonly;Open_creat] 0o666 (choose_disk d) in
  seek_in ic b;
  try
    let v = input_byte ic in
    close_in ic;
    v
  with
    End_of_file -> close_in ic; 0

let write_disk d b v =
  let oc = open_out_gen [Open_wronly;Open_creat] 0o666 (choose_disk d) in
  seek_out oc b;
  output_byte oc v;
  close_out oc

let rec run_dcode_real p =
  match p with
  | DRead (d, b, rx) -> run_dcode_real (rx (read_disk d b))
  | DWrite (d, b, v, rx) -> write_disk d b v; run_dcode_real rx
  | DHalt -> 0

let acode = (Bank.ASetAcct (1, Bank.initial,
            (Bank.ASetAcct (2, Bank.initial,
            (Bank.ATransfer (1, 2, 10,
             Bank.AHalt))))));;

let tcode = Trans.compile_at acode;;

let pcode = MemLog.compile_tp tcode;;

let dcode = DiskLog.compile_pd pcode;;

run_dcode_coq dcode;;

run_dcode_real dcode;;

