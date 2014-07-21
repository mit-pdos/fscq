open Disk
open DiskLog
open Printf
open Datatypes
open FileSpec
open FsLayout

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

let rec run_dcode2_real p =
  match p with
  | DiskLog.DRead (d, b, rx) -> run_dcode2_real (rx (read_disk d b))
  | DiskLog.DWrite (d, b, v, rx) -> write_disk d b v; run_dcode2_real rx
  | DiskLog.DHalt -> 0

let rec run_dcode_real p =
  match p with
  | Disk.DRead (b, rx) ->
    let v = read_disk NDataDisk b in
    Printf.printf "read(%d): %d\n" b v;
    run_dcode_real (rx v)
  | Disk.DWrite (b, v, rx) ->
    Printf.printf "write(%d, %d)\n" b v;
    write_disk NDataDisk b v; run_dcode_real rx
  | Disk.DHalt -> 0

let fcode = FileSpec.FCommon (FileSpec.FAlloc,
            fun o -> match Obj.magic o with
            | None -> FileSpec.FHalt
            | Some f -> FileSpec.FCommon (FileSpec.FTrunc (f, 1),
            fun x -> FileSpec.FCommon (FileSpec.FWrite (f, 0, 7),
            fun x -> FileSpec.FHalt)));;

let dcode = FsLayout.compile_id (FsLayout.do_init (Balloc.compile_bi (Balloc.do_init (File.compile_fb fcode))));;

run_dcode_real dcode;;

