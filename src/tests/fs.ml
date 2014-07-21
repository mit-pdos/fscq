open Disk
open DiskLog
open Printf
open Datatypes
open FileSpec
open FsLayout
open Sys

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
  | DiskLog.DRead (d, b, rx) ->
    let v = read_disk d b in
    Printf.printf "read(%s, %d): %d\n" (choose_disk d) b v;
    run_dcode2_real (rx v)
  | DiskLog.DWrite (d, b, v, rx) ->
    Printf.printf "write(%s, %d, %d)\n" (choose_disk d) b v;
    write_disk d b v; run_dcode2_real rx
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
            | Some f -> FileSpec.FCommon (FileSpec.FTrunc (f, 2),
            fun x -> FileSpec.FCommon (FileSpec.FWrite (f, 0, 7),
            fun x -> FileSpec.FCommon (FileSpec.FWrite (f, 1, 8),
            fun x -> FileSpec.FHalt))));;

let dcode = FsLayout.compile_id (FsLayout.do_init (Balloc.compile_bi (Balloc.do_init (File.compile_fb fcode))));;

let t2code = Trans2.T2Begin (Trans2.T2DProg (dcode, Trans2.T2Commit (Trans2.T2Halt)));;

let dcode2 = DiskLog.compile_pd (MemLog.compile_tp (Trans.compile_t2t t2code));;

Printf.printf "Running fcode on bare disk..\n";;

try Sys.remove (choose_disk NDataDisk) with Sys_error _ -> ();;

run_dcode_real dcode;;

Printf.printf "Running fcode on logged disk..\n";;

try Sys.remove (choose_disk NDataDisk) with Sys_error _ -> ();;
try Sys.remove (choose_disk NLogDisk)  with Sys_error _ -> ();;

run_dcode2_real dcode2;;

