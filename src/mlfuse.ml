open Log
open Printf
open Sys
open Word
open Interp
open Unix

let mem_state = ref (Log.ms_empty, (Cache.cache_empty, ()))

let run_fs ds prog =
  try
    let (ms', r) = run_prog ds (prog !mem_state) in
    mem_state := ms';
    r
  with
    e -> Printf.printf "run_fs exception: %s\n%!" (Printexc.to_string e); raise e

let string_explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let string_implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l

let split_path s = Str.split (Str.regexp "/+") s

let split_path_coq s = List.map string_explode (split_path s)

let lookup ds fsxp path =
  let nameparts = split_path_coq path in
  Printf.printf "namei %s\n" (String.concat "/" (List.map string_implode nameparts));
  let (r, ()) = run_fs ds (FS.lookup fsxp (FSLayout.coq_FSXPRootInum fsxp) nameparts) in
  r

let stat_dir (W ino) =
  {
    Unix.LargeFile.st_nlink = 2;
    st_kind = S_DIR;
    st_perm = 0o755;
    st_size = Int64.of_int 4096;
    st_dev = 0;
    st_ino = Z.to_int ino;
    st_uid = 0;
    st_gid = 0;
    st_rdev = 0;
    st_atime = 0.0;
    st_mtime = 0.0;
    st_ctime = 0.0;
  }

let attr_to_kind ftype =
  match ftype with
  | 0 -> S_REG
  | 1 -> S_SOCK
  | 2 -> S_FIFO
  | 3 -> S_BLK
  | 4 -> S_CHR
  | _ -> raise (Failure "attr_to_kind")

let stat_file (W ino) (W len) { ByteFile.BYTEFILE.coq_FMTime = wmtime; coq_FType = wtype; coq_FDev = wdev } =
  let (W fmtime) = wmtime in
  let (W ftype) = wtype in
  let (W fdev) = wdev in
  {
    Unix.LargeFile.st_nlink = 1;
    st_kind = attr_to_kind (Z.to_int ftype);
    st_perm = 0o755;
    st_size = Z.to_int64 len;
    st_dev = Z.to_int fdev;
    st_ino = Z.to_int ino;
    st_uid = 0;
    st_gid = 0;
    st_rdev = 0;
    st_atime = 0.0;
    st_mtime = Z.to_float fmtime;
    st_ctime = 0.0;
  }

let fscq_getattr ds fsxp path =
  let r = lookup ds fsxp path in
  match r with
  | None -> raise (Unix_error (ENOENT, "stat", path))
  | Some (ino, true) -> stat_dir ino
  | Some (ino, false) ->
    let (attr, ()) = run_fs ds (FS.file_get_attr fsxp ino) in
    let (len, ()) = run_fs ds (FS.file_get_sz fsxp ino) in
    stat_file ino len attr

let fscq_readdir ds fsxp path _ =
  let r = lookup ds fsxp path in
  match r with
  | None -> raise (Unix_error (ENOENT, "readdir", path))
  | Some (ino, true) ->
    let (files, ()) = run_fs ds (FS.readdir fsxp ino) in
    List.append ["."; ".."] (List.map (fun (name, (ino, isdir)) -> string_implode name) files)
  | Some (_, false) -> raise (Unix_error (ENOTDIR, "readdir", path))

let fscq_fopen ds fsxp path flags =
  let r = lookup ds fsxp path in
  match r with
  | None -> raise (Unix_error (ENOENT, "fopen", path))
  | Some (_, true) -> raise (Unix_error (EISDIR, "fopen", path))
  | Some (W ino, false) -> Some (Z.to_int ino)

let fscq_mknod ds fsxp path mode =
  let fn = Filename.basename path in
  let r = lookup ds fsxp (Filename.dirname path) in
  Printf.printf "mknod %d\n%!" mode;
  ()

let fscq_mkdir ds fsxp path mode =
  Printf.printf "fscq_mkdir %s\n%!" path;
  let fn = Filename.basename path in
  Printf.printf "fscq_mkdir %s %s\n%!" path fn;
  let r = lookup ds fsxp (Filename.dirname path) in
  Printf.printf "fscq_mkdir %s %s lookup done\n%!" path fn;
  match r with
  | None -> raise (Unix_error (ENOENT, "mkdir", path))
  | Some (_, false) -> raise (Unix_error (ENOTDIR, "mkdir", path))
  | Some (dnum, true) ->
    Printf.printf "fscq_mkdir %s %s dir ok\n%!" path fn;
    let fn_coq = string_explode fn in
    Printf.printf "fscq_mkdir %s %s explode done\n%!" path fn;
    let (r, ()) = run_fs ds (FS.mkdir fsxp dnum fn_coq) in
    Printf.printf "fscq_mkdir %s %s mkdir done\n%!" path fn;
    match r with
    | None -> raise (Unix_error (EIO, "mkdir", path))
    | Some _ -> Printf.printf "fscq_mkdir OK\n%!"; ()

let _ =
  if (Array.length Sys.argv < 2) then Printf.printf "Usage: %s disk -f /mnt/fscq\n" Sys.argv.(0);
  let diskfn = Sys.argv.(1) in
  let ds = init_disk diskfn in
  let (mscs, (fsxp, ())) = run_prog ds FS.recover in
  Printf.printf "Recovery OK\n%!";
  mem_state := mscs;
  let fuseargv = Array.append [| Sys.argv.(0) |] (Array.sub Sys.argv 2 ((Array.length Sys.argv) - 2)) in
  Fuse.main fuseargv
    {
      Fuse.default_operations with
        getattr = fscq_getattr ds fsxp;
        readdir = fscq_readdir ds fsxp;
        fopen = fscq_fopen ds fsxp;
        mknod = fscq_mknod ds fsxp;
        mkdir = fscq_mkdir ds fsxp;
    }
