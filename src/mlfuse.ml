open Log
open Printf
open Sys
open Word
open Interp
open Unix
open Bigarray

let mem_state = ref (Log.ms_empty, (Cache.cache_empty, ()))
let fuselock = Mutex.create ()

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
  | _ -> S_REG

let stat_file (W ino) (W len) { ByteFile.BYTEFILE.coq_FMTime = wmtime; coq_FType = wtype; coq_FDev = wdev } =
  let (W fmtime) = wmtime in
  let (W ftype) = wtype in
  let (W fdev) = wdev in
  {
    Unix.LargeFile.st_nlink = 1;
    st_kind = attr_to_kind (Z.to_int ftype);
    st_perm = 0o755;
    st_size = Z.to_int64 len;
    st_dev = 0;
    st_ino = Z.to_int ino;
    st_uid = 0;
    st_gid = 0;
    st_rdev = Z.to_int fdev;
    st_atime = 0.0;
    st_mtime = Z.to_float fmtime;
    st_ctime = 0.0;
  }

let fscq_getattr ds fsxp path =
  Mutex.lock fuselock;
  let r = lookup ds fsxp path in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "stat", path))
  | Some (ino, true) -> Mutex.unlock fuselock; stat_dir ino
  | Some (ino, false) ->
    let (attr, ()) = run_fs ds (FS.file_get_attr fsxp ino) in
    let (len, ()) = run_fs ds (FS.file_get_sz fsxp ino) in
    Mutex.unlock fuselock;
    stat_file ino len attr

let fscq_readdir ds fsxp path _ =
  Mutex.lock fuselock;
  let r = lookup ds fsxp path in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "readdir", path))
  | Some (ino, true) ->
    let (files, ()) = run_fs ds (FS.readdir fsxp ino) in
    Mutex.unlock fuselock;
    List.append ["."; ".."] (List.map (fun (name, (ino, isdir)) -> string_implode name) files)
  | Some (_, false) -> Mutex.unlock fuselock; raise (Unix_error (ENOTDIR, "readdir", path))

let fscq_fopen ds fsxp path flags =
  Mutex.lock fuselock;
  let r = lookup ds fsxp path in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "fopen", path))
  | Some (_, true) -> Mutex.unlock fuselock; raise (Unix_error (EISDIR, "fopen", path))
  | Some (W ino, false) -> Mutex.unlock fuselock; Some (Z.to_int ino)

let fscq_mknod ds fsxp path kind perm rdev =
  Mutex.lock fuselock;
  let fn = string_explode (Filename.basename path) in
  let r = lookup ds fsxp (Filename.dirname path) in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "mknod", path))
  | Some (_, false) -> Mutex.unlock fuselock; raise (Unix_error (ENOTDIR, "mknod", path))
  | Some (dnum, true) ->
    let (r, ()) = ( match kind with
                    | S_REG  -> run_fs ds (FS.create fsxp dnum fn)
                    | S_SOCK -> run_fs ds (FS.mkdev fsxp dnum fn (W (Z.of_int 1)) (W (Z.of_int 0)))
                    | S_FIFO -> run_fs ds (FS.mkdev fsxp dnum fn (W (Z.of_int 2)) (W (Z.of_int 0)))
                    | S_BLK  -> run_fs ds (FS.mkdev fsxp dnum fn (W (Z.of_int 3)) (W (Z.of_int rdev)))
                    | S_CHR  -> run_fs ds (FS.mkdev fsxp dnum fn (W (Z.of_int 4)) (W (Z.of_int rdev)))
                    | _ -> Mutex.unlock fuselock; raise (Unix_error (EIO, "mknod", path))
                  ) in
    match r with
    | None -> Mutex.unlock fuselock; raise (Unix_error (EIO, "mknod", path))
    | Some _ -> Mutex.unlock fuselock; ()

let fscq_mkdir ds fsxp path mode =
  Mutex.lock fuselock;
  let fn = string_explode (Filename.basename path) in
  let r = lookup ds fsxp (Filename.dirname path) in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "mkdir", path))
  | Some (_, false) -> Mutex.unlock fuselock; raise (Unix_error (ENOTDIR, "mkdir", path))
  | Some (dnum, true) ->
    let (r, ()) = run_fs ds (FS.mkdir fsxp dnum fn) in
    match r with
    | None -> Mutex.unlock fuselock; raise (Unix_error (EIO, "mkdir", path))
    | Some _ -> Mutex.unlock fuselock; ()

let fscq_read ds fsxp path buf ofs ino =
  Mutex.lock fuselock;
  let inum = W (Z.of_int ino) in
  let zoff = Z.of_int64 ofs in
  let zlen = Z.of_int (Array1.dim buf) in
  let (res, ()) = run_fs ds (FS.read_bytes fsxp inum zoff zlen) in
  match res with
  | ByteFile.BYTEFILE.Coq_len_bytes (cc, (W bytes)) ->
    let strbytes = Z.to_bits bytes in
    String.iteri (fun i c -> Array1.set buf i c) strbytes;
    Mutex.unlock fuselock;
    Z.to_int cc

let fscq_write ds fsxp path buf ofs ino =
  Mutex.lock fuselock;
  let inum = W (Z.of_int ino) in
  let zoff = Z.of_int64 ofs in
  let len = Array1.dim buf in
  let strbytes = String.create len in
  for i = 0 to len-1 do
    String.set strbytes i (Array1.get buf i)
  done;
  let zbytes = Z.of_bits strbytes in
  let (res, ()) = run_fs ds (FS.append fsxp inum zoff (Z.of_int len) (W zbytes)) in
  Mutex.unlock fuselock;
  if res then len else raise (Unix_error (EIO, "write", path))

let fscq_rename ds fsxp src dst =
  Mutex.lock fuselock;
  let src_fn = string_explode (Filename.basename src) in
  let src_dn = split_path_coq (Filename.dirname src) in
  let dst_fn = string_explode (Filename.basename dst) in
  let dst_dn = split_path_coq (Filename.dirname dst) in
  let (r, ()) = run_fs ds (FS.rename fsxp (FSLayout.coq_FSXPRootInum fsxp)
                           src_dn src_fn dst_dn dst_fn) in
  Mutex.unlock fuselock;
  if r then () else raise (Unix_error (EIO, "rename", src))

let fscq_unlink ds fsxp path =
  Mutex.lock fuselock;
  let fn = string_explode (Filename.basename path) in
  let r = lookup ds fsxp (Filename.dirname path) in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "unlink", path))
  | Some (_, false) -> Mutex.unlock fuselock; raise (Unix_error (ENOTDIR, "unlink", path))
  | Some (dnum, true) ->
    let (r, ()) = run_fs ds (FS.delete fsxp dnum fn) in
    Mutex.unlock fuselock;
    if r then () else raise (Unix_error (EIO, "unlink", path))

let fscq_truncate ds fsxp path len =
  Mutex.lock fuselock;
  let r = lookup ds fsxp path in
  match r with
  | None -> Mutex.unlock fuselock; raise (Unix_error (ENOENT, "unlink", path))
  | Some (_, true) -> Mutex.unlock fuselock; raise (Unix_error (EISDIR, "unlink", path))
  | Some (inum, false) ->
    let (r, ()) = run_fs ds (FS.file_resize fsxp inum (Z.of_int64 len)) in
    Mutex.unlock fuselock;
    if r then () else raise (Unix_error (EIO, "truncate", path))

let fscq_chmod ds fsxp path mode =
  ()

let fscq_chown ds fsxp path uid gid =
  ()

let fscq_statfs ds fsxp path =
  Mutex.lock fuselock;
  let ((W freeblocks), ((W freeinodes), ())) = run_fs ds (FS.statfs fsxp) in
  Mutex.unlock fuselock;
  let (W block_bitmaps) = FSLayout.coq_BmapNBlocks (FSLayout.coq_FSXPBlockAlloc fsxp) in
  let (W inode_bitmaps) = FSLayout.coq_BmapNBlocks (FSLayout.coq_FSXPInodeAlloc fsxp) in
  {
    Unix_util.f_bsize = Int64.of_int Interp.blockbytes;
    f_frsize = Int64.of_int Interp.blockbytes;
    f_blocks = Int64.of_int (8 * Interp.blockbytes * (Z.to_int block_bitmaps));
    f_bfree = Z.to_int64 freeblocks;
    f_bavail = Z.to_int64 freeblocks;
    f_files = Int64.of_int (8 * Interp.blockbytes * (Z.to_int inode_bitmaps));
    f_ffree = Z.to_int64 freeblocks;
    f_favail = Z.to_int64 freeblocks;
    f_fsid = Int64.of_int 0;
    f_flag = Int64.of_int 0;
    f_namemax = Z.to_int64 DirName.SDIR.namelen;
  }

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
        read = fscq_read ds fsxp;
        write = fscq_write ds fsxp;
        rename = fscq_rename ds fsxp;
        unlink = fscq_unlink ds fsxp;
        rmdir = fscq_unlink ds fsxp;
        truncate = fscq_truncate ds fsxp;
        chmod = fscq_chmod ds fsxp;
        chown = fscq_chown ds fsxp;
        statfs = fscq_statfs ds fsxp;
    }
