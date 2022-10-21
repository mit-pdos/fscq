module Errno = Fscq.Errno
module FSLayout = Fscq.FSLayout
module AsyncFS = Fscq.AsyncFS.AFS
module Ops = Fscq.Operations

let cachesize = Z.of_int 100_000
(* there also are many hardcoded "4096" in the rest of the code.. *)
let blocksize = (Z.to_int Fscq.AsyncDisk.Valulen.valulen) / 8

type mscs = Fscq.BFile.BFILE.memstate
type fsxp = FSLayout.fs_xparams

type state = {
  ops : Fscq.Operations.state;
  lock : Mutex.t;
}

let mk_state (ops: Ops.state) : state =
  { ops; lock = Mutex.create () }

external reraise : exn -> 'a = "%reraise"
let[@inline never] with_lock (st: state) f =
  Mutex.lock st.lock;
  match f () with
  | x ->
    Mutex.unlock st.lock;
    x
  | exception e ->
    Mutex.unlock st.lock;
    reraise e

let fscq_getattr st path =
  with_lock st @@ fun () ->
  let ctx = Fuse.get_context () in
  let stat = Fscq.Operations.getattr st.ops path in
  { stat with st_uid = ctx.uid; st_gid = ctx.gid }

let fscq_fopen st path flags =
  with_lock st @@ fun () ->
  Ops.fopen st.ops path flags

let fscq_mknod st path kind _perm _rdev =
  with_lock st @@ fun () ->
  Ops.mknod st.ops path kind

let fscq_mkdir st path _ =
  with_lock st @@ fun () ->
  Ops.mkdir st.ops path

let fscq_unlink st path =
  with_lock st @@ fun () ->
  Ops.unlink st.ops path

let fscq_read st path buffer offset inum =
  with_lock st @@ fun () ->
  Ops.read st.ops path buffer offset inum

let fscq_write st path buffer offset inum =
  with_lock st @@ fun () ->
  let buflen = Bigarray.Array1.size_in_bytes buffer in
  Ops.write st.ops path buffer offset buflen inum

let fscq_truncate st path size =
  with_lock st @@ fun () ->
  Ops.truncate st.ops path size

let fscq_opendir st path x =
  with_lock st @@ fun () ->
  Ops.opendir st.ops path x

let fscq_readdir st path dnum =
  with_lock st @@ fun () ->
  Ops.readdir st.ops path dnum

let fscq_rename st src dst =
  with_lock st @@ fun () ->
  Ops.rename st.ops src dst

let fscq_sync_file st path isdatasync inum =
  with_lock st @@ fun () ->
  Ops.sync_file st.ops path isdatasync inum

let fscq_sync_dir st x y z =
  with_lock st @@ fun () ->
  Ops.sync_dir st.ops x y z

let fscq_statfs (st: state) x =
  with_lock st @@ fun () ->
  let stats = Ops.statfs st.ops x in
  Fuse.Unix_util.{
    f_bsize = stats.blocksize;
    f_frsize = stats.blocksize; (* ??? "Fragment size, smallest addressable data size" *)
    f_blocks = stats.blocks;
    f_bfree = stats.free_blocks;
    f_bavail = stats.free_blocks;
    f_files = stats.files;
    f_ffree = stats.free_files;
    f_favail = stats.free_files; (* fuse.h says: ignored? *)
    f_fsid = 0L; (* fuse.h says: ignored? *)
    f_flag = 0L; (* fuse.h says: ignored? *)
    f_namemax = stats.namemax;
  }

let fscq_utime _path _ _ =
  ()

let fscq_chmod (_path: string) (_mode: int) =
  ()

let fscq_destroy (st: state) () =
  with_lock st @@ fun () ->
  Ops.destroy st.ops

let fscq_fuse_ops st =
  { Fuse.default_operations with
    getattr = fscq_getattr st;
    fopen = fscq_fopen st;
    (* create file : missing *)
    mknod = fscq_mknod st;
    mkdir = fscq_mkdir st;
    unlink = fscq_unlink st;
    rmdir = fscq_unlink st;
    read = fscq_read st;
    write = fscq_write st;
    truncate = fscq_truncate st;
    opendir = fscq_opendir st;
    readdir = fscq_readdir st;
    statfs = fscq_statfs st;
    destroy = fscq_destroy st;
    utime = fscq_utime;
    rename = fscq_rename st;
    chmod = fscq_chmod;
    fsync = fscq_sync_file st;
    fsyncdir = fscq_sync_dir st;
  }

(* main *)

let () =
  match Sys.argv |> Array.to_list with
  | argv0 :: disk :: _ ->
    let fuseargv = Array.append [| argv0 |] (Array.sub Sys.argv 2 ((Array.length Sys.argv) - 2)) in
    Printf.printf "Recovering file system\n%!";
    begin match Ops.load_fs disk with
      | Errno.Err _ ->
        Printf.eprintf "recovery failed; is this an FSCQ fs?\n"; exit 1
      | Errno.OK ops_st ->
        let st = mk_state ops_st in
        Printf.printf "Starting file system\n%!";
        Fuse.main fuseargv (fscq_fuse_ops st)
    end
  | _ ->
    Printf.eprintf "Usage: %s <disk file> -f <mountpoint> [other fuse options...]\n"
      Sys.argv.(0); exit 1
