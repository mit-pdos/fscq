open Unix
module AsyncFS = AsyncFS.AFS

let cachesize = Z.of_int 100_000
(* there also are some hardcoded "4096" in the code below... *)
let blocksize = (Z.to_int AsyncDisk.Valulen.valulen) / 8

type mscs = BFile.BFILE.memstate
type fsxp = FSLayout.fs_xparams

type state = {
  ds : Disk.state;
  mutable mscs : mscs;
  fsxp : fsxp;
}

type fs_stats = {
  blocksize : int64;
  blocks : int64;
  free_blocks : int64;
  files : int64;
  free_files : int64;
  namemax : int64;
}

let run (p: mscs -> (mscs * 'a) Prog.prog) (st: state) =
  let mscs', ret = Interp.run st.ds (p st.mscs) in
  st.mscs <- mscs';
  ret

(* Error conversion to Unix *)

let unix_of_errno (e: Errno.coq_Errno): Unix.error =
  match e with
  | Errno.ELOGOVERFLOW -> EIO
  | Errno.ENOTDIR -> ENOTDIR
  | Errno.EISDIR -> EISDIR
  | Errno.ENOENT -> ENOENT
  | Errno.EFBIG -> EFBIG
  | Errno.ENAMETOOLONG -> ENAMETOOLONG
  | Errno.EEXIST -> EEXIST
  | Errno.ENOSPCBLOCK -> ENOSPC
  | Errno.ENOSPCINODE -> ENOSPC
  | Errno.ENOTEMPTY -> ENOTEMPTY
  | Errno.EINVAL -> EINVAL

let check_errno fname arg = function
  | Errno.OK () -> ()
  | Errno.Err e -> raise (Unix_error (unix_of_errno e, fname, arg))

(* path helpers *)

(* TODO less ad-hoc path handling?
   what kind of paths can we get from fuse? *)

let split_directories (path: string) =
  if path = "/" then []
  else List.tl @@ String.split_on_char '/' path

let rec take_drop_last = function
  | [] -> raise (Invalid_argument "take_drop_last")
  | [x] -> ([], x)
  | x :: xs ->
    let (xs', last) = take_drop_last xs in
    x :: xs', last

let split_dirs_file (path: string) =
  take_drop_last (split_directories path)

let explode s =
  String.to_seq s |> List.of_seq

let implode l =
  String.of_seq @@ List.to_seq l

(* Int64 helpers *)

module Int64 = struct
  include Int64
  let ( * ) = mul
  let ( - ) = sub
  let ( + ) = add
  let ( / ) = div
end

(* stat helpers *)

let stat_dir (inum: Z.t): Unix.LargeFile.stats =
  Unix.LargeFile.{
    st_dev = 0; (* ignored by fuse *)
    st_ino = Z.to_int inum; (* ignored by fuse *)
    st_kind = S_DIR;
    st_perm = 0o755;
    st_nlink = 2;
    st_uid = 0;
    st_gid = 0;
    st_rdev = 0;
    st_size = 4096L;
    st_atime = 0.;
    st_mtime = 0.;
    st_ctime = 0.;
  }

let kind_of_attr attr =
  let W w = Inode.INODE.coq_AType attr in
  if Z.(equal w zero) then S_REG else S_SOCK

let stat_file (inum: Z.t) (attr: Obj.t) =
  Unix.LargeFile.{
    st_dev = 0; (* ignored by fuse *)
    st_ino = Z.to_int inum; (* ignored by fuse *)
    st_rdev = 0;
    st_kind = kind_of_attr attr;
    st_perm = 0o777;
    st_nlink = 1;
    st_uid = 0;
    st_gid = 0;
    st_size =
      Z.to_int64 @@ Word.wordToNat 64
      @@ Inode.INODE.coq_ABytes attr;
    st_atime = 0.;
    st_mtime =
      Z.to_float @@ Word.wordToNat 32
      @@ Inode.INODE.coq_AMTime attr;
    st_ctime = 0.;
  }

(* operations *)

let getattr (st: state) (path: string) =
  let nameparts = split_directories path in
  let res, () = run (
    AsyncFS.lookup st.fsxp
      st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode nameparts)
  ) st in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "stat", path))
  | Errno.OK (inum, true (*isdir*)) ->
    stat_dir inum
  | Errno.OK (inum, false) ->
    let attr, () = run (AsyncFS.file_get_attr st.fsxp inum) st in
    stat_file inum attr

let fopen (st: state) (path: string) (flags: Unix.open_flag list) =
  let nameparts = split_directories path in
  let res, () = run (
    AsyncFS.lookup st.fsxp
      st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode nameparts)
  ) st in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "fopen", path))
  | Errno.OK (_, true (*isdir*)) ->
    raise (Unix_error (EISDIR, "fopen", path))
  | Errno.OK (inum, false) ->
    if List.mem O_TRUNC flags then begin
      let res, () = run (AsyncFS.file_truncate st.fsxp inum Z.zero) st in
      check_errno "fopen" path res;
      let res, () = run (AsyncFS.file_set_sz st.fsxp inum (Word.W Z.zero)) st in
      check_errno "fopen" path res
    end;
    Some (Z.to_int inum) (* XXX? what about the None case? *)

let mknod (st: state) (path: string) kind =
  let dirparts, filename = split_dirs_file path in
  let res, () = run (
    AsyncFS.lookup st.fsxp
      st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode dirparts)
  ) st in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "mknod", path))
  | Errno.OK (_, false(*isdir*)) ->
    raise (Unix_error (ENOTDIR, "mknod", path))
  | Errno.OK (dnum, true) ->
    let res, () =
      match kind with
      | S_REG -> run (AsyncFS.create st.fsxp dnum (explode filename)) st
      | S_SOCK -> run (AsyncFS.mksock st.fsxp dnum (explode filename)) st
      | _ -> raise (Unix_error (EINVAL, "mknod", path))
    in
    match res with
    | Errno.Err _ -> raise (Unix_error (EIO, "mknod", path))
    | Errno.OK _ -> ()

let mkdir (st: state) path =
  let dirparts, filename = split_dirs_file path in
  let res, () = run (
    AsyncFS.lookup st.fsxp
      st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode dirparts)
  ) st in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "mkdir", path))
  | Errno.OK (_, false(*isdir*)) ->
    raise (Unix_error (ENOTDIR, "mkdir", path))
  | Errno.OK (dnum, true) ->
    let res, () = run (AsyncFS.mkdir st.fsxp dnum (explode filename)) st in
    match res with
    | Errno.Err _ -> raise (Unix_error (EIO, "mkdir", path))
    | Errno.OK _ -> ()

let unlink (st: state) path =
  let dirparts, filename = split_dirs_file path in
  let res, () = run (
    AsyncFS.lookup st.fsxp
      st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode dirparts)
  ) st in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "mkdir", path))
  | Errno.OK (_, false(*isdir*)) ->
    raise (Unix_error (ENOTDIR, "unlink", path))
  | Errno.OK (dnum, true) ->
    let res, () = run (AsyncFS.delete st.fsxp dnum (explode filename)) st in
    match res with
    | Errno.Err _ -> raise (Unix_error (EIO, "unlink", path))
    | Errno.OK () -> ()

(* MISSING IN OCAMLFUSE *)
let destroy (st: state) =
  let () = run (AsyncFS.umount st.fsxp) st in
  Disk.close st.ds;
  Disk.print_stats st.ds

let iter_ranges off count f =
  let startblock = off / blocksize in
  let endblock = (off + count - 1) / blocksize in
  for blk = startblock to endblock do
    let startoff =
      if blk = startblock then off mod blocksize
      else 0
    in
    let endoff =
      if blk = endblock then (off + count - 1) mod blocksize + 1
      else blocksize
    in
    f ~blknum:blk ~off_in_blk:startoff ~count_from_off:(endoff - startoff)
  done

let read_range st inum buffer off bytecount =
  let pos = ref 0 in
  iter_ranges off bytecount
    (fun ~blknum ~off_in_blk ~count_from_off ->
       let Word.W wbuf, () =
         run (AsyncFS.read_fblock st.fsxp inum (Z.of_int blknum)) st in
       let bits = Z.to_bits wbuf in
       for i = 0 to count_from_off - 1 do
         buffer.{!pos + i} <- bits.[off_in_blk + i]
       done;
       pos := !pos + count_from_off
    )

let read (st: state) _path buffer (offset: int64) inum =
  let bytecount = Bigarray.Array1.size_in_bytes buffer in
  let inum = Z.of_int inum in
  let Word.W len, () = run (AsyncFS.file_get_sz st.fsxp inum) st in
  let offset = Int64.to_int offset in (* XXX is this dangerous? *)
  let len = Z.to_int len in
  let offset' = min offset len in
  let bytecount' = min bytecount (len - offset') in
  read_range st inum buffer offset' bytecount';
  bytecount'

let bytes_of_bigarray_range ba pos len =
  let buf = Bytes.create len in
  for i = 0 to len - 1 do
    Bytes.set buf i ba.{pos + i}
  done;
  Bytes.unsafe_to_string buf

let write_piece st ~inum ~do_log ~init_len ~buffer ~offset ~blknum ~off_in_blk ~count_from_off =
  let bufoff = (blknum * blocksize) + off_in_blk - offset in
  (* data in buffer is in range [bufoff;bufoff+count_from_off) *)
  let piece_bytes =
    if count_from_off = blocksize then
      (* whole block writes don't need read-modify-write *)
      bytes_of_bigarray_range buffer bufoff count_from_off
    else begin
      let old_block =
        if (init_len <= blknum * blocksize)
        || (offset = 0 && init_len <= blknum * blocksize + count_from_off)
        then
          (* If we are doing a partial block write, we don't need RMW in two cases:
             (1.) The file was smaller than the start of this block.
             (2.) The partial write of this block starts immediately at offset 0
                  in this block and writes all the way up to (and maybe past)
                  the original end of the file. *)
          String.make blocksize (Char.chr 0)
        else begin
          let Word.W block, () = run (AsyncFS.read_fblock st.fsxp inum (Z.of_int blknum)) st in
          Z.to_bits block
        end
      in
      let buf = Bytes.of_string old_block in
      for i = 0 to count_from_off - 1 do
        Bytes.set buf (off_in_blk + i) buffer.{bufoff + i}
      done;
      Bytes.unsafe_to_string buf
    end
  in
  let piece_word = Word.W (Z.of_bits piece_bytes) in
  if do_log then (
    let (_:bool), () = run (AsyncFS.update_fblock st.fsxp inum (Z.of_int blknum) piece_word) st in
    ()
  ) else (
    let () = run (AsyncFS.update_fblock_d st.fsxp inum (Z.of_int blknum) piece_word) st in
    ()
  );
  count_from_off (* number of bytes written *)

let write (st: state) path buffer (offset: int64) datalen inum =
  let Word.W len, () = run (AsyncFS.file_get_sz st.fsxp (Z.of_int inum)) st in
  let len = Z.to_int len in
  let offset = Int64.to_int offset in (* XXX dangerous? *)
  let inum = Z.of_int inum in
  let endpos = offset + datalen in
  let okspc, do_log =
    if len < endpos then (
      let res, () =
        run (AsyncFS.file_truncate st.fsxp inum (Z.of_int ((endpos + 4095) / 4096))) st in
      (* Appends to a file need to be logged so that the truncate and write
         happen in the log. Technically these are different transactions but
         FSCQ never breaks up the log. *)
      (res, true)
    ) else (
      if offset mod 4096 = 0 && datalen mod 4096 = 0 && datalen > 4096 * 5 then
        (* block is large and aligned -> bypass write *)
        (Errno.OK (), false)
      else
        (* NOTE: logged overwrites to the middle of the file are disabled since
           they are currently not synced by fdatasync, which is unexpected from
           a user looking at the Linux API. Thus, regardless of the offset and
           length of the write, we always do a direct write. *)
        (Errno.OK (), false)
    )
  in
  match okspc with
  | Errno.Err _ -> raise (Unix_error (EIO(*?*), "write", path))
  | Errno.OK () ->
    let bytes_written = ref 0 in
    iter_ranges offset datalen (fun ~blknum ~off_in_blk ~count_from_off ->
      let nwritten =
        write_piece st ~inum ~do_log ~init_len:len ~buffer ~offset
          ~blknum ~off_in_blk ~count_from_off in
      bytes_written := !bytes_written + nwritten
    );
    let okspc =
      if len < endpos then (
        let ok, () = run (AsyncFS.file_set_sz st.fsxp inum (Word.W (Z.of_int endpos))) st in
        ok
      ) else Errno.OK ()
    in
    match okspc with
    | Errno.OK () -> !bytes_written
    | Errno.Err _ -> raise (Unix_error (ENOSPC, "write", path))

let truncate (st: state) (path: string) (size: int64) =
  let nameparts = split_directories path in
  let res, () = run (
    AsyncFS.lookup st.fsxp st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode nameparts)
  ) st
  in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "unlink", path))
  | Errno.OK (_, true (*isdir*)) -> raise (Unix_error (EISDIR, "unlink", path))
  | Errno.OK (inum, false (*isdir*)) ->
    (* Note that this function is unverified *)
    let res, () = run (AsyncFS.ftruncate st.fsxp inum (Z.of_int64 size)) st in
    match res with
    | Errno.OK () -> ()
    | Errno.Err _ -> raise (Unix_error (EIO, "truncate", path))

let opendir (st: state) path _ =
  let nameparts = split_directories path in
  let res, () = run (
    AsyncFS.lookup st.fsxp st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode nameparts)
  ) st
  in
  match res with
  | Errno.Err _ -> raise (Unix_error (ENOENT, "opendir", path))
  | Errno.OK (_, false (*isdir*)) ->
    raise (Unix_error (ENOTDIR, "opendir", path))
  | Errno.OK (dnum, true) ->
    Some (Z.to_int dnum) (* What about the None case? *)

let readdir (st: state) _path dnum =
  (* XXX ocamlfuse does not require file stats? *)
  (* let mkstat ctx (fn, (inum, isdir)) = *)
  (*   if isdir then (fn, stat_dir ctx inum) *)
  (*   else ( *)
  (*     let attr, () = run (AsyncFS.file_get_attr st.fsxp inum) st in *)
  (*     (fn, stat_file ctx inum attr) *)
  (*   ) *)
  (* in *)
  (* let ctx = Fuse.get_context () in *)
  let dnum = Z.of_int dnum in
  let files, () = run (AsyncFS.readdir st.fsxp dnum) st in
  (* let files_stat = List.map (mkstat ctx) files in *)
  let files = List.map (fun (fn, _) -> implode fn) files in
  ["."; ".."] @ files

let rename (st: state) path_src path_dst =
  let srcparts, srcname = split_dirs_file path_src in
  let dstparts, dstname = split_dirs_file path_dst in
  let res, () = run (
    AsyncFS.rename st.fsxp
      st.fsxp.FSLayout.coq_FSXPRootInum
      (List.map explode srcparts) (explode srcname)
      (List.map explode dstparts) (explode dstname)
  ) st in
  match res with
  | Errno.OK () -> ()
  | Errno.Err _ -> raise (Unix_error (EIO, "rename", path_src))

let sync_file (st: state) _path isdatasync inum =
  run (AsyncFS.file_sync st.fsxp (Z.of_int inum)) st;
  if not isdatasync then (
    (* full sync *)
    run (AsyncFS.tree_sync st.fsxp) st
  )

let sync_dir (st: state) _ _ _ : unit =
  run (AsyncFS.tree_sync st.fsxp) st

let statfs (st: state) _ =
  let freeblocks, (freeinodes, ()) = run (AsyncFS.statfs st.fsxp) st in
  let block_bitmaps = FSLayout.(coq_BmapNBlocks st.fsxp.coq_FSXPBlockAlloc1) in
  let inode_bitmaps = FSLayout.(coq_BmapNBlocks st.fsxp.coq_FSXPInodeAlloc) in
  { blocksize = 4096L;
    blocks = Int64.(8L * 4096L * Z.to_int64 block_bitmaps);
    free_blocks = Z.to_int64 freeblocks;
    files = Int64.(8L * 4096L * Z.to_int64 inode_bitmaps);
    free_files = Z.to_int64 freeinodes;
    namemax = Z.to_int64 DirName.SDIR.namelen; }

let load_fs disk =
  let ds = Disk.init disk in
  match Interp.run ds (AsyncFS.recover cachesize) with
  | Errno.Err e -> Errno.Err e
  | Errno.OK (mscs, fsxp) ->
    Errno.OK { ds; mscs; fsxp }
