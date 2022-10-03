module Errno = Fscq.Errno
module AsyncFS = Fscq.AsyncFS
module FSLayout = Fscq.FSLayout

let cachesize = Z.of_int 100_000

let do_mkfs fn =
  let ds = Fscq.Disk.init fn in
  Printf.printf "Initializing filesystem in %s\n" fn;
  let mkfs_prog = AsyncFS.AFS.mkfs cachesize (Z.of_int 4) (Z.of_int 1) (Z.of_int 256) in
  begin match Fscq.Interp.run ds mkfs_prog with
  | Errno.Err _ -> Printf.printf "mkfs failed"
  | Errno.OK (_, fsxp) ->
    Printf.printf "Initialization OK, %s blocks\n"
      (Z.to_string fsxp.FSLayout.coq_FSXPMaxBlock);
    Printf.printf "  === disk layout addresses ===\n";
    Printf.printf "  superblock: 0\n";
    Printf.printf "  data blocks start: 1\n";
    Printf.printf "  inode blocks start: %s\n"
      (Z.to_string (Z.succ FSLayout.(coq_IXStart fsxp.coq_FSXPInode)));
    Printf.printf "  log header: %s\n"
      (Z.format "%x" FSLayout.(coq_LogHeader fsxp.coq_FSXPLog));
    Printf.printf "  log data start: %s\n"
      (Z.format "%x" FSLayout.(coq_LogData fsxp.coq_FSXPLog))
  end;
  Fscq.Disk.close ds

let _ =
  match Sys.argv with
  | [| _ ; fn |] ->
    do_mkfs fn
  | _ ->
    Printf.printf "Usage: %s <disk path>\n" Sys.argv.(0)
