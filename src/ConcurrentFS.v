Require Import CCL.
Require Import OptimisticTranslator OptimisticFS.

Require AsyncFS.
(* imports for DirTreeRep.rep *)
Import Log FSLayout Inode.INODE BFile.

(* various other imports *)
Import BFILE.
Import SuperBlock.
Import GenSepN.

Require Import HomeDirProtocol.

Record FSParams St :=
  { fs_cache : CacheParams St;
    fsmem: var (Mem St) memstate;
    fstree: var (Abstraction St) dirtree;
    (* static configurations: *)
    homedirs: TID -> list string;
    fsparams: fs_xparams; }.

Definition fs_invariant St (FP: FSParams St) sigma :=
    let tree := get_var (fstree FP) (Sigma.s sigma) in
    let fsxp := fsparams FP in
    let mscs := get_var (fsmem FP) (Sigma.mem sigma) in
    let CP := fs_cache FP in
    exists ds ilist frees,
      LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs) (Sigma.hm sigma)
              (seq_disk CP sigma) /\
      (DirTreeRep.rep fsxp Pred.emp tree ilist frees)
        (list2nmem (ds!!)).

Definition fs_guarantee St (FP: FSParams St) tid sigma sigma' :=
    CacheRep (fs_cache FP) empty_writebuffer sigma /\
    CacheRep (fs_cache FP) empty_writebuffer sigma' /\
    fs_invariant FP sigma /\
    fs_invariant FP sigma' /\
    let tree := get_var (fstree FP) (Sigma.s sigma) in
    let tree' := get_var (fstree FP) (Sigma.s sigma') in
    homedir_guarantee tid (homedirs FP) tree tree'.

Section ConcurrentFS.

  Context {St:StateTypes}.
  Variable G:Protocol St.
  Variable FP:FSParams St.
  Variable fsG: forall tid sigma sigma',
      G tid sigma sigma ->
      fs_guarantee FP tid sigma sigma'.

  Definition get_fsmem := get_var (fsmem FP).
  Definition set_fsmem := set_var (fsmem FP).
  Definition upd_fstree s update := set_var (fstree FP) s (update (get_var (fstree FP) s)).

  Definition fsxp := fsparams FP.

  Definition guard {T} (r: Result T) : {exists v, r=Success v} + {r=Failed}.
    destruct r; eauto.
  Defined.

  Definition retry_syscall T
             (p: memstate -> @cprog St (Result (memstate * T) * WriteBuffer))
             (update: TID -> dirtree -> dirtree)
    : cprog (Result T) :=
    retry guard (m <- Get;
                   do '(r, wb) <- p (get_fsmem m);
                   match r with
                   | Success (ms', r) =>
                     _ <- CacheCommit (fs_cache FP) wb;
                       m <- Get;
                       _ <- Assgn (set_fsmem m ms');
                       _ <- GhostUpdate (fun tid s => upd_fstree s (update tid));
                       Ret (Success r)
                   | Failed =>
                     _ <- CacheAbort (fs_cache FP) wb;
                       _ <- Yield;
                       Ret Failed
                   end).

  Definition file_get_attr inum :=
    retry_syscall (fun mscs =>
                     OptFS.file_get_attr (fs_cache FP) fsxp inum mscs empty_writebuffer)
                  (fun _ => id).

End ConcurrentFS.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)