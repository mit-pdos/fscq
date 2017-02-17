Require Import CCL.
Require Import Hashmap.
Require Import OptimisticTranslator OptimisticFS.

Require AsyncFS.
(* imports for DirTreeRep.rep *)
Import Log FSLayout Inode.INODE BFile.

(* various other imports *)
Import BFILE.
Import SuperBlock.
Import GenSepN.
Import Pred.

Require Import HomeDirProtocol.
Require Import RelationClasses.

Section ConcurrentFS.

  Context {OtherSt:StateTypes}.

  Record FsMem :=
    fsMem { fsmem: memstate;
            fs_other_mem: Mem OtherSt; }.

  Record FsAbstraction :=
    fsAbstraction { fstree: dirtree;
                    homedirs: TID -> list string;
                    fs_other_s : Abstraction OtherSt; }.

  Definition St := OptimisticCache.St
                     {| Mem := FsMem;
                        Abstraction := FsAbstraction; |}.

  Variable fsxp: fs_xparams.

  Definition get_fsmem (m: Mem St) :=
    fsmem (cache_other_mem m).
  Definition get_fstree (sigma: Sigma St) :=
    fstree (cache_other_s (Sigma.s sigma)).
  Definition get_homedirs (sigma: Sigma St) :=
    homedirs (cache_other_s (Sigma.s sigma)).

  Definition fs_rep d tree mscs hm :=
    exists ds ilist frees,
      LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs) hm d /\
      (DirTreeRep.rep fsxp Pred.emp tree ilist frees)
        (list2nmem (ds!!)).

  Definition fs_invariant (sigma: Sigma St) :=
    let tree := get_fstree sigma in
    let mscs := get_fsmem (Sigma.mem sigma) in
    CacheRep empty_writebuffer sigma /\
    fs_rep (seq_disk sigma) tree mscs (Sigma.hm sigma).

  Definition fs_guarantee tid (sigma sigma':Sigma St) :=
    fs_invariant sigma /\
    fs_invariant sigma' /\
    let tree := get_fstree sigma in
    let tree' := get_fstree sigma' in
    homedir_guarantee tid (get_homedirs sigma) tree tree' /\
    get_homedirs sigma' = get_homedirs sigma.

  Theorem fs_rely_same_fstree : forall tid sigma sigma',
      fs_invariant sigma ->
      fs_invariant sigma' ->
      get_fstree sigma' = get_fstree sigma ->
      get_homedirs sigma' = get_homedirs sigma ->
      Rely fs_guarantee tid sigma sigma'.
  Proof.
    unfold fs_guarantee; intros.
    constructor.
    exists (S tid); intuition.
    rewrite H1.
    apply homedir_guar_preorder.
  Qed.

  Lemma Rely_homedir_rely : forall tid sigma sigma',
      Rely fs_guarantee tid sigma sigma' ->
      homedir_rely tid (get_homedirs sigma) (get_fstree sigma) (get_fstree sigma') /\
      get_homedirs sigma' = get_homedirs sigma.
  Proof.
    unfold fs_guarantee, homedir_guarantee, homedir_rely.
    induction 1; intros; repeat deex; intuition (congruence || eauto).
  Qed.

  Theorem fs_guarantee_refl : forall tid sigma,
      fs_invariant sigma ->
      fs_guarantee tid sigma sigma.
  Proof.
    unfold fs_guarantee; intuition.
  Qed.

  Lemma fs_guarantee_trans : forall tid sigma sigma' sigma'',
      fs_guarantee tid sigma sigma' ->
      fs_guarantee tid sigma' sigma'' ->
      fs_guarantee tid sigma sigma''.
  Proof.
    unfold fs_guarantee; intuition eauto; try congruence.
    etransitivity; eauto.
    replace (get_homedirs sigma).
    auto.
  Qed.

  Lemma fs_guarantee_set_l : forall tid sigma sigma' l,
      fs_guarantee tid sigma sigma' ->
      fs_guarantee tid sigma (Sigma.set_l sigma' l).
  Proof.
    unfold fs_guarantee, fs_invariant.
    destruct sigma, sigma'; simpl in *; intuition.
  Qed.

  Theorem fs_rely_invariant : forall tid sigma sigma',
      fs_invariant sigma ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_invariant sigma'.
  Proof.
    induction 2; intros; repeat deex; intuition eauto.
    unfold fs_guarantee in *; intuition.
  Qed.

  (* TODO: eventually abstract away protocol *)

  (* TODO: provide mem/abstraction setter/updater in cache, and here: callers
  should not have to deal with listing out the other parts of these records *)

  Definition set_fsmem (m: Mem St) fsm : Mem St :=
    let other := fs_other_mem (cache_other_mem m) in
    cacheMem (St:={|Mem:=FsMem|}) (cache m)
             (fsMem fsm other).

  Definition upd_fstree update (s: Abstraction St) : Abstraction St :=
    let fsS0 := cache_other_s s in
    let other := fs_other_s fsS0 in
    cacheS (St:={|Abstraction:=FsAbstraction|}) (vdisk_committed s) (vdisk s)
           (fsAbstraction (update (fstree fsS0)) (homedirs fsS0) other).

  Inductive SyscallResult {T} :=
  | Done (v:T)
  | TryAgain
  | SyscallFailed.

  Arguments SyscallResult T : clear implicits.

  Definition OptimisticProg T :=
    memstate ->
    LockState -> WriteBuffer ->
    cprog (St:=St) (Result (memstate * T) * WriteBuffer).

  (* Execute p assuming it is read-only. This program could distinguish between
  failures that require filling the cache [Failure (CacheMiss a)] and failures
  that require upgrading to a write lock [Failure WriteRequired], but currently
  does not do so. *)
  Definition readonly_syscall T (p: OptimisticProg T) : cprog (SyscallResult T) :=
    _ <- GetReadLock;
      m <- Get;
      (* for read-only syscalls, the returned write buffer is always the same
       as the input *)
      do '(r, _) <- p (get_fsmem m) ReadLock empty_writebuffer;
      _ <- ReleaseReadLock;
      match r with
      | Success (ms', r) => Ret (Done r)
      | Failure e =>
        match e with
        | Unsupported => Ret SyscallFailed
        | _ => Ret TryAgain
        end
      end.

  Definition guard {T} (r:SyscallResult T)
    : {(exists v, r = Done v) \/ r = SyscallFailed}
      + {r = TryAgain}.
  Proof.
    destruct r; eauto.
  Defined.

  Definition write_syscall T (p: OptimisticProg T) (update: dirtree -> dirtree) :
    cprog (SyscallResult T) :=
    retry guard
          (_ <- GetWriteLock;
             m <- Get;
             do '(r, wb) <- p (get_fsmem m) WriteLock empty_writebuffer;
             match r with
             | Success (ms', r) =>
               _ <- CacheCommit wb;
                 _ <- Assgn (set_fsmem m ms');
                 _ <- GhostUpdate (fun _ s => upd_fstree update s);
                 _ <- Unlock;
                 Ret (Done r)
             | Failure e =>
               match e with
               | CacheMiss a =>
                 _ <- CacheAbort;
                   _ <- Unlock;
                   (* TODO: [Yield a] here when the noop Yield is added *)
                   Ret TryAgain
               | WriteRequired => (* unreachable - have write lock *)
                 Ret SyscallFailed
               | Unsupported =>
                 Ret SyscallFailed
               end
             end).

  Definition retry_syscall T (p: OptimisticProg T) (update: dirtree -> dirtree) :=
    r <- readonly_syscall p;
      match r with
      | Done v => Ret (Done v)
      | TryAgain => write_syscall p update
      | SyscallFailed => Ret SyscallFailed
      end.

  Record FsSpecParams T :=
    { fs_pre : dirtree -> Prop;
      fs_post : T -> Prop;
      fs_mscs_R : memstate -> memstate -> Prop;
      fs_dirup : dirtree -> dirtree; }.

  Definition FsSpec A T := A -> FsSpecParams T.

  Definition fs_spec A T (fsspec: FsSpec A T) :
    memstate -> LockState ->
    Spec A (Result (memstate * T) * WriteBuffer) :=
    fun mscs l a '(sigma_i, sigma) =>
      {| precondition :=
           mscs = get_fsmem (Sigma.mem sigma) /\
           CacheRep empty_writebuffer sigma /\
           Sigma.l sigma = l /\
           ReadPermission l /\
           fs_rep (seq_disk sigma) (get_fstree sigma) mscs (Sigma.hm sigma) /\
           fs_pre (fsspec a) (get_fstree sigma);
         postcondition :=
           fun '(sigma_i', sigma') '(r, wb') =>
             CacheRep wb' sigma' /\
             Sigma.l sigma' = l /\
             locally_modified sigma sigma' /\
             vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
             (l = ReadLock -> vdisk (Sigma.s sigma') = vdisk (Sigma.s sigma)) /\
             (l = ReadLock -> CacheRep empty_writebuffer sigma') /\
             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
             match r with
             | Success (mscs', r) =>
               fs_post (fsspec a) r /\
               fs_mscs_R (fsspec a) mscs mscs' /\
               fs_rep (seq_disk sigma') (fs_dirup (fsspec a) (get_fstree sigma')) mscs' (Sigma.hm sigma')
             | Failure e =>
               (l = WriteLock -> e <> WriteRequired) /\
               (* if we revert the disk, we can restore the fs_rep *)
               fs_rep (add_buffers (vdisk_committed (Sigma.s sigma'))) (get_fstree sigma') mscs (Sigma.hm sigma') /\
               get_fsmem (Sigma.mem sigma') = get_fsmem (Sigma.mem sigma) /\
               get_fstree sigma' = get_fstree sigma
             end /\
             sigma_i' = sigma_i; |}.

  Definition precondition_stable A T (fsspec: FsSpec A T) homes tid :=
    forall a tree tree', fs_pre (fsspec a) tree ->
                    homedir_rely tid homes tree tree' ->
                    fs_pre (fsspec a) tree'.

  Definition mscs_nocommit A T (fsspec: FsSpec A T) :=
    forall a mscs mscs',
      fs_mscs_R (fsspec a) mscs mscs' ->
      (forall d tree hm, fs_rep d tree mscs' hm ->
                    fs_rep d tree mscs hm).

  Theorem mscs_nocommit_msalloc_eq : forall mscs mscs',
      MSAlloc mscs' = MSAlloc mscs ->
      (forall d tree hm, fs_rep d tree mscs' hm ->
                    fs_rep d tree mscs hm).
  Proof.
    unfold fs_rep; intros; repeat deex.
    exists ds, ilist, frees.
    intuition.
    (* doesn't appear true, but is needed to avoid committing state for read-only syscalls *)
    (* TODO: prove an appropriate theorem for LOG.rep that avoids needing to
    commit mscs (the mscs will change, due to the cache, but the LOG.rep should
    remain true with the old one) *)
  Abort.

  Lemma precondition_stable_rely : forall A T (spec: FsSpec A T) tid a sigma sigma',
      precondition_stable spec (get_homedirs sigma) tid ->
      fs_pre (spec a) (get_fstree sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_pre (spec a) (get_fstree sigma').
  Proof.
    unfold precondition_stable; intros.
    eapply H in H0; eauto.
    apply Rely_homedir_rely in H1; intuition.
  Qed.

  Definition readonly_spec A T (fsspec: FsSpec A T) tid :
    Spec (St:=St) A (SyscallResult T) :=
    fun a '(sigma_i, sigma) =>
      {| precondition :=
           fs_invariant sigma /\
           Sigma.l sigma = Free /\
           let tree := get_fstree sigma in
           fs_pre (fsspec a) tree /\
           precondition_stable fsspec (get_homedirs sigma) tid /\
           mscs_nocommit fsspec;
         postcondition :=
           fun '(sigma_i', sigma') r =>
             fs_invariant sigma' /\
             Rely fs_guarantee tid sigma sigma' /\
             Sigma.l sigma' = Free /\
             match r with
             | Done v => fs_post (fsspec a) v
             | TryAgain => True
             | SyscallFailed => True
             end /\
             fs_guarantee tid sigma_i' sigma'|}.

  Lemma fs_rep_hashmap_incr : forall vd tree mscs hm hm',
      fs_rep vd tree mscs hm ->
      hashmap_le hm hm' ->
      fs_rep vd tree mscs hm'.
  Proof.
    unfold fs_rep; intros.
    repeat deex.
    exists ds, ilist, frees; intuition eauto.
    eapply LOG.rep_hashmap_subset; eauto.
  Qed.

  Hint Resolve fs_rep_hashmap_incr.

  Theorem readonly_syscall_ok : forall T (p: OptimisticProg T) A (fsspec: FsSpec A T) tid,
      (forall mscs, cprog_spec fs_guarantee tid
                          (fs_spec fsspec mscs ReadLock) (p mscs ReadLock empty_writebuffer)) ->
      cprog_spec fs_guarantee tid
                 (readonly_spec fsspec tid) (readonly_syscall p).
  Proof.
    intros.
    unfold readonly_syscall.

    step.
    destruct st as [sigma_i sigma]; simpl in *.
    intuition eauto.

    step.
    deex.
    destruct sigma'; simpl; auto.

    assert (fs_invariant sigma').
    eapply fs_rely_invariant; eauto.

    match goal with
    | [ H: Rely fs_guarantee _ _ _ |- _ ] =>
      pose proof H;
        eapply precondition_stable_rely in H; eauto
    end.

    step_using ltac:(apply H).
    eexists; simpl; intuition eauto.

    unfold fs_invariant in *; intuition eauto.
    destruct sigma'; simpl in *; eauto.
    destruct sigma'; simpl in *; eauto.
    unfold fs_invariant in *; intuition eauto.
    destruct sigma'; simpl in *; eauto.
    unfold get_fstree in *; destruct sigma'; simpl in *; eauto.

    step.
    intuition eauto.
    match goal with
    | [ u:unit |- _ ] => destruct u
    end.

    assert (fs_invariant (Sigma.set_l sigma0 Free)).
    unfold fs_invariant, locally_modified, seq_disk, get_fstree, get_fsmem in *;
      destruct sigma', sigma0; simpl in *; intuition eauto.
    repeat match goal with
           | [ H: _ = _ |- _ ] =>
             progress rewrite H in *
           end.
    eauto.

    assert (fs_guarantee tid sigma' (Sigma.set_l sigma0 Free)).
    unfold fs_guarantee, get_homedirs, get_fstree, locally_modified in *;
      destruct sigma', sigma0; simpl in *; intuition eauto.
    match goal with
    | [ |- homedir_guarantee _ _ ?tree ?tree' ] =>
      replace tree' with tree by congruence;
        reflexivity
    end.
    congruence.

    assert (fs_guarantee tid (Sigma.set_l sigma' ReadLock) (Sigma.set_l sigma0 Free)).
    destruct sigma'; simpl in *; eauto.

    assert (Rely fs_guarantee tid sigma (Sigma.set_l sigma0 Free)).
    eapply Rely_trans; eauto.
    constructor.
    exists (S tid); intuition.

    destruct a0 as [(mscs & r) | ].
    step.
    intuition eauto.
    destruct sigma0; simpl; auto.

    destruct e; step; intuition eauto.
    destruct sigma0; simpl; auto.
    destruct sigma0; simpl; auto.
    destruct sigma0; simpl; auto.
  Qed.

  Definition file_get_attr inum :=
    retry_syscall (fun mscs => OptFS.file_get_attr _ fsxp inum mscs)
                  (fun tree => tree).

  Lemma exists_tuple : forall A B P,
      (exists a b, P (a, b)) ->
      exists (a: A * B), P a.
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

  Ltac split_lift_prop :=
    unfold Prog.pair_args_helper in *; simpl in *;
    repeat match goal with
           | [ H: context[(emp * _)%pred] |- _ ] =>
             apply star_emp_pimpl in H
           | [ H: context[(_ * [[ _ ]])%pred] |- _ ] =>
             apply sep_star_lift_apply in H
           | [ H : _ /\ _ |- _ ] => destruct H
           | _ => progress subst
           end.

  Hint Extern 0 {{ CacheCommit _; _ }} => apply CacheCommit_ok : prog.
  Hint Extern 0 {{ CacheAbort; _ }} => apply CacheAbort_ok : prog.

  Lemma locally_modified_fstree : forall sigma sigma',
      locally_modified sigma sigma' ->
      get_fstree sigma' = get_fstree sigma.
  Proof.
    unfold get_fstree, locally_modified; intros.
    destruct sigma, sigma'; simpl in *; intuition congruence.
  Qed.

  Lemma locally_modified_fsmem : forall sigma sigma',
      locally_modified sigma sigma' ->
      get_fsmem (Sigma.mem sigma') = get_fsmem (Sigma.mem sigma).
  Proof.
    unfold get_fsmem, locally_modified; intros.
    destruct sigma, sigma'; simpl in *; intuition congruence.
  Qed.

  Lemma locally_modified_homedirs : forall sigma sigma',
      locally_modified sigma sigma' ->
      get_homedirs sigma' = get_homedirs sigma.
  Proof.
    unfold get_homedirs, locally_modified; intros.
    destruct sigma, sigma'; simpl in *; intuition congruence.
  Qed.

  Ltac learning :=
    repeat match goal with
           | [ H: locally_modified _ _ |- _ ] =>
             learn that (locally_modified_fstree H)
           | [ H: locally_modified _ _ |- _ ] =>
             learn that (locally_modified_fsmem H)
           | [ H: locally_modified _ _ |- _ ] =>
             learn that (locally_modified_homedirs H)
           | [ H: locally_modified _ _ |- _ ] =>
             learn that (locally_modified_lock_preserved H)
           | [ H: CacheRep empty_writebuffer _ |- _ ] =>
             learn that (CacheRep_empty H)
           end.

  Lemma upd_fstree_id : forall up sigma,
      (forall tree, up tree = tree) ->
      upd_fstree up sigma = sigma.
  Proof.
    unfold upd_fstree.
    destruct sigma, cache_other_s; simpl; intros.
    rewrite H; auto.
  Qed.

  Lemma get_set_fsmem : forall m mscs,
      get_fsmem (set_fsmem m mscs) = mscs.
  Proof.
    reflexivity.
  Qed.

  Lemma seq_disk_set_fsmem : forall d m mscs s hm l,
      seq_disk (state d (set_fsmem m mscs) s hm l) = seq_disk (state d m s hm l).
  Proof.
    reflexivity.
  Qed.

  Lemma get_fstree_set_fsmem : forall d m mscs s hm l,
      get_fstree (state d (set_fsmem m mscs) s hm l) = get_fstree (state d m s hm l).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite upd_fstree_id using solve [ auto ] : get_set.
  Hint Rewrite get_set_fsmem seq_disk_set_fsmem get_fstree_set_fsmem : get_set.

  Ltac simplify :=
    repeat match goal with
           | [ H: get_fstree _ = get_fstree _ |- _ ] =>
             rewrite H in *
           | _ => progress autorewrite with get_set
           | _ => progress simpl
           end.

  Theorem opt_file_get_attr_ok : forall inum mscs l tid,
      cprog_spec fs_guarantee tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun tree => find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(r, _) => r = BFILE.BFAttr f;
                                fs_mscs_R :=
                                  fun mscs mscs' => MSAlloc mscs' = MSAlloc mscs;
                                fs_dirup := fun tree => tree |}) mscs l)
                 (OptFS.file_get_attr _ fsxp inum mscs l empty_writebuffer).
  Proof.
    unfold fs_spec.
    prestep; step_using ltac:(apply OptFS.file_get_attr_ok).

    match goal with
    | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
      let n := fresh n in
      let m := fresh m in
      destruct a as [n m]
    end; simpl in *.

    unfold fs_rep in *; intuition eauto; repeat deex.
    destruct ds.
    destruct sigma; simpl in *.
    repeat apply exists_tuple; descend; simpl; intuition eauto.

    SepAuto.pred_apply; SepAuto.cancel.
    eauto.

    step.
    intuition eauto.
    destruct a as [(mscs & (attr & u)) | ]; split_lift_prop; intuition eauto;
      try (learning; congruence).

    descend; intuition eauto.

    unfold seq_disk in *; simpl in *.
    learning.
    match goal with
    | [ H: DirTreeRep.rep _ _ ?tree _ _ _ |-
        DirTreeRep.rep _ _ ?tree' _ _ _ ] =>
      replace tree' with tree by congruence;
        apply H
    end.

    subst.
    congruence.

    unfold seq_disk in *; simpl in *.
    learning.
    descend; intuition eauto.
    match goal with
    | [ H: LOG.rep _ _ _ _ _ ?d |-
        LOG.rep _ _ _ _ _ ?d' ] =>
      replace d' with d by congruence
    end.
    eapply LOG.rep_hashmap_subset; eauto.

    match goal with
    | [ H: DirTreeRep.rep _ _ ?tree _ _ _ |-
        DirTreeRep.rep _ _ ?tree' _ _ _ ] =>
      replace tree' with tree by congruence;
        apply H
    end.
  Qed.

  Hint Extern 0 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply opt_file_get_attr_ok : prog.

  Lemma and_copy : forall (P Q:Prop),
      P ->
      (P -> Q) ->
      P /\ Q.
  Proof.
    eauto.
  Qed.

  Lemma rely_file_preserved : forall sigma sigma' tid pathname f,
      find_subtree (get_homedirs sigma tid ++ pathname) (get_fstree sigma) = Some f ->
      Rely fs_guarantee tid sigma sigma' ->
      find_subtree (get_homedirs sigma' tid ++ pathname) (get_fstree sigma') = Some f.
  Proof.
    unfold Rely, fs_guarantee; intros.
    induction H0; intuition; repeat deex.
    unfold homedir_guarantee in H3.
    specialize (H3 _ ltac:(eauto)).
    unfold homedir_rely in H3.

    apply find_subtree_app' in H; deex; intuition.
    erewrite find_subtree_app; eauto.
    congruence.
  Qed.

  Lemma rely_trans : forall St (G: Protocol St) tid sigma sigma' sigma'',
      Rely G tid sigma sigma' ->
      Rely G tid sigma' sigma'' ->
      Rely G tid sigma sigma''.
  Proof.
    unfold Rely; intros.
    eapply Relation_Operators.rt_trans; eauto.
  Qed.

  Theorem file_get_attr_ok : forall inum tid,
      cprog_spec fs_guarantee tid
                 (fun '(pathname, f) '(sigma_i, sigma) =>
                    {| precondition :=
                         fs_guarantee tid sigma_i sigma /\
                         let tree := get_fstree sigma in
                         find_subtree (get_homedirs sigma tid ++ pathname) tree = Some (TreeFile inum f);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           Rely fs_guarantee tid sigma sigma' /\
                           match r with
                           | Done (r, _) => r = BFILE.BFAttr f
                           | _ => True
                           end /\
                           fs_guarantee tid sigma_i' sigma'
                    |}) (file_get_attr inum).
  Proof.
  Abort.

  (* translate remaining system calls for extraction *)

  Definition lookup dnum names :=
    retry_syscall (fun mscs => OptFS.lookup _ fsxp dnum names mscs)
                  (fun tree => tree).

  Definition read_fblock inum off :=
    retry_syscall (fun mscs => OptFS.read_fblock _ fsxp inum off mscs)
                  (fun tree => tree).

  Definition file_set_attr inum attr :=
    retry_syscall (fun mscs => OptFS.file_set_attr _ fsxp inum attr mscs)
                  (fun tree => tree).

  Definition file_truncate inum sz :=
    retry_syscall (fun mscs => OptFS.file_truncate _ fsxp inum sz mscs)
                  (fun tree => tree).

  Definition update_fblock_d inum off b :=
    retry_syscall (fun mscs => OptFS.update_fblock_d _ fsxp inum off b mscs)
                  (fun tree => tree).

  Definition create dnum name :=
    retry_syscall (fun mscs => OptFS.create _ fsxp dnum name mscs)
                  (fun tree => tree).

  Definition rename dnum srcpath srcname dstpath dstname :=
    retry_syscall (fun mscs => OptFS.rename _ fsxp dnum srcpath srcname dstpath dstname mscs)
                  (fun tree => tree).

  Definition delete dnum name :=
    retry_syscall (fun mscs => OptFS.delete _ fsxp dnum name mscs)
                  (fun tree => tree).

  (* wrap unverified syscalls *)

  Definition statfs :=
    retry_syscall (fun mscs => OptFS.statfs _ fsxp mscs)
                  (fun tree => tree).

  Definition mkdir dnum name :=
    retry_syscall (fun mscs => OptFS.mkdir _ fsxp dnum name mscs)
                  (fun tree => tree).

  Definition file_get_sz inum :=
    retry_syscall (fun mscs => OptFS.file_get_sz _ fsxp inum mscs)
                  (fun tree => tree).

  Definition file_set_sz inum sz :=
    retry_syscall (fun mscs => OptFS.file_set_sz _ fsxp inum sz mscs)
                  (fun tree => tree).

  Definition readdir dnum :=
    retry_syscall (fun mscs => OptFS.readdir _ fsxp dnum mscs)
                  (fun tree => tree).

  Definition tree_sync :=
    retry_syscall (fun mscs => OptFS.tree_sync _ fsxp mscs)
                  (fun tree => tree).

  Definition file_sync inum :=
    retry_syscall (fun mscs => OptFS.file_sync _ fsxp inum mscs)
                  (fun tree => tree).

  Definition update_fblock inum off b :=
    retry_syscall (fun mscs => OptFS.update_fblock _ fsxp inum off b mscs)
                  (fun tree => tree).

  Definition mksock dnum name :=
    retry_syscall (fun mscs => OptFS.mksock _ fsxp dnum name mscs)
                  (fun tree => tree).

  Definition umount :=
    retry_syscall (fun mscs => OptFS.umount _ fsxp mscs)
                  (fun tree => tree).

End ConcurrentFS.

Definition OtherSt := {| Mem := unit; Abstraction := unit |}.

Definition init (mscs: memstate) : @cprog (@St OtherSt) unit.
  apply Assgn.
  constructor; simpl.
  exact MemCache.empty_cache.
  constructor; simpl.
  exact mscs.
  exact tt.
Defined.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)