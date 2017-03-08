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

Record FsParams :=
  { fsmem: ident; (* : memsstate *)
    fstree: ident; (* : dirtree *)
    fshomedirs: ident; (* thread_homes *)
    }.

Section ConcurrentFS.

  Variable fsxp: fs_xparams.
  Variable CP:CacheParams.
  Variable P:FsParams.

  Definition fs_rep vd hm mscs tree :=
    exists ds ilist frees,
      LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs) hm (add_buffers vd) /\
      (DirTreeRep.rep fsxp Pred.emp tree ilist frees mscs)
        (list2nmem (ds!!)).

  Definition fs_invariant d hm tree (homedirs: thread_homes) : heappred :=
    (fstree P |-> abs tree *
     fshomedirs P |-> abs homedirs *
     exists mscs vd, CacheRep CP d empty_writebuffer vd vd *
                fsmem P |-> val mscs *
                [[ fs_rep vd hm mscs tree ]])%pred.

  Definition fs_guarantee tid (sigma sigma':Sigma) :=
    exists tree tree' homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) /\
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
      homedir_guarantee tid homedirs tree tree'.

  Theorem fs_rely_same_fstree : forall tid sigma sigma' tree homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree homedirs (Sigma.mem sigma') ->
      Rely fs_guarantee tid sigma sigma'.
  Proof.
    intros.
    constructor.
    exists (S tid); intuition.
    unfold fs_guarantee.
    descend; intuition eauto.
    reflexivity.
  Qed.

  Section InvariantUniqueness.

    Ltac mem_eq m a v :=
      match goal with
      | [ H: context[ptsto a v] |- _ ] =>
        let Hptsto := fresh in
        assert ((exists F, F * a |-> v)%pred m) as Hptsto by
              (SepAuto.pred_apply' H; SepAuto.cancel);
        unfold exis in Hptsto; destruct Hptsto;
        apply ptsto_valid' in Hptsto
      end.

    Lemma fs_invariant_tree_unique : forall d hm tree homedirs
                                       d' hm' tree' homedirs' m,
        fs_invariant d hm tree homedirs m ->
        fs_invariant d' hm' tree' homedirs' m ->
        tree = tree'.
    Proof.
      unfold fs_invariant; intros.
      mem_eq m (fstree P) (abs tree).
      mem_eq m (fstree P) (abs tree').
      rewrite H1 in H2; inversion H2; inj_pair2.
      auto.
    Qed.

    Lemma fs_invariant_homedirs_unique : forall d hm tree homedirs
                                       d' hm' tree' homedirs' m,
        fs_invariant d hm tree homedirs m ->
        fs_invariant d' hm' tree' homedirs' m ->
        homedirs = homedirs'.
    Proof.
      unfold fs_invariant; intros.
      mem_eq m (fshomedirs P) (abs homedirs).
      mem_eq m (fshomedirs P) (abs homedirs').
      rewrite H1 in H2; inversion H2; inj_pair2.
      auto.
    Qed.

  End InvariantUniqueness.

  Ltac invariant_unique :=
    repeat match goal with
           | [ H: fs_invariant _ _ ?tree _ ?m,
                  H': fs_invariant _ _ ?tree' _ ?m |- _ ] =>
             first [ constr_eq tree tree'; fail 1 |
                     assert (tree' = tree) by
                         apply (fs_invariant_tree_unique H' H); subst ]
           | [ H: fs_invariant _ _ _ ?homedirs ?m,
                  H': fs_invariant _ _ _ ?homedirs' ?m |- _ ] =>
             first [ constr_eq homedirs homedirs'; fail 1 |
                     assert (homedirs' = homedirs) by
                         apply (fs_invariant_homedirs_unique H' H); subst ]
           end.

  Theorem fs_rely_invariant : forall tid sigma sigma' tree homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      exists tree', fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma').
  Proof.
    unfold fs_guarantee; intros.
    generalize dependent tree.
    induction H0; intros; repeat deex; eauto.
    invariant_unique.
    eauto.
    edestruct IHclos_refl_trans1; eauto.
  Qed.

  Lemma fs_rely_invariant' : forall tid sigma sigma',
      Rely fs_guarantee tid sigma sigma' ->
      forall tree homedirs,
        fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
        exists tree',
          fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma').
  Proof.
    intros.
    eapply fs_rely_invariant; eauto.
  Qed.

  Theorem fs_homedir_rely : forall tid sigma sigma' tree homedirs tree',
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') ->
      homedir_rely tid homedirs tree tree'.
  Proof.
    unfold fs_guarantee; intros.
    generalize dependent tree'.
    generalize dependent tree.
    apply Operators_Properties.clos_rt_rt1n in H0.
    induction H0; intros; repeat deex; invariant_unique.
    - reflexivity.
    - match goal with
      | [ H: homedir_guarantee _ _ _ _ |- _ ] =>
        specialize (H _ ltac:(eauto))
      end.
      specialize (IHclos_refl_trans_1n _ ltac:(eauto) _ ltac:(eauto)).
      unfold homedir_rely in *; congruence.
  Qed.

  Lemma fs_rely_preserves_subtree : forall tid sigma sigma' tree homedirs tree' path f,
      find_subtree (homedirs tid ++ path) tree = Some f ->
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') ->
      find_subtree (homedirs tid ++ path) tree' = Some f.
  Proof.
    intros.
    eapply fs_homedir_rely in H1; eauto.
    unfold homedir_rely in H1.
    eapply find_subtree_app' in H; repeat deex.
    erewrite find_subtree_app; eauto.
    congruence.
  Qed.

  Theorem fs_guarantee_refl : forall tid sigma homedirs,
      (exists tree, fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma)) ->
      fs_guarantee tid sigma sigma.
  Proof.
    intros; deex.
    unfold fs_guarantee; descend; intuition eauto.
    reflexivity.
  Qed.

  Theorem fs_guarantee_trans : forall tid sigma sigma' sigma'',
      fs_guarantee tid sigma sigma' ->
      fs_guarantee tid sigma' sigma'' ->
      fs_guarantee tid sigma sigma''.
  Proof.
    unfold fs_guarantee; intuition.
    repeat deex; invariant_unique.

    descend; intuition eauto.
    etransitivity; eauto.
  Qed.

  Inductive SyscallResult {T} :=
  | Done (v:T)
  | TryAgain
  | SyscallFailed.

  Arguments SyscallResult T : clear implicits.

  Definition OptimisticProg T :=
    memstate ->
    LockState -> WriteBuffer ->
    cprog (Result (memstate * T) * WriteBuffer).

  (* Execute p assuming it is read-only. This program could distinguish between
  failures that require filling the cache [Failure (CacheMiss a)] and failures
  that require upgrading to a write lock [Failure WriteRequired], but currently
  does not do so. *)
  Definition readonly_syscall T (p: OptimisticProg T) : cprog (SyscallResult T) :=
    _ <- GetReadLock;
      mscs <- Get memstate (fsmem P);
      (* for read-only syscalls, the returned write buffer is always the same
       as the input *)
      do '(r, _) <- p mscs ReadLock empty_writebuffer;
      match r with
      | Success (ms', r) =>
        l <- UpgradeReadLock;
          _ <- if lock_dec l WriteLock then
                _ <- Assgn (fsmem P) ms';
                  _ <- Unlock;
                  Ret tt
              else
                _ <- ReleaseReadLock;
                Ret tt;
          Ret (Done r)
      | Failure e =>
        _ <- ReleaseReadLock;
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
             m <- Get _ (fsmem P);
             do '(r, wb) <- p m WriteLock empty_writebuffer;
             match r with
             | Success (ms', r) =>
               _ <- CacheCommit CP wb;
                 _ <- Assgn (fsmem P) ms';
                 _ <- GhostUpdate (fstree P) (fun _ => update);
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
    Spec _ (Result (memstate * T) * WriteBuffer) :=
    fun mscs l '(F, vd0, vd, tree, a) '(sigma_i, sigma) =>
      {| precondition :=
           (F * CacheRep CP (Sigma.disk sigma) empty_writebuffer vd0 vd)%pred (Sigma.mem sigma) /\
           fs_rep vd (Sigma.hm sigma) mscs tree /\
           fs_pre (fsspec a) tree /\
           Sigma.l sigma = l /\
           ReadPermission l;
         postcondition :=
           fun '(sigma_i', sigma') '(r, wb') =>
             exists vd',
             (F * CacheRep CP (Sigma.disk sigma) empty_writebuffer vd0 vd')%pred (Sigma.mem sigma') /\
             Sigma.l sigma' = l /\
             (l = ReadLock -> vd' = vd) /\
             match r with
             | Success (mscs', r) =>
               fs_post (fsspec a) r /\
               fs_mscs_R (fsspec a) mscs mscs' /\
               fs_rep vd' (Sigma.hm sigma') mscs' (fs_dirup (fsspec a) tree)
             | Failure e =>
               (l = WriteLock -> e <> WriteRequired) /\
               fs_rep vd (Sigma.hm sigma') mscs tree
             end /\
             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
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

  Lemma precondition_stable_rely_fwd : forall A T (spec: FsSpec A T) tid a
                                     sigma tree homedirs sigma',
      precondition_stable spec homedirs tid ->
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_pre (spec a) tree ->
      exists tree',
        fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
        homedir_rely tid homedirs tree tree' /\
        fs_pre (spec a) tree'.
  Proof.
    unfold precondition_stable; intros.
    match goal with
    | [ H: fs_invariant _ _ _ _ _,
           H': Rely _ _ _ _ |- _ ] =>
      pose proof (fs_rely_invariant H H')
    end; deex.
    descend; intuition eauto using fs_homedir_rely.
  Qed.

  Definition readonly_spec A T (fsspec: FsSpec A T) tid :
    Spec _ (SyscallResult T) :=
    fun '(tree, homedirs, a) '(sigma_i, sigma) =>
      {| precondition :=
           (fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs) (Sigma.mem sigma) /\
           Sigma.l sigma = Free /\
           fs_pre (fsspec a) tree /\
           precondition_stable fsspec homedirs tid /\
           mscs_nocommit fsspec;
         postcondition :=
           fun '(sigma_i', sigma') r =>
             (fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree homedirs) (Sigma.mem sigma') /\
             Rely fs_guarantee tid sigma sigma' /\
             Sigma.l sigma' = Free /\
             match r with
             | Done v => fs_post (fsspec a) v
             | TryAgain => True
             | SyscallFailed => True
             end /\
             fs_guarantee tid sigma_i' sigma'|}.

  Lemma fs_rep_hashmap_incr : forall vd tree mscs hm hm',
      fs_rep vd hm mscs tree ->
      hashmap_le hm hm' ->
      fs_rep vd hm' mscs tree.
  Proof.
    unfold fs_rep; intros.
    repeat deex.
    exists ds, ilist, frees; intuition eauto.
    eapply LOG.rep_hashmap_subset; eauto.
  Qed.

  Hint Resolve fs_rep_hashmap_incr.

  Theorem readonly_syscall_ok : forall T (p: OptimisticProg T) A (fsspec: FsSpec A T) tid,
      (forall mscs, cprog_spec fs_guarantee tid
                          (fs_spec fsspec mscs ReadLock)
                          (p mscs ReadLock empty_writebuffer)) ->
      cprog_spec fs_guarantee tid
                 (readonly_spec fsspec tid) (readonly_syscall p).
  Proof.
    intros.
    unfold readonly_syscall.

    step.
    destruct st as [sigma_i sigma]; simpl in *.
    destruct a as ((tree & homedirs) & a); simpl in *.
    intuition eauto.

    step.
    deex.
    destruct sigma'; simpl; auto.

    match goal with
    | [ H: Rely fs_guarantee _ _ _ |- _ ] =>
      pose proof H;
        eapply precondition_stable_rely_fwd in H; eauto;
          deex
    end.
    unfold fs_invariant in H9.
    (* need to deex mscs inside fs_invariant - should write an unfold rule that moves the existential to the top *)
    descend; simpl in *; intuition eauto.
    unfold fs_invariant in *.
    SepAuto.pred_apply; SepAuto.cancel.
    Show Existentials.
    instantiate (1 := mscs).

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
    retry_syscall (fun mscs => file_get_attr _ fsxp inum mscs)
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
    retry_syscall (fun mscs => lookup _ fsxp dnum names mscs)
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