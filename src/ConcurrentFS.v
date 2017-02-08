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

  Theorem fs_guarantee_refl : forall tid sigma,
      fs_invariant sigma ->
      fs_guarantee tid sigma sigma.
  Proof.
    unfold fs_guarantee; intuition.
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

  Definition guard {T} (r: Result T) : {exists v, r=Success v} + {r=Failed}.
    destruct r; eauto.
  Defined.

  Definition retry_syscall T
             (p: memstate -> @cprog St (Result (memstate * T) * WriteBuffer))
             (update: dirtree -> dirtree)
    : cprog (Result T) :=
    retry guard (m <- Get;
                   do '(r, wb) <- p (get_fsmem m);
                   match r with
                   | Success (ms', r) =>
                     _ <- CacheCommit wb;
                       m <- Get;
                       _ <- Assgn (set_fsmem m ms');
                       _ <- GhostUpdate (fun _ s => upd_fstree update s);
                       Ret (Success r)
                   | Failed =>
                     _ <- CacheAbort;
                       _ <- Yield;
                       Ret Failed
                   end).

  Definition file_get_attr inum : @cprog St _ :=
    retry_syscall (fun mscs =>
                     OptFS.file_get_attr _ fsxp inum mscs empty_writebuffer)
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

  Lemma seq_disk_set_fsmem : forall d m mscs s hm,
      seq_disk (state d (set_fsmem m mscs) s hm) = seq_disk (state d m s hm).
  Proof.
    reflexivity.
  Qed.

  Lemma get_fstree_set_fsmem : forall d m mscs s hm,
      get_fstree (state d (set_fsmem m mscs) s hm) = get_fstree (state d m s hm).
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

  Theorem opt_file_get_attr_ok : forall inum mscs wb tid,
      cprog_spec fs_guarantee tid
                 (fun '(pathname, f) '(sigma_i, sigma) =>
                    {| precondition :=
                         let tree := get_fstree sigma in
                         mscs = get_fsmem (Sigma.mem sigma) /\
                         CacheRep wb sigma /\
                         fs_rep (seq_disk sigma) tree mscs (Sigma.hm sigma) /\
                         find_subtree pathname tree = Some (TreeFile inum f);
                       postcondition :=
                         fun '(sigma_i', sigma') '(r, wb') =>
                           CacheRep wb' sigma' /\
                           locally_modified sigma sigma' /\
                           hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                           vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
                           match r with
                           | Success (mscs', (r, _)) =>
                             r = BFILE.BFAttr f /\
                             fs_rep (seq_disk sigma') (get_fstree sigma) mscs' (Sigma.hm sigma')
                           | Failed =>
                             fs_rep (seq_disk sigma) (get_fstree sigma) mscs (Sigma.hm sigma') /\
                             get_fsmem (Sigma.mem sigma') = get_fsmem (Sigma.mem sigma)
                           end /\
                           sigma_i' = sigma_i; |})
                 (OptFS.file_get_attr _ fsxp inum mscs wb).
  Proof.
    prestep; step_using ltac:(apply OptFS.file_get_attr_ok).

    unfold fs_rep in *; intuition eauto; repeat deex.
    destruct ds.
    destruct sigma; simpl in *.
    repeat apply exists_tuple; descend; simpl; intuition eauto.

    SepAuto.pred_apply; SepAuto.cancel.
    eauto.

    step.
    intuition eauto.
    destruct a as [(mscs & (attr & u)) | ]; split_lift_prop; intuition eauto.

    descend; intuition eauto.
    eapply LOG.rep_hashmap_subset; eauto.

    learning; congruence.
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
                           | Success (r, _) => r = BFILE.BFAttr f
                           | Failed => True
                           end /\
                           fs_guarantee tid sigma_i' sigma'
                    |}) (file_get_attr inum).
  Proof.
    unfold file_get_attr, retry_syscall; intros.

    eapply retry_spec' with (Failed).
    simpl.
    induction n; simpl.
    - step.
      step.
      intuition eauto.
      constructor.
      exists (S tid); intuition.
      unfold fs_guarantee in *; simpl in *; intuition eauto.
      apply homedir_guar_preorder.
    - step.
      step.

      match goal with
      | [ H: fs_guarantee _ _ _ |- _ ] =>
        unfold fs_guarantee, fs_invariant in H; intuition; repeat deex
      end.

      repeat apply exists_tuple; descend; simpl; intuition eauto.

      destruct a as [(mscs & (attr & u)) | ].
      + step.

        intuition eauto.

        hoare.
        destruct (guard r); repeat deex.
        step.

        match goal with
        | [ H: Success _ = Success _ |- _ ] =>
          inversion H; subst; clear H
        end.
        split_lift_prop.
        learning.

        destruct sigma, sigma0, sigma'; simpl in *; simplify.
        intuition eauto.

        eapply fs_rely_same_fstree; unfold fs_invariant; intuition eauto.
        simplify; subst; eauto.

        unfold seq_disk, get_fstree in *; simpl in *.
        congruence.

        unfold get_homedirs in *; simpl in *; congruence.

        unfold fs_guarantee; intuition eauto.
        unfold fs_guarantee, fs_invariant in *; intuition eauto.
        unfold fs_guarantee, fs_invariant in *; simplify; intuition eauto.
        unfold seq_disk, get_fstree in *; simpl in *; congruence.

        simplify.
        unfold get_homedirs, get_fstree in *; simpl in *.
        etransitivity; eauto.
        congruence.

        unfold get_homedirs in *; simpl in *; congruence.

        subst.
        step.
        congruence.
      + hoare.

        apply and_copy.

        unfold fs_guarantee; intuition eauto.
        unfold fs_invariant in *; intuition eauto.
        unfold fs_invariant, fs_guarantee in *; intuition eauto.

        learning; simplify.
        destruct sigma_i, sigma, sigma', sigma0 in *; simpl in *; subst; eauto.
        unfold seq_disk in *; simpl in *; eauto.
        congruence.

        learning; simplify.
        etransitivity; eauto.
        match goal with
        | [ |- homedir_guarantee _ _ ?tree ?tree' ] =>
          replace tree with tree' by congruence; reflexivity
        end.

        learning; simplify.
        unfold get_homedirs in *; simpl in *.
        congruence.

        step.
        repeat apply exists_tuple; descend; simpl; intuition eauto.

        eapply fs_guarantee_refl.
        match goal with
        | [ H: Rely fs_guarantee _ _ _ |- _ ] =>
          eapply fs_rely_invariant in H; eauto
        end.
        unfold fs_guarantee in *; intuition eauto.

        learning.
        match goal with
        | [ H: find_subtree (get_homedirs ?sigma ?tid ++ _) ?tree = Some _,
               H': Rely fs_guarantee ?tid ?sigma' _ |- _ ] =>
          replace (get_homedirs sigma tid) with (get_homedirs sigma' tid) in H by congruence;
            replace tree with (get_fstree sigma') in H by congruence
        end.

        eapply rely_file_preserved; eauto.

        step.
        intuition eauto.

        Lemma rely_trans : forall St (G: Protocol St) tid sigma sigma' sigma'',
            Rely G tid sigma sigma' ->
            Rely G tid sigma' sigma'' ->
            Rely G tid sigma sigma''.
        Proof.
          unfold Rely; intros.
          eapply Relation_Operators.rt_trans; eauto.
        Qed.

        eapply rely_trans; eauto.
        eapply rely_trans; eauto.
        eapply fs_rely_same_fstree; eauto.
        unfold fs_invariant; intuition eauto.
        unfold fs_guarantee in *; intuition eauto.
        learning; congruence.
        learning; congruence.
  Qed.

End ConcurrentFS.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)