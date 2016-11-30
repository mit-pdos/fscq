Require Import CoopConcur.
Require Import CoopConcurAuto.
Require ConcurrentCache.
Require Import Protocols.
Require Import ConcurrentFS.
Require Import Rec.
Require Import DirTree.

Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

Require Import GenSepN BFile Log SuperBlock.
Require Import ConcurrentBridge.

Module St <: GlobalState.
  Definition Sigma :=
    defState (mem_types ConcurrentCache.Sigma ++
                        (BFILE.memstate
                           :: (FSLayout.fs_xparams:Type)
                           :: nil))
             (abstraction_types ConcurrentCache.Sigma ++
                                ((FSLayout.fs_xparams:Type)
                                   :: DIRTREE.dirtree
                                   :: nil)).
End St.

Arguments HNext {A elm a types} _.
Notation "f @ x" := (f x) (at level 10, x at level 20, only parsing).

Definition mMscs : var (mem_types St.Sigma) BFILE.memstate :=
  HNext @ HNext @ HFirst.

Definition mFsxp : var (mem_types St.Sigma) FSLayout.fs_xparams :=
  HNext @ HNext @ HNext @ HFirst.

Definition vFsxp : var (abstraction_types St.Sigma) FSLayout.fs_xparams :=
  HNext @ HNext @ HNext @ HNext @ HNext @ HFirst.

Definition vDirTree : var (abstraction_types St.Sigma) DIRTREE.dirtree :=
  HNext @ HNext @ HNext @ HNext @ HNext @ HNext @ HFirst.

Hint Constructors List.NoDup.

Ltac prove_nodup :=
    repeat match goal with
           | [ |- List.NoDup _ ] => constructor
           | [ |- False ] => Omega.omega
           | [ |- ~ _ ] => intro
           | [ H: List.In _ _ |- _ ] => inversion H; clear H
           end.

Module CacheProj <: ConcurrentCache.CacheProj St.
  Definition stateProj: StateProj St.Sigma ConcurrentCache.Sigma.
    unshelve econstructor.

    exact [( HFirst; HNext HFirst )].
    simpl.
    repeat apply HCons; try exact HNil.
    exact (HFirst).
    exact (HNext @ HFirst).
    exact (HNext @ HNext @ HFirst).
    exact (HNext @ HNext @ HNext @ HFirst).
    exact (HNext @ HNext @ HNext @ HNext @ HFirst).

    simpl; prove_nodup.
    simpl; prove_nodup.
  Defined.
End CacheProj.

Ltac prove_not_in :=
  match goal with
  | [ |- HIn _ _ -> False ] =>
    solve [ intros;
            repeat match goal with
                   | [ H: HIn _ _ |- _ ] =>
                     inversion H; subst; repeat sigT_eq; clear H
                   end ]
  end.

Ltac unmodified_var :=
  try match goal with
      | [ H: modified _ ?l ?l' |- get _ ?l' = get _ ?l ] =>
        symmetry; apply H
      end;
  try match goal with
      | [ H: modified _ ?l ?l' |- get _ ?l = get _ ?l' ] =>
        apply H
      end;
  prove_not_in.

Module CacheSubProtocol <: ConcurrentCache.CacheSubProtocol.
  Module CacheProtocol := ConcurrentCache.MakeCacheProtocol St CacheProj.

  Module App <: GlobalProtocol.
    Module St := St.
    Definition Sigma := St.Sigma.

    (* this won't be so simple with additional state in Sigma *)
    Definition delta : Protocol Sigma.
      apply (defProtocol
               (fun d hm m s =>
                  invariant CacheProtocol.delta d hm m s /\
                  let fsxp := get mFsxp m in
                  let mscs := get mMscs m in
                  let tree := get vDirTree s in
                  (exists ds ilist frees,
                    LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
                            (LOG.NoTxn ds) (BFILE.MSLL mscs) hm
                            (lower_disk (get CacheProtocol.vdisk0 s)) /\
                    ((DIRTREE.rep fsxp emp tree ilist frees)
                       @ list2nmem (ds!!))%pred) /\
                  get CacheProtocol.vdisk s = get CacheProtocol.vdisk0 s /\
                    get vFsxp s = fsxp)
               (fun tid s s' => guar CacheProtocol.delta tid s s' /\
                             get vDirTree s' = get vDirTree s /\
                             get vFsxp s' = get vFsxp s)).
      intros; constructor; hnf; intros.
      intuition idtac; apply guar_preorder.
      intuition idtac; try congruence.
      eapply guar_preorder; eauto.
    Defined.
  End App.

  Module Proj := CacheProj.

  Definition protocolProj:SubProtocol App.delta CacheProtocol.delta.
  Proof.
    constructor; simpl; intros; intuition idtac.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    simpl; intros; intuition idtac.
    unmodified_var.
    unmodified_var.
  Qed.

  Lemma log_rep_hashmap_le : forall xp F ms st hm hm' d,
      hashmap_le hm hm' ->
      LOG.rep xp F st ms hm d -> LOG.rep xp F st ms hm' d.
  Proof.
    intros.
    pred_apply.
    apply LOG.rep_hashmap_subset.
    eauto.
  Qed.

  Hint Resolve log_rep_hashmap_le.

  Definition invariantRespectsPrivateVars :
    forall d hm m s d' hm' m' s',
      invariant App.delta d hm m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' hm' m' s' ->
      hashmap_le hm hm' ->
      invariant App.delta d' hm' m' s'.
  Proof.
    simpl; intros; destruct_ands; repeat deex.
    assert (get vDirTree s' = get vDirTree s) by unmodified_var.
    assert (get mFsxp m' = get mFsxp m) by unmodified_var.
    assert (get mMscs m' = get mMscs m) by unmodified_var.
    assert (get vFsxp s' = get vFsxp s) by unmodified_var.
    assert (get CacheProtocol.vdisk0 s' = get CacheProtocol.vdisk0 s) by unmodified_var.
    assert (get CacheProtocol.vdisk s' = get CacheProtocol.vdisk s) by unmodified_var.
    unfold id in *; simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H in *
           end.
    intuition idtac.
    descend.
    intuition eauto.
  Qed.

End CacheSubProtocol.

Module CFS := ConcurFS CacheSubProtocol.

Import CacheSubProtocol CacheProtocol.
Import CFS.Bridge.

Ltac learn_unmodified :=
  unfold id; simpl;
  repeat match goal with
         | [ H: modified _ ?l ?l' |- _ ] =>
           let learn_unmodified_var v :=
               try (
                   not_learnt (get v l' = get v l);
                   let Heq := fresh in
                   assert (get v l' = get v l) as Heq by (symmetry; apply H; prove_not_in);
                   pose proof (AlreadyLearnt Heq);
                   unfold id in Heq; simpl in Heq) in
           progress (learn_unmodified_var mFsxp;
                     learn_unmodified_var vFsxp;
                     learn_unmodified_var mMscs;
                     learn_unmodified_var vDirTree;
                     learn_unmodified_var CacheProtocol.vdisk;
                     learn_unmodified_var CacheProtocol.vdisk0)
         end.

Definition read_fblock inum off :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- CFS.read_fblock fsxp inum off mscs;
    match r with
    | Some r =>
      let '(mscs', (v, _)) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        Ret (value v)
    | None =>
      _ <- ConcurrentCache.cache_abort;
      Ret None
    end.

Lemma exists_tuple : forall A B (P: A * B -> Prop) (b: B),
    (exists (a: A), P (a, b)) ->
    exists (a: A * B), P a.
Proof.
  intros.
  deex.
  exists (a, b); auto.
Qed.

Theorem read_fblock_ok : forall inum off,
      SPEC App.delta, tid |-
              {{ pathname f Fd vs,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   (Fd * off |-> vs)%pred (list2nmem (BFILE.BFData f)) /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   tree' = get vDirTree s /\
                   match r with
                   | Some r => r = fst vs /\
                              BFILE.MSAlloc (get mMscs m') = BFILE.MSAlloc (get mMscs m)
                   | None => guar App.delta tid s s'
                   end /\
                   hashmap_le hm hm'
              }} read_fblock inum off.
Proof.
  intros.
  step.
  step.
  step.

  match goal with
  | [ H: invariant App.delta _ _ _ _ |- _ ] =>
    simpl in H; destruct_ands; repeat deex
  end.
  match goal with
  | [ H: guar App.delta _ _ _ |- _ ] =>
    simpl in H; destruct_ands; repeat deex
  end.

  Ltac next_evar name := match goal with
                         | |- exists (_: _ * ?t), _ =>
                           let name := fresh name in
                           evar (name:t);
                           apply (exists_tuple _ name);
                           subst name
                         end.
  next_evar F_. next_evar frees. next_evar ilist.
  next_evar vs. next_evar Fd. next_evar f.
  next_evar pathname. next_evar tree. next_evar Ftop.
  next_evar Fm.
  evar (ds0: DiskSet.diskset); exists ds0; subst ds0.
  simpl.

  unfold project_disk, id in *; simpl.
  intuition eauto.
  replace (get vdisk s).
  pred_apply; cancel; eauto.

  step.
  destruct p as [ mscs [v _] ].
  step.
  step;
    try solve [ match goal with
                | [ H: cacheI _ _ _ _ |- _ ] =>
                  apply H
                end ].
  learn_unmodified.

  step.
  simpl.
  learn_unmodified.
  simpl_get_set_all.
  repeat match goal with
         | [ H: get _ _ = get _ _ |- _ ] =>
           rewrite H
         end.
  intuition eauto.
  descend.
  intuition eauto.
  pred_apply; cancel.
  replace (get vDirTree s_i).
  eauto.
  congruence.

  learn_unmodified.
  congruence.

  (* prove postcondition *)
  learn_unmodified.
  simpl_get_set_all.
  apply emp_star in H28.
  apply sep_star_lift_apply in H28.
  destruct_ands.
  simpl; intuition idtac.
  congruence.

  step;
    try solve [ match goal with
                | [ H: cacheI _ _ _ _ |- _ ] =>
                  apply H
                end ].
  learn_unmodified.
  unfold id in *; simpl in *.
  step.
  learn_unmodified.
  repeat match goal with
         | [ H: get _ _ = get _ _ |- _ ] =>
           rewrite H
         end.
  replace (get vDirTree s_i).
  intuition idtac.
  descend.
  intuition eauto.

  learn_unmodified.
  congruence.

  learn_unmodified.
  congruence.

  learn_unmodified.
  congruence.

  eapply cacheR_preorder; eauto.

  learn_unmodified.
  congruence.

  learn_unmodified.
  congruence.
Qed.
