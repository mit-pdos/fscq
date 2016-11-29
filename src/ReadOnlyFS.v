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
                  exists ds ilist frees,
                    LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
                            (LOG.NoTxn ds) (BFILE.MSLL mscs) hm
                            (lower_disk (get CacheProtocol.vdisk s)) /\
                    ((DIRTREE.rep fsxp emp tree ilist frees)
                       @ list2nmem (ds!!))%pred /\
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

  Ltac unmodified_var :=
    try match goal with
        | [ H: modified _ ?l ?l' |- get _ ?l' = get _ ?l ] =>
          symmetry; apply H
        end;
    try match goal with
        | [ H: modified _ ?l ?l' |- get _ ?l = get _ ?l' ] =>
          apply H
        end;
    match goal with
    | [ |- HIn _ _ -> False ] =>
      solve [ intros;
              repeat match goal with
                     | [ H: HIn _ _ |- _ ] =>
                       inversion H; subst; repeat sigT_eq; clear H
                     end ]
    end.

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
    simpl; intuition idtac.
    repeat deex.
    assert (get mFsxp m' = get mFsxp m) as Hfsxp by unmodified_var.
    assert (get mMscs m' = get mMscs m) as Hmscs by unmodified_var.
    assert (get CacheProtocol.vdisk s' = get CacheProtocol.vdisk s) as Hvdisk by unmodified_var.
    assert (get vDirTree s' = get vDirTree s) as Htree by unmodified_var.
    assert (get vFsxp s' = get vFsxp s) as Hvfsxp by unmodified_var.
    unfold id in *; simpl in *.
    rewrite !Hfsxp, !Hmscs, !Hvdisk, !Htree, !Hvfsxp in *.
    repeat match goal with
           | |- exists _, _ => eexists
           end.
    intuition eauto.
  Qed.

End CacheSubProtocol.

Module CFS := ConcurFS CacheSubProtocol.