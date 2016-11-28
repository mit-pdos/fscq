Require Import CoopConcur.
Require Import CoopConcurAuto.
Require ConcurrentCache.
Require Import Protocols.
Require Import ConcurrentFS.

Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

Module St <: GlobalState.
  (* TODO: add file-system state *)
  Definition Sigma := ConcurrentCache.Sigma.
End St.

Arguments HNext {A elm a types} _.
Notation "f @ x" := (f x) (at level 10, x at level 20, only parsing).
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
             (fun d m s => invariant CacheProtocol.delta d m s)
             (fun tid s s' => guar CacheProtocol.delta tid s s')).
      apply guar_preorder.
    Defined.
  End App.

  Module Proj := CacheProj.

  Definition protocolProj:SubProtocol App.delta CacheProtocol.delta.
  Proof.
    constructor; intros; eauto.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    intros.
    eauto.
  Qed.

  Definition invariantRespectsPrivateVars :
    forall d m s d' m' s',
      invariant App.delta d m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' m' s' ->
      invariant App.delta d' m' s'.
  Proof.
    intros.
    eauto.
  Qed.

End CacheSubProtocol.

Module CFS := ConcurFS CacheSubProtocol.

Print CFS.