Require Import CoopConcur.
Require Import Protocols.
Require Import ConcurrentCache.
Require Import Omega.
Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

(* somewhat oddly, Sigma now refers to the cache state - would have hidden that
and referred to it qualified if Coq let me do so cleanly *)

Module CopyState <: GlobalState.
  Definition Sigma := Sigma.
End CopyState.

Module CopyCacheProj <: CacheProj CopyState.
  Hint Constructors List.NoDup.
  Hint Extern 4 False => omega.
  Definition stateProj : StateProj CopyState.Sigma Sigma.
    unshelve econstructor; simpl.
    exact [( HFirst; (HNext HFirst) )].
    exact [( HFirst;
             HNext HFirst;
             HNext (HNext HFirst);
             HNext (HNext (HNext HFirst)) )].
    repeat (constructor; simpl; intuition auto).
    repeat (constructor; simpl; intuition auto).
  Defined.
End CopyCacheProj.

Module CacheProtocol := MakeCacheProtocol CopyState CopyCacheProj.

Module App <: GlobalProtocol.
  Module St := CopyState.
  Definition Sigma := St.Sigma.
  Definition delta := CacheProtocol.delta.
End App.

Module CacheSub <: CacheSubProtocol.
  Module App := App.
  Module Proj := CopyCacheProj.

  Module CacheProtocol := MakeCacheProtocol App Proj.

  Definition protocolProj:SubProtocol App.delta CacheProtocol.delta.
  Proof.
    constructor; auto.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    simpl; auto.
  Qed.

  Definition invariantRespectsPrivateVars :
    forall d m s d' m' s',
      invariant App.delta d m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' m' s' ->
      invariant App.delta d' m' s'.
  Proof.
    simpl; intros; auto.
  Qed.
End CacheSub.

Module ConcurrentCache := MakeConcurrentCache CacheSub.

Import ConcurrentCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)