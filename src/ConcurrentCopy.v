Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import ConcurrentCache.
Require Import DiskReaders.
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

Theorem vdisk_not_cache_or_disk0 :
  HIn CacheProtocol.vdisk [(CacheProtocol.vCache; CacheProtocol.vDisk0)] -> False.
Proof.
  rewrite (hin_iff_index_in CacheProtocol.vdisk); simpl.
  unfold CacheProtocol.vCache, CacheProtocol.vdisk, CacheProtocol.vDisk0.
  simpl.
  repeat (rewrite get_first; simpl) ||
         (rewrite get_next; simpl).
  intuition.
Qed.

Hint Resolve vdisk_not_cache_or_disk0.

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

Definition copy a a' :=
  opt_v <- cache_read a;
    match opt_v with
    | None => _ <- cache_abort;
               Ret false
    | Some v => ok <- cache_write a' v;
                 if ok then
                   Ret true
                 else
                   _ <- cache_abort;
                 Ret false
    end.

Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.

(* gives all cache variables *)
Import CacheSub.CacheProtocol.

Lemma same_domain_vdisk : forall d m s d' m' s' tid,
    invariant delta d m s ->
    guar delta tid s s' ->
    invariant delta d' m' s' ->
    same_domain (get vdisk s) (get vdisk s').
Proof.
  simplify.
Abort.

Theorem copy_ok : forall a a',
    SPEC App.delta, tid |-
                {{ v v',
                 | PRE d m s_i s:
                     invariant App.delta d m s /\
                     get vdisk s a = Some v /\
                     get vdisk s a' = Some v'
                 | POST d' m' s_i' s' r:
                     invariant App.delta d' m' s' /\
                     (r = true ->
                      get vdisk s' = upd (get vdisk s) a' v) /\
                     (r = false ->
                      get vdisk s' = hide_readers (get vDisk0 s))
                }} copy a a'.
Proof.
  hoare.
  eexists; simplify; finish.
  hoare.
  assert (w = v).
  { match goal with
    | [ H: forall _, Some ?w = Some _ -> _ |- _ ] =>
      specialize (H w)
    end; eauto. }
  subst.
  (* TODO: need a derived same_domain for vdisk from invariant + guar *)

  assert (get vdisk s = get vdisk s0) as Hvdiskeq.
  match goal with
  | [ H: modified _ s s0 |- _ ] =>
    apply H; auto
  end.
  rewrite <- Hvdiskeq in *.
  eexists; simplify; finish.

  hoare.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)