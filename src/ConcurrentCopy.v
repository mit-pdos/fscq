Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import ConcurrentCache.
Require Import DiskReaders.
Require Import Omega.
Require Import Star.
Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

(* somewhat oddly, Sigma now refers to the cache state - would have hidden that
and referred to it qualified if Coq let me do so cleanly *)

(** Copy example

Each thread tid copies from address 0 to the location (tid+1).

The cache is always committed; transactions can only do writes to (tid+1). *)

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

Definition destinations_readonly tid (s s': abstraction CopyState.Sigma) :=
  forall a, a <> tid + 1 ->
       get CacheProtocol.vdisk s' a = get CacheProtocol.vdisk s a.

Theorem destinations_readonly_preorder : forall tid,
    PreOrder (destinations_readonly tid).
Proof.
  unfold destinations_readonly; intros.
  constructor; hnf; intros; eauto.
  rewrite <- H by auto.
  eauto.
Qed.

Definition cache_committed (s: abstraction CopyState.Sigma) :=
  get CacheProtocol.vdisk s = hide_readers (get CacheProtocol.vDisk0 s).

Module App <: GlobalProtocol.
  Module St := CopyState.
  Definition Sigma := St.Sigma.

  Definition copyInvariant d m s :=
    cache_committed s /\
    invariant CacheProtocol.delta d m s.

  Definition copyGuar tid (s s': abstraction Sigma) :=
    guar CacheProtocol.delta tid s s' /\
    destinations_readonly tid s s'.

  Theorem copyGuar_preorder : forall tid, PreOrder (copyGuar tid).
  Proof.
    intros.
    (* TODO: move and_preorder somewhere else *)
    apply CacheProtocol.and_preorder.
    apply guar_preorder.
    apply destinations_readonly_preorder.
  Qed.

  Definition delta :=
    {| invariant := copyInvariant;
       guar := copyGuar;
       guar_preorder := copyGuar_preorder |}.

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

Theorem vWriteBuffer_not_cache_or_disk0 :
  HIn CacheProtocol.vWriteBuffer [(CacheProtocol.vCache; CacheProtocol.vDisk0)] -> False.
Proof.
  rewrite (hin_iff_index_in CacheProtocol.vWriteBuffer); simpl.
  unfold CacheProtocol.vCache, CacheProtocol.vWriteBuffer, CacheProtocol.vDisk0.
  simpl.
  repeat (rewrite get_first; simpl) ||
         (rewrite get_next; simpl).
  intuition.
Qed.

Hint Resolve vdisk_not_cache_or_disk0.
Hint Resolve vWriteBuffer_not_cache_or_disk0.

Module CacheSub <: CacheSubProtocol.
  Module App := App.
  Module Proj := CopyCacheProj.

  Module CacheProtocol := CacheProtocol.
  Import CacheProtocol.

  Definition protocolProj:SubProtocol App.delta delta.
  Proof.
    constructor.
    - intros.
      apply H.
    - intros.
      apply H.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar delta tid s s' ->
      modified [( vCache; vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    simpl; intros.
    unfold App.copyGuar; split; auto.
    unfold destinations_readonly; intros.
    assert (get vdisk s = get vdisk s').
    apply H0; auto.
    congruence.
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
    split; auto.
    destruct H.
    unfold cache_committed in *.
    unfold Top.CacheProtocol.vdisk, Top.CacheProtocol.vDisk0 in *.
    fold vdisk vDisk0 in *.
    assert (get vdisk s = get vdisk s') as Heq.
    apply H0; auto.
    rewrite Heq in *.
    unfold id in *.
    rewrite H.
    assert (get vWriteBuffer s = get vWriteBuffer s').
    apply H0; auto.
    (* this is actually true since the write buffer didn't change, but it
    depends on reasoning about the cache_rep in a pretty deep way - this will
    all be fixed by splitting vDisk0 into the part dealing with readers in the
    cache_rep and the public linearized disk without readers *)
    admit.
  Admitted.

End CacheSub.

Module ConcurrentCache := MakeConcurrentCache CacheSub.
Import ConcurrentCache.

Definition copy :=
  tid <- GetTID;
  opt_v <- cache_read 0;
    match opt_v with
    | None => _ <- cache_abort;
               _ <- Yield 0;
               Ret false
    | Some v => ok <- cache_write (tid+1) v;
                 if ok then
                   _ <- cache_commit;
                   Ret true
                 else
                   _ <- cache_abort;
                 _ <- Yield (tid+1);
                 Ret false
    end.

Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.

(* gives all cache variables *)
Import CacheSub.CacheProtocol.

Lemma destinations_readonly_vdisk_eq : forall s s',
    get vdisk s = get vdisk s' ->
    forall tid, destinations_readonly tid s s'.
Proof.
  unfold destinations_readonly; intros.
  congruence.
Qed.

Hint Resolve destinations_readonly_vdisk_eq.

Lemma destinations_readonly_upd : forall (s s': abstraction CopyState.Sigma) tid v,
    get vdisk s' = upd (get vdisk s) (tid+1) v ->
    destinations_readonly tid s s'.
Proof.
  unfold destinations_readonly; intros.
  rewrite H.
  autorewrite with upd; now auto.
Qed.

Hint Resolve destinations_readonly_upd.

Ltac unfolds :=
  unfold CacheSub.App.Sigma, CacheSub.App.St.Sigma, CopyState.Sigma in *;
  unfold CacheProtocol.vdisk, CacheProtocol.vDisk0 in *;
  fold vdisk vDisk0 in *.

(* local spec for cache_abort in terms of global invariant *)

Theorem cache_abort_ok :
  SPEC App.delta, tid |-
{{ (_:unit),
 | PRE d m s_i s:
     invariant CacheProtocol.delta d m s
 | POST d' m' s_i' s' _:
     invariant App.delta d' m' s' /\
     get vdisk s' = hide_readers (get vDisk0 s) /\
     guar CacheProtocol.delta tid s s' /\
     s_i' = s_i
}} cache_abort.
Proof.
  hoare.
  split; eauto.
  unfold cache_committed.
  unfolds; congruence.
Qed.

Hint Extern 1 {{cache_abort; _}} => apply cache_abort_ok : prog.

Ltac simp_hook ::=
     match goal with
     | [ H: modified [( vCache; vDisk0 )] ?s ?s' |- _ ] =>
       learn that (ltac:(apply H; auto) : get vdisk s = get vdisk s')
     end.

Lemma guar_refl : forall Sigma tid (s: abstraction Sigma) (delta: Protocol Sigma),
    guar delta tid s s.
Proof.
  intros.
  apply guar_preorder.
Qed.

Hint Resolve guar_refl.

Theorem copy_ok :
    SPEC App.delta, tid |-
                {{ v v',
                 | PRE d m s_i s:
                     invariant App.delta d m s /\
                     get vdisk s 0 = Some v /\
                     get vdisk s (tid+1) = Some v' /\
                     guar App.delta tid s_i s
                 | POST d' m' s_i' s' r:
                     invariant App.delta d' m' s' /\
                     (r = true ->
                      get vdisk s' (tid+1) = Some v) /\
                     (r = false ->
                      rely App.delta tid s s') /\
                     guar App.delta tid s_i' s'
                }} copy.
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

  eexists; simplify; finish.
  (* TODO: get vdisk s0's are different - probably something
  module-related *) (* get vdisk s0 equality is about variable in
  CopyState.Sigma whereas goal is about CacheSub.App.Sigma *)
  Set Printing Implicit. idtac.
  unfolds.
  replace (get vdisk s0).
  Unset Printing Implicit.
  eauto.

  hoare.

  split; auto.
  unfold cache_committed.
  unfolds.
  congruence.

  unfolds.
  replace (get vdisk s2).
  match goal with
  | [ H: get vdisk s1 = upd _ _ _ |- _ ] =>
    rewrite H
  end.
  autorewrite with upd; now auto.

  eapply guar_preorder with s; eauto.
  eapply guar_preorder with s0; eauto.
  split; eauto.
  eapply guar_preorder with s1.
  split; eauto.
  split; eauto.

  eapply guar_preorder with s; eauto.
  eapply guar_preorder with s0.
  split; eauto.
  split; eauto.
  unfold destinations_readonly; intros; unfolds.
  destruct H; unfold cache_committed in H; unfolds.
  (* these replaces are unnecessary, they just show part of what's going on *)
  replace (get vdisk s1).
  replace (get vdisk s0).
  congruence.

  eapply rely_trans with s1; eauto.
  unfold rely, others.
  eapply star_one_step.
  exists (tid+1); split; [ omega | ].
  split.
  unshelve eapply cache_guar_tid_independent; eauto.
  apply destinations_readonly_vdisk_eq.
  destruct H; unfold cache_committed in H; unfolds.
  congruence.

  eapply guar_preorder with s; eauto.
  eapply guar_preorder with s0.
  split; eauto.
  split; eauto.
  unfold destinations_readonly; intros; unfolds.
  destruct H; unfold cache_committed in H; unfolds.
  replace (get vdisk s1).
  replace (get vdisk s0).
  congruence.

  eapply rely_trans with s1; eauto.
  unfold rely, others.
  eapply star_one_step.
  exists (tid+1); split; [ omega | ].
  split.
  unshelve eapply cache_guar_tid_independent; eauto.
  apply destinations_readonly_vdisk_eq.
  destruct H; unfold cache_committed in H; unfolds.
  congruence.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)