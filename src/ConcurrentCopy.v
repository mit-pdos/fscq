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
             HNext (HNext (HNext HFirst));
             HNext (HNext (HNext (HNext HFirst))) )].
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
  get CacheProtocol.vdisk s = get CacheProtocol.vdisk0 s.

Module App <: GlobalProtocol.
  Module St := CopyState.
  Definition Sigma := St.Sigma.

  Definition copyInvariant d hm m s :=
    cache_committed s /\
    invariant CacheProtocol.delta d hm m s.

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

Ltac unfold_list l :=
  match l with
  | HNil => idtac
  | HCons ?v ?l' => unfold v; unfold_list l'
  end.

Ltac prove_not_hin :=
  match goal with
  | |- HIn ?v ?l -> False =>
    rewrite (hin_iff_index_in v); simpl;
    unfold v; unfold_list l; simpl;
    repeat (rewrite get_first; simpl) ||
           (rewrite get_next; simpl);
    intuition auto
  end.

Hint Extern 3 (HIn _ _ -> False) => prove_not_hin.

Ltac not_modified v :=
  match goal with
  | [ H: modified _ ?s ?s' |- _ ] =>
    lazymatch goal with
    | [ H: get v s = get v s' |- _ ] => fail
    | _ => assert (get v s = get v s') by (apply H; prove_not_hin)
    end
  end.

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
    not_modified vdisk.
    congruence.
  Qed.

  Definition invariantRespectsPrivateVars :
    forall d hm m s d' hm' m' s',
      invariant App.delta d hm m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' hm' m' s' ->
      hashmap_le hm hm' ->
      invariant App.delta d' hm' m' s'.
  Proof.
    simpl; intros; auto.
    split; auto.
    destruct H.
    unfold cache_committed in *.
    unfold Top.CacheProtocol.vdisk,
    Top.CacheProtocol.vdisk0,
    Top.CacheProtocol.vDisk0 in *;
      fold vdisk vdisk0 vDisk0 in *.
    not_modified vdisk.
    not_modified vdisk0.
    unfold id in *; simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite <- H
           end.
    auto.
  Qed.

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
    | Some v => _ <- cache_write (tid+1) v;
                 _ <- cache_commit;
                 Ret true
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
  unfold CacheProtocol.vdisk, CacheProtocol.vdisk0, CacheProtocol.vDisk0 in *;
  fold vdisk vdisk0 vDisk0 in *.

(* local spec for cache_abort in terms of global invariant *)

Theorem cache_abort_ok :
  SPEC App.delta, tid |-
{{ (_:unit),
 | PRE d hm m s_i s:
     invariant CacheProtocol.delta d hm m s
 | POST d' hm' m' s_i' s' _:
     invariant App.delta d' hm' m' s' /\
     get vdisk s' = get vdisk0 s /\
     guar CacheProtocol.delta tid s s' /\
     hm' = hm /\
     s_i' = s_i
}} cache_abort.
Proof.
  hoare.
  split; eauto.
  unfold cache_committed.
  unfolds.
  not_modified vdisk0.
  unfold CopyState.Sigma in *.
  congruence.
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

Lemma invariant_cache_committed : forall d hm m s,
    invariant App.delta d hm m s ->
    get vdisk s = get vdisk0 s.
Proof.
  destruct 1; auto.
Qed.

Hint Resolve invariant_cache_committed.

Ltac simp_hook ::=
     match goal with
     | [ H: invariant App.delta _ _ _ _ |- _ ] =>
       learn that (invariant_cache_committed H)
     end ||
     (progress repeat not_modified vdisk) ||
     (progress repeat not_modified vdisk0).

Theorem copy_ok :
    SPEC App.delta, tid |-
                {{ v v',
                 | PRE d hm m s_i s:
                     invariant App.delta d hm m s /\
                     get vdisk s 0 = Some v /\
                     get vdisk s (tid+1) = Some v' /\
                     guar App.delta tid s_i s
                 | POST d' hm' m' s_i' s' r:
                     invariant App.delta d' hm' m' s' /\
                     (r = true ->
                      get vdisk s' = upd (get vdisk s) (tid+1) v) /\
                     (r = false ->
                      rely App.delta tid s s') /\
                     hashmap_le hm hm' /\
                     guar App.delta tid s_i' s'
                }} copy.
Proof.
  hoare.
  eexists; simplify; finish.
  hoare. (* 20s *)

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

  hoare. (* 30s *)

  split; auto.
  unfold cache_committed.
  unfolds.
  congruence.

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
  congruence.

  eapply rely_trans with s1; eauto.
  unfold rely, others.
  eapply star_one_step.
  exists (tid+1); split; [ omega | ].
  split.
  unfold delta in *; simpl in *.
  Search s s0.
  unshelve eapply cache_guar_tid_independent; eauto.
  apply destinations_readonly_vdisk_eq.
  simpl in *.
  congruence.
Qed.

Hint Extern 1 {{copy; _}} => apply copy_ok : prog.

(* as a small step to retrying copy, retry up to once and then give up *)
Definition copy_retry1 :=
  ok <- copy;
    if ok then
      Ret true
    else
      copy.

Lemma rely_destination_stable : forall tid (s s': abstraction App.Sigma),
    rely App.delta tid s s' ->
    get vdisk s' (tid+1) = get vdisk s (tid+1).
Proof.
  induction 1; intros; auto.
  unfold others in H; deex.
  unfold App.delta, App.copyGuar in H1; simpl in *; destruct_ands.
  rewrite IHstar.
  unfold TID in *.
  rewrite H2; auto.
Qed.

Lemma rely_addr_0_stable : forall tid (s s': abstraction App.Sigma),
    rely App.delta tid s s' ->
    get vdisk s' 0 = get vdisk s 0.
Proof.
  induction 1; auto.
  rewrite IHstar.
  unfold others in H; deex.
  unfold App.delta, App.copyGuar in H1; simpl in *; destruct_ands.
  rewrite H2; auto.
Qed.

Ltac simp_hook ::=
     match goal with
     | [ H: rely App.delta _ _ _ |- _ ] =>
       learn that (rely_addr_0_stable H) ||
             learn that (rely_destination_stable H)
     end.

Ltac descend :=
  repeat match goal with
  | |- exists _, _ => eexists
  end.

Theorem copy_retry1_ok :
    SPEC App.delta, tid |-
                {{ v v',
                 | PRE d hm m s_i s:
                     invariant App.delta d hm m s /\
                     get vdisk s 0 = Some v /\
                     get vdisk s (tid+1) = Some v' /\
                     guar App.delta tid s_i s
                 | POST d'' hm'' m'' s_i' s'' r:
                     invariant App.delta d'' hm'' m'' s'' /\
                     (r = false ->
                      rely App.delta tid s s'') /\
                     (r = true ->
                      exists d' hm' m' s',
                        rely App.delta tid s s' /\
                        invariant App.delta d' hm' m' s' /\
                        get vdisk s'' = upd (get vdisk s') (tid+1) v) /\
                     hashmap_le hm hm'' /\
                     guar App.delta tid s_i' s''
                }} copy_retry1.
Proof.
  intros.
  step.

  descend; simplify; finish.
  step.

  step.
  (* trivial rely *)
  exists d, hm, m, s.
  simplify; finish.
  apply star_refl.
  step.

  (* We don't generate enough equalities for existentials to be automatically
  instantiated (congruence is dispatching the goals), but we could do so. Before
  a tactic called complete_mem_equalities would do this, taking [m a = Some v]
  and [m = m'] and producing [m' a = Some v]. This quickly gets out of hand
  without some control over, eg, what direction equalities use. *)
  exists v, v'; simplify; finish.
  step.

  eapply rely_trans; eauto.

  exists d0, hm0, m0, s0; intuition eauto.
  eapply hashmap_le_preorder; eauto.
Qed.

Fixpoint copy_fuel_retry n :=
  match n with
  | 0 => copy
  | S n' => ok <- copy;
             if ok then
               Ret true
             else
               copy_fuel_retry n'
  end.

Theorem copy_fuel_retry_ok : forall n,
    SPEC App.delta, tid |-
                {{ v v',
                 | PRE d hm m s_i s:
                     invariant App.delta d hm m s /\
                     get vdisk s 0 = Some v /\
                     get vdisk s (tid+1) = Some v' /\
                     guar App.delta tid s_i s
                 | POST d'' hm'' m'' s_i' s'' r:
                     invariant App.delta d'' hm'' m'' s'' /\
                     (r = false ->
                      rely App.delta tid s s'') /\
                     (r = true ->
                      exists d' hm' m' s',
                        rely App.delta tid s s' /\
                        invariant App.delta d' hm' m' s' /\
                        get vdisk s'' = upd (get vdisk s') (tid+1) v) /\
                     hashmap_le hm hm'' /\
                     guar App.delta tid s_i' s''
                }} copy_fuel_retry n.
Proof.
  induction n; intros.
  - step.
    descend; simplify; finish.
    step.

    exists d, hm, m, s; intuition eauto.
    apply star_refl.
  - simpl; step.
    descend; simplify; finish.
    step.
    step.

    exists d, hm, m, s; intuition eauto.
    apply star_refl.

    step.
    exists v, v'; simplify; finish.

    step.
    eapply rely_trans; eauto.

    exists d', hm', m', s'; intuition eauto.
    eapply rely_trans; eauto.

    eapply hashmap_le_preorder; eauto.
Qed.

(* copy_retry1 is a special case of having fuel (where you only have 1 fuel).

 Of course 0 fuel is just copy (even moreso evident from the definition of
 copy_fuel_retry). *)
Lemma copy_retry1_is_1_fuel :
  copy_retry1 = copy_fuel_retry 1.
Proof.
  reflexivity.
Qed.

CoFixpoint copy_retry :=
  ok <- copy;
    if ok then
      Ret tt
    else
      copy_retry.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)