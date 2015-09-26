Require Import EventCSL.
Require Import EventCSLauto.
Require Import Hlist.
Require Import Star.
Require Import Coq.Program.Equality.
Require Import List.
Import List.ListNotations.
Open Scope list.

Section MemCache.

  Definition AssocCache := list (addr * valu).
  Definition cache_add (c:AssocCache) a v := (a, v) :: c.
  Fixpoint cache_get (c:AssocCache) a0 : option valu :=
    match c with
    | nil => None
    | (a, v) :: c' =>
      if (weq a a0) then Some v
      else cache_get c' a
    end.

End MemCache.

Definition S := unit.
Definition Mcontents := [AssocCache; Mutex].

Definition Cache : var Mcontents _ := HFirst.

Definition CacheL : var Mcontents _ := HNext HFirst.

Fixpoint cache_pred c : @pred addr (@weq addrlen) valu :=
  match c with
  | nil => emp
  | (a, v) :: c' => a |-> v * cache_pred c'
  end.

(** given a lock variable and some other variable v, generate a relation for tid
over memory that makes the variable read-only for non-owners. *)
Definition lock_protects (lvar : var Mcontents Mutex)
           {tv} (v : var Mcontents tv) tid (m m' : M Mcontents) :=
  forall owner_tid,
    get m lvar = Locked owner_tid ->
    tid <> owner_tid ->
    get m' v = get m v.

Definition lock_protects_disk (lvar : var Mcontents Mutex)
           tid (m : M Mcontents) (d d' : DISK) :=
  forall owner_tid,
    get m lvar = Locked owner_tid ->
    tid <> owner_tid ->
    d' = d.

Inductive lock_protocol (lvar : var Mcontents Mutex) (tid : ID) :  M Mcontents -> M Mcontents -> Prop :=
| NoChange : forall m m', get m lvar = get m' lvar ->
                     lock_protocol lvar tid m m'
| OwnerRelease : forall m m', get m lvar = Locked tid ->
                         get m' lvar = Open ->
                         lock_protocol lvar tid m m'
| OwnerAcquire : forall m m', get m lvar = Open ->
                         get m' lvar = Locked tid ->
                         lock_protocol lvar tid m m'.

Hint Constructors lock_protocol.

Definition cacheR tid : Relation Mcontents S :=
  fun dms dms' =>
    let '(d, m, _) := dms in
    let '(d', m', _) := dms' in
    lock_protocol CacheL tid m m' /\
    lock_protects CacheL Cache tid m m' /\
    lock_protects_disk CacheL tid m d d'.

Definition cacheI : Invariant Mcontents S :=
  fun m s d =>
    let c := get m Cache in
    exists F, (d |= F * cache_pred c)%judgement.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects_disk lock_protects : prog.
Hint Unfold cacheR cacheI : prog.

Theorem locks_are_all_CacheL : forall (l:var Mcontents Mutex),
    l = CacheL.
Proof.
  intros.
  unfold Mcontents in l.
  unfold var in l.
  unfold CacheL.
  dependent destruction l.
  contradict x0.
  admit. (* types are inequal *)

  dependent destruction l.
  auto.
  inversion l.
Admitted.

Theorem locks_are_not_caches : forall (l : var Mcontents Mutex),
    member_index l <> member_index Cache.
Proof.
  intros.
  rewrite (locks_are_all_CacheL l).
  cbn; auto.
Qed.

Hint Resolve locks_are_not_caches.

Ltac solve_get_set :=
  simpl_get_set;
  try match goal with
      | [ |- _ =p=> _ ] => cancel
      | [ |- ?p _ ] => match type of p with
                      | pred => solve [ pred_apply; cancel ]
                      end
      end.

Hint Extern 4 (get (set _ _ _) _ = _) => solve_get_set.
Hint Extern 4 (_ = get (set _ _ _) _) => solve_get_set.

Ltac dispatch :=
  intros; subst;
  cbn in *;
  (repeat match goal with
         | [ |- _ /\ _ ] => intuition
         | [ |- exists _, _ ] => eexists
         | _ => solve_get_set
         end); eauto.

Theorem cache_lock_step_available : lock_step_available cacheR cacheI.
Proof.
  unfold lock_step_available.
  repeat (autounfold with prog); unfold pred_in.
  intros.
  rewrite (locks_are_all_CacheL l).
  deex. exists d.
  case_eq (get m CacheL); intros.
  - dispatch.
  - case_eq (PeanoNat.Nat.eq_dec tid0 tid); intros.
    * dispatch.
    * exists (set m Open CacheL), s.
      dispatch.
      unfold StateR', othersR.
      eapply star_step; [| apply star_refl].
      dispatch.
Qed.

Hint Resolve cache_lock_step_available : prog.

Definition cacheS : transitions Mcontents S :=
  Build_transitions cacheR cacheI.

Definition locked_disk_read {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      let c' := cache_add c a v in
      Assgn Cache c';;
            rx v
  | Some v =>
    rx v
  end.

Definition locked_async_disk_read {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      Yield;;
           let c' := cache_add c a v in
           Assgn Cache c';;
                 rx v
  | Some v =>
    rx v
  end.

Lemma ptsto_conflict_falso : forall AT AEQ V a v0 v1 (F p:@pred AT AEQ V),
    a |-> v0 * a |-> v1 * F =p=> p.
Proof.
  unfold pimpl.
  intros.
  exfalso.
  eapply ptsto_conflict_F with (a := a) (m := m).
  pred_apply; cancel.
Qed.

Lemma cache_hit : forall c a v,
    cache_get c a = Some v ->
    exists F, cache_pred c =p=> F * a |-> v.
Proof.
  induction c; intros.
  inversion H.
  destruct a.
  simpl in *.
  match goal with
  | [ H: context[if ?b then _ else _] |- _ ] =>
    destruct b; simpl; inv_opt; eexists
  end.
  - cancel.
  - edestruct IHc; eauto.
    rewrite H.
    cancel.
    eapply pimpl_trans; [| apply ptsto_conflict_falso with (a := w)]; cancel.

    Grab Existential Variables.
    auto.
Qed.

Lemma cache_miss : forall F a v c d,
    (F * cache_pred c * a |-> v)%pred d ->
    cache_get c a = None.
Proof.
  intros.
  case_eq (cache_get c a); intros; auto.
  apply cache_hit in H0.
  deex.
  exfalso.
  eapply ptsto_conflict_F with (a := a) (m := d).
  pred_apply; cancel.
  rewrite H0.
  cancel.
Qed.

Theorem cache_add_pred : forall c a v,
    cache_pred (cache_add c a v) <=p=>
        a |-> v * cache_pred c.
Proof.
  auto.
Qed.

Hint Rewrite get_set.
Hint Rewrite cache_add_pred.

Hint Extern 0 (okToUnify (cache_pred ?c)
                         (cache_pred ?c)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (cache_pred (get ?m Cache))
                         (cache_pred (get ?m Cache))) => constructor : okToUnify.

Ltac valid_match_opt :=
  match goal with
  | [ |- valid _ _ _ _ (match ?discriminee with
                       | None => _
                       | Some _ => _
                       end) ] =>
    case_eq discriminee; intros
  end.

Ltac cache_contents_eq :=
  match goal with
  | [ H: cache_get ?c ?a = ?v1, H2 : cache_get ?c ?a = ?v2 |- _ ] =>
    assert (v1 = v2) by (
                         rewrite <- H;
                         rewrite <- H2;
                         auto)
  end; inv_opt.

Definition state_m (dms: DISK * M Mcontents * S) :=
  let '(_, m, _) := dms in m.

Definition state_d (dms: DISK * M Mcontents * S) :=
  let '(d, _, _) := dms in d.

Lemma cache_readonly' : forall tid dms dms',
    get (state_m dms) CacheL = Locked tid ->
    othersR cacheR tid dms dms' ->
    get (state_m dms') Cache = get (state_m dms) Cache /\
    get (state_m dms') CacheL = Locked tid.
Proof.
  repeat (autounfold with prog).
  unfold othersR.
  intros.
  destruct dms, dms'.
  destruct p, p0.
  cbn in *.
  deex.
  intuition eauto.
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; congruence
  end.
Qed.

Lemma cache_readonly : forall tid dms dms',
    get (state_m dms) CacheL = Locked tid ->
    star (othersR cacheR tid) dms dms' ->
    get (state_m dms') Cache = get (state_m dms) Cache /\
    get (state_m dms') CacheL = Locked tid.
Proof.
  intros.
  eapply (star_invariant _ _ (cache_readonly' tid));
    intros; intuition; eauto.
  congruence.
Qed.

Lemma disk_readonly' : forall tid dms dms',
    get (state_m dms) CacheL = Locked tid ->
    othersR cacheR tid dms dms' ->
    state_d dms' = state_d dms /\
    get (state_m dms') CacheL = Locked tid.
Proof.
  repeat (autounfold with prog).
  unfold othersR.
  intros.
  destruct dms, dms'.
  destruct p, p0.
  cbn in *.
  deex.
  intuition eauto.
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; congruence
  end.
Qed.

Lemma disk_readonly : forall tid dms dms',
    get (state_m dms) CacheL = Locked tid ->
    star (othersR cacheR tid) dms dms' ->
    state_d dms' = state_d dms /\
    get (state_m dms') CacheL = Locked tid.
Proof.
  intros.
  eapply (star_invariant _ _ (disk_readonly' tid));
    intros; intuition; eauto.
  congruence.
Qed.

Ltac remove_duplicates :=
  repeat match goal with
         | [ H: ?p, H': ?p |- _ ] =>
           match type of p with
           | Prop => clear H'
           end
         end.

Hint Extern 4 (get (set _ _ _) _ = _) => simpl_get_set : prog.
Hint Extern 4 (_ = get (set _ _ _) _) => simpl_get_set : prog.

Ltac mem_contents_eq :=
  match goal with
  | [ H: get ?m ?var = _, H': get ?m ?var = _ |- _ ] =>
    rewrite H in H';
      try inversion H';
      subst
  end.

Ltac star_readonly thm :=
  match goal with
  | [ H: star _ _ _ |- _ ] =>
    let H' := fresh in
    pose proof H as H';
      apply thm in H'; [| cbn; now auto ];
      cbn in H';
      destruct H'
  end.

Ltac cache_locked := star_readonly cache_readonly.
Ltac disk_locked := star_readonly disk_readonly.

Theorem locked_disk_read_miss_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache) * a |-> v /\
                  get m CacheL = Locked tid
     | POST d' m' _ r: d' |= F * cache_pred (get m' Cache) /\
                       r = v /\
                       get m' CacheL = Locked tid
    }} locked_disk_read a.
Proof.
  unfold locked_disk_read.
  hoare.
  (* TODO: it would be nice to automate this pattern, but the problem
     is that the hypothesis pattern depends on the lemma and is hard
     to extract from Ltac *)
  match goal with
  | [ H: (F * cache_pred _ * _)%pred d |- _ ] =>
    let H' := fresh in
    pose proof H as H';
      apply cache_miss in H'
  end.
  valid_match_opt; hoare; solve_get_set;
  try cache_contents_eq;
  try congruence.
Qed.

Theorem locked_disk_read_hit_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache) /\
                  cache_get (get m Cache) a = Some v
     | POST d' m' _ r: d' |= F * cache_pred (get m' Cache) /\
                       r = v
    }} locked_disk_read a.
Proof.
  unfold locked_disk_read.
  hoare.
  valid_match_opt; hoare; solve_get_set;
  try cache_contents_eq;
  try congruence.

  Grab Existential Variables.
  all: auto.
Qed.

(** FIXME: this is a terrible hack. When we have two hypotheses about
the same memory, it deletes the older one, since we carry forward less
information then what we get by using the fact that the disk hasn't
changed (from the lock invariant) and pred_apply then picks the wrong
disk. It has two problems:

* it isn't guaranteed to delete the less useful premise
* the solution to this problem is actually to backtrack over
  pred_apply (there are only two options, after all)
*)
Ltac keep_older_pred :=
  match goal with
  | [ H: _ ?d, H' : ?p ?d |- _ ] =>
    match type of (d, p) with
      | (DISK * pred)%type => clear H'
    end
  end.

Ltac simplify :=
  step_simplifier;
  try cache_locked;
  try disk_locked;
  subst;
  try keep_older_pred.

Ltac finish :=
  solve_get_set;
  try solve [ pred_apply; cancel ];
  try cache_contents_eq;
  try congruence;
  eauto.

Theorem locked_async_disk_read_miss_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache) * a |-> v /\
                  get m CacheL = Locked tid
     | POST d' m' _ r: exists F',
         d' |= F' * cache_pred (get m' Cache) /\
         r = v /\
         get m' CacheL = Locked tid
    }} locked_async_disk_read a.
Proof.
  unfold locked_async_disk_read.
  hoare.
  match goal with
  | [ H: (F * cache_pred _ * _)%pred d |- _ ] =>
    let H' := fresh in
    pose proof H as H';
      apply cache_miss in H'
  end.
  valid_match_opt; hoare pre simplify with finish.
Qed.

Definition disk_read {T} a rx : prog _ _ T :=
  AcquireLock CacheL;;
              v <- locked_disk_read a;
              Assgn CacheL Open;;
              rx v.

(* These two theorems are no longer true: they attempt to separate
cache miss and cache hit into two cases via the precondition, but this
trick no longer works: the cache can change after acquiring the lock,
and the precondtion can't talk about this new cache. We really need a
combined theorem (proven from the above two specs), but this is hard
to state since it's necessary that a |-> v is in F or cache_pred,
which I'm not sure how to state and then guarantee across
AcquireLock. *)

Theorem disk_read_miss_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache) * a |-> v
     | POST d' m' _ r: d' |= F * cache_pred (get m' Cache) /\
                       r = v
    }} disk_read a.
Proof.
  unfold disk_read.
  hoare.
Abort.

Theorem disk_read_hit_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache) /\
                  cache_get (get m Cache) a = Some v
     | POST d' m' _ r: d' |= F * cache_pred (get m' Cache) /\
                       r = v
    }} disk_read a.
Proof.
  unfold disk_read.
  hoare.
Abort.