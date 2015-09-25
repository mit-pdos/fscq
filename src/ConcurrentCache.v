Require Import EventCSL.
Require Import EventCSLauto.
Require Import Hlist.
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

Definition Cache := Eval simpl in VAR 0 IN Mcontents.

Definition CacheL := Eval simpl in @HNext _ _ AssocCache _ (VAR 0 IN [Mutex]).

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
    let '(_, m, _) := dms in
    let '(_', m', _) := dms' in
    lock_protocol CacheL tid m m' /\
    lock_protects CacheL Cache tid m m'.

Definition cacheI : Invariant Mcontents S :=
  fun m s d =>
    forall c, c = get m Cache ->
         exists F, (d |= F * cache_pred c)%judgement.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects : prog.
Hint Unfold cacheR cacheI : prog.

Definition cacheS : transitions Mcontents S :=
  Build_transitions cacheR cacheI.

Definition disk_read {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      let c' := cache_add c a v in
      Assgn Cache c';;
      rx v
  | Some v => rx v
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

Theorem disk_read_miss_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache) * a |-> v /\
                  get m CacheL = Locked tid
     | POST d' m' _ r: d' |= F * cache_pred (get m' Cache) /\
                       r = v
    }} disk_read a.
Proof.
  unfold disk_read.
  hoare.
  valid_match_opt.
  (* cache hit; impossible due to precondition *)
  intros_pre.
  intuition; subst.
  Check cache_miss.
  match goal with
  | [ H: context[cache_pred (get m Cache)] |- _ ] =>
    apply cache_miss in H
  end.
  cache_contents_eq.

  hoare.
  autorewrite with core; cancel.
  rewrite get_set_other; cbn; auto.

  (* this is the read-only obligation from the lock protocol, which
  only applies if you're not the owner.  *)
  congruence.
  autorewrite with core; cancel.
Qed.

Lemma emp_not_ptsto : forall AT AEQ V (F: @pred AT AEQ V) a v,
    ~ (emp =p=> F * a |-> v).
Proof.
  unfold not, pimpl; intros.
  specialize (H empty_mem).
  assert (@emp AT AEQ V empty_mem) by (apply emp_empty_mem).
  intuition.
  apply ptsto_valid' in H1.
  inversion H1.
Qed.

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
  valid_match_opt.
  hoare.
  cache_contents_eq; auto.
  step; cache_contents_eq.

  Grab Existential Variables.
  all: auto.
Qed.

CoFixpoint lock {T} (rx: unit -> prog Mcontents S T) :=
  l <- Get CacheL;
  If (is_locked l) {
       Yield;;
            lock rx
     } else {
    tid <- GetTID;
    Assgn CacheL (Locked tid);;
          rx tt
  }.

Theorem lock_ok :
  cacheS TID: tid |-
{{ (_:unit),
 | PRE d m s: d |= cacheI m s
 | POST d' m' s' _: d' |= cacheI m' s' /\
                    get m' CacheL = Locked tid
}} lock.
Proof.
  unfold lock.
  intros_pre.
Abort.