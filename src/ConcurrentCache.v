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

Section Lock.
  Inductive Lock := Open | Locked.
End Lock.

Definition S := unit.
Definition Mcontents := [AssocCache; Lock].

Definition Cache := Eval simpl in VAR 0 IN Mcontents.

Definition CacheL := @HNext _ _ AssocCache _ (VAR 0 IN [Lock]).

Fixpoint cache_pred c : @pred addr (@weq addrlen) valu :=
  match c with
  | nil => emp
  | (a, v) :: c' => a |-> v * cache_pred c'
  end.

Definition cacheR : Relation Mcontents S :=
  fun tid dms dms' =>
    True.

Definition cacheI : Invariant Mcontents S :=
  fun m s d =>
    forall c, c = get m Cache ->
         exists F, (d |= F * cache_pred c;)%judgement.

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
       | PRE d m _: d |= F * cache_pred (get m Cache) * a |-> v;
       | POST d' m' _ r: d' |= F * cache_pred (get m' Cache);
       /\ r = v
    }} disk_read a.
Proof.
  unfold disk_read.
  hoare.
  valid_match_opt.
  (* cache hit; impossible due to precondition *)
  intros_pre.
  intuition; subst.
  apply cache_miss in H0.
  cache_contents_eq.

  hoare.
  autorewrite with core; cancel.
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

Check ptsto_eq.

Theorem disk_read_hit_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m _: d |= F * cache_pred (get m Cache);
       /\ (cache_get (get m Cache) a = Some v)
       | POST d' m' _ r: d' |= F * cache_pred (get m Cache);
       /\ r = v
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