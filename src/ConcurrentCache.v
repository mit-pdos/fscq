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
         (d |= cache_pred c;)%judgement.

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

Lemma cache_hit : forall c a v,
    cache_get c a = Some v ->
    exists F, cache_pred c =p=> F * a |-> v.
Proof.
  induction c; intros.
  inversion H.
  destruct a.
  simpl in H.
  destruct (weq w a0); simpl.
  inversion H.
  subst.
  eexists.
  cancel.
  edestruct IHc; eauto.
  eexists.
  rewrite H0.
  cancel.
  intro m; intros.
  exfalso.
  eapply ptsto_conflict_F with (m := m) (a := w).
  pred_apply; cancel.

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

Theorem disk_read_miss_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
       | PRE d m s: d |= F * cache_pred (get m Cache) * a |-> v;
       | POST d' m' s' r: d' |= F * cache_pred (get m' Cache);
       /\ r = v
    }} disk_read a.
Proof.
  unfold disk_read.
  hoare.
  match goal with
  | [ |- valid _ _ _ _ (match ?discriminee with
                       | None => _
                       | Some _ => _
                       end) ] =>
    case_eq discriminee; intros
  end.
  (* cache hit; impossible due to precondition *)
  intros_pre.
  intuition; subst.
  apply cache_miss in H0.
  assert (None = Some w).
  rewrite <- H0.
  rewrite <- H.
  auto.
  inversion H4.

  hoare.
  unfold cacheI.
  unfold pimpl; intros.
  unfold pred_in.
  pred_apply; cancel.
Admitted.