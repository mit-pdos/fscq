Require Import Locking.
Require Import Automation.
Import List.
Import List.ListNotations.
Require Import FMapAVL.
Require Import FMapFacts.

Module Make (AOT: OrderedType).

Module Map := FMapAVL.Make(AOT).
Module MapFacts := WFacts_fun AOT Map.
Module MapProperties := WProperties_fun AOT Map.

Local Definition A := AOT.t.

Local Definition M := Map.t BusyFlag.
Local Definition S := Map.t BusyFlagOwner.

Implicit Types (m:M) (s:S) (a: A).

Local Definition mem m a :=
  match Map.find a m with
  | Some l => l
  | None => Open
  end.

Local Definition get s a :=
  match Map.find a s with
  | Some l => l
  | None => NoOwner
  end.

Definition rep m s :=
  forall a, ghost_lock_invariant (mem m a) (get s a).

Section Updates.

Definition set_locked m a :=
  Map.add a Locked m.

Definition add_lock s a tid :=
  Map.add a (Owned tid) s.

Hint Unfold rep
  mem get
  set_locked add_lock : locks.
Hint Rewrite MapFacts.add_eq_o using (solve [ auto ]) : map.
Hint Rewrite MapFacts.add_neq_o using (solve [ auto ]) : map.

Hint Constructors ghost_lock_invariant.

Local Theorem rep_stable_add : forall m s a tid,
  rep m s ->
  rep (set_locked m a) (add_lock s a tid).
Proof.
  repeat autounfold with locks; intros.
  destruct (AOT.eq_dec a a0); autorewrite with map in *; eauto.
Qed.

Definition set_open m a :=
  Map.remove a m.

Definition free_lock s a :=
  Map.remove a s.

Hint Unfold set_open free_lock : locks.
Hint Rewrite MapFacts.remove_eq_o using (solve [ auto ]) : map.
Hint Rewrite MapFacts.remove_neq_o using (solve [ auto ] ) : map.

Local Theorem rep_stable_remove : forall m s a,
  rep m s ->
  rep (set_open m a) (free_lock s a).
Proof.
  repeat autounfold with locks; intros.
  destruct (AOT.eq_dec a a0); autorewrite with map in *; eauto.
Qed.

Ltac t :=
  repeat autounfold with locks; intros; subst;
  autorewrite with map; auto.

Theorem get_add_lock : forall s a a' tid,
  a = a' ->
  get (add_lock s a tid) a' = Owned tid.
Proof.
  t.
Qed.

Theorem get_add_lock_other : forall s a a' tid,
  ~AOT.eq a a' ->
  get (add_lock s a tid) a' = get s a'.
Proof.
  t.
Qed.

Theorem get_free_lock : forall s a a',
  AOT.eq a a' ->
  get (free_lock s a) a' = NoOwner.
Proof.
  t.
Qed.

Theorem get_free_lock_other : forall s a a',
  ~AOT.eq a a' ->
  get (free_lock s a) a' = get s a'.
Proof.
  t.
Qed.

Theorem mem_set_locked : forall m a a',
    AOT.eq a a' ->
    mem (set_locked m a) a' = Locked.
Proof.
  t.
Qed.

Theorem mem_set_locked_other : forall m a a',
    ~AOT.eq a a' ->
    mem (set_locked m a) a' = mem m a'.
Proof.
  t.
Qed.

Theorem mem_set_open : forall m a a',
    AOT.eq a a' ->
    mem (set_open m a) a' = Open.
Proof.
  t.
Qed.

Theorem mem_set_open_other : forall m a a',
    ~AOT.eq a a' ->
    mem (set_open m a) a' = mem m a'.
Proof.
  t.
Qed.

End Updates.

Hint Rewrite get_add_lock
     get_add_lock_other
     get_free_lock
     get_free_lock_other
     mem_set_locked
     mem_set_locked_other
     mem_set_open
     mem_set_open_other using (solve [ auto ] ) : locks.

Definition is_open a m : {mem m a = Open} + {mem m a <> Open}.
Proof.
  destruct (mem m a);
    left + right;
    congruence.
Defined.

End Make.