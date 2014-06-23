Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Definition storage := nat -> nat.
Definition st_write (s:storage) a v :=
  fun a' => if eq_nat_dec a a' then v else s a'.
Definition st_read (s:storage) a :=
  s a.

Definition empty_storage : storage := fun a => 0.

Print le_S.

Inductive steppable (A:Type) :=
  | step : (storage -> storage * A) -> steppable A
  | mbind : forall B:Type, steppable B -> (B -> steppable A) -> steppable A
  | mret : A -> steppable A.

Definition read a : steppable nat := step (fun s => (s, st_read s a)).
Definition write a v : steppable unit := step (fun s => (st_write s a v, tt)).

Notation "'do' x <- y ; z" := (mbind y (fun x => z))
  (left associativity, at level 200, x ident, y at level 100, z at level 200).

Fixpoint run {A:Type} (f:steppable A) (s:storage) (rem:nat) : storage * option (A * nat) :=
  match f with
  | step op => match rem with
               | O => (s, None)
               | S rem' => match op s with (s', b) => (s', Some (b, rem')) end
               end
  | mbind _ a b => match run a s rem with
                   | (s', None) => (s', None)
                   | (s', Some (v, rem')) => run (b v) s' rem'
                   end
  | mret a => (s, Some (a, rem))
  end.

Definition program := do _ <- write 0 3; do _ <- write 1 5; do a <- read 0; do b <- read 1; mret (a+b).

Ltac find_match n :=
  match goal with
  | [ |- context [ match n with _ => _ end ] ] => idtac
  end.

Ltac case_nat n :=
  try (find_match n; destruct n as [|n]; simpl; case_nat n).

Definition normally {R:Type} (f:steppable R) (P:R->Prop) : Prop :=
  forall s' n v rem,
  run f empty_storage n = (s', Some (v, rem)) -> P v.

Theorem program_ok : normally program (fun v => v = 8).
Proof.
  unfold normally.
  intros s' n v rem.
  unfold run, program.
  simpl.
  case_nat n; crush.
Qed.

Definition write_pair a x := match x with (v1, v2) => 
  do _ <- write a v1;
  write (S a) v2
  end.
  
Definition read_pair a :=
  do v1 <- read a;
  do v2 <- read (S a);
  mret (v1, v2).

Definition write_two a b :=
  do _ <- write_pair 0 (a, b);
  do _ <- write 2 1;
  mret tt.

Definition read_two :=
  do x <- read_pair 0;
  match x with (a, b) =>
  do c <- read 2;
  mret (if eq_nat_dec c 1 then Some (a, b) else None)
  end.

Ltac flip_equality H :=
  match goal with [ H : ?X = ?Y |- _ ] => let H1 := fresh "H" in rename H into H1; assert (H : Y = X) by (rewrite H1; reflexivity); clear H1 end.
  
Ltac clear_equalities :=
  repeat match goal with
  | [ |- ?X = ?Y -> _ ] => intro
  | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H
  end.

Ltac use_equalities :=
  repeat match goal with
  | [ H : ?X = ?Y |- _ ] => try rewrite H in *
  end.

Theorem pair_ok :
  forall a b,
  forall s n r s' n' r' res,
  (s, r) = run (write_two a b) empty_storage n ->
  (s', Some (res, r')) = run read_two s n' ->
  res = None \/ res = Some (a, b).
Proof.
  intros a b s n r s' n' r' res. 
  simpl.
  case_nat n; case_nat n'; try congruence; clear_equalities; use_equalities; crush.
Qed.
