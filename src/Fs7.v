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

Ltac case_nat n  :=
  try (find_match n; destruct n as [|n]; case_nat n).  

Definition normally {R:Type} (f:steppable R) (P:R->Prop) : Prop :=
  forall s s' n v rem,
  run f s n = (s', Some (v, rem)) -> P v.
  
Theorem program_ok : normally program (fun v => v = 8).
Proof.
  unfold normally.
  intros s s' n v rem.
  unfold run, program.
  simpl.
  case_nat n; crush.
Qed.