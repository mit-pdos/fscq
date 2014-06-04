Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Parameter state : Set.

Definition crashable (A:Type) := state -> (state * option A).

Definition mret {R:Type} (x:R) : crashable R :=
  fun s => (s, Some x).

Definition mbind {A:Type} {B:Type} (a:crashable A) (f:A->crashable B) : crashable B :=
  fun s =>
     match a s with
     | (s', None) => (s', None)
     | (s', Some av) => f av s'
     end.

Parameter read : nat -> crashable nat.
Parameter write : nat -> nat -> crashable unit.

Notation "a >>= f" := (mbind a f) (left associativity, at level 50).

Notation "'do' x <- y ; z" := (mbind y (fun x => z))
  (left associativity, at level 200, x ident, y at level 100, z at level 200).

Axiom read_write_ok :
  forall (n v:nat),
  forall B,
  forall x: nat -> crashable B,
  (do _ <- write n v; do v' <- read n; x v') = (do _ <- write n v; do v' <- read n; x v).

Axiom read_write_diff_commute :
  forall (n n' v:nat),
  forall B,
  forall x: nat -> crashable B,
  n <> n' ->
  (do _ <- write n v; do v' <- read n'; x v') = (do v' <- read n'; do _ <- write n v; x v').

Axiom read_read_commute :
  forall (n n':nat),
  forall B,
  forall x: nat -> nat -> crashable B,
  (do v <- read n ; do v' <- read n' ; x v v') = (do v' <- read n' ; do v <- read n ; x v v').

Definition normally {R:Type} (c:crashable R) (P:R->Prop) : Prop :=
  forall (s:state),
  match c s with
  | (_, None) => True
  | (_, Some v) => P v
  end.

Theorem simpl :
  normally (do _ <- write 0 3; do _ <- write 1 5; do a <- read 0; do b <- read 1; mret (a+b))
    (fun sum => sum = 8).
Proof.
  rewrite read_read_commute.
  rewrite read_write_ok.
  rewrite read_read_commute.
  rewrite read_write_diff_commute ; [ idtac | crush].
  rewrite read_write_ok.
  unfold normally, mbind, mret; intro.
  repeat ((case (write _ _ _) || case (read _ _)) ; destruct 0; [ idtac | auto ]); auto.
Qed.

(* XXX: above axioms don't work well with crashes; perhaps instead the following read-backwards axioms *)

Axiom read_write_ok2 : 
  forall n v v' s s' s'',
  write n v s = (s', Some tt) ->
  read n s' = (s'', Some v') ->
  v = v'.

(* even a read that crashes does not influence any other reads: *)
Axiom read_read_commute2 :
  forall n n' r v' s s' s'',
  read n s = (s', r) ->
  read n' s' = (s'', Some v') ->
  exists s''', read n' s = (s''', Some v').

(* even a write that crashes does not influence any other reads: *)
Axiom read_write_diff_commute2 :
  forall n n' v v' r s s' s'',
  n <> n' ->
  write n v s = (s', r) ->
  read n' s' = (s'', Some v') ->
  exists s''', read n' s = (s''', Some v').
