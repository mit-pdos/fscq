Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Parameter storage : Set.
Parameter st_write : storage -> nat -> nat -> storage.
Parameter st_read : storage -> nat -> nat.

Axiom disk_read_same:
  forall s a v,
  st_read (st_write s a v) a = v.

Axiom disk_read_other:
  forall s a a' v,
  st_read (st_write s a' v) a = st_read s a.


Parameter crashstate : Set.
Parameter should_crash : crashstate -> bool.
Parameter next_crash : crashstate -> crashstate.

Record state : Set := mkstate {
  state_storage : storage;
  state_crash : crashstate
}.

Definition crashable (A:Type) := state -> (state * option A).

Definition mret {R:Type} (x:R) : crashable R :=
  fun s => (s, Some x).

Definition mbind {A:Type} {B:Type} (a:crashable A) (f:A->crashable B) : crashable B :=
  fun s =>
     match a s with
     | (s', None) => (s', None)
     | (s', Some av) => f av s'
     end.

Definition read (addr: nat) : crashable nat :=
  fun (s: state) =>
    let ncrash := next_crash (state_crash s) in
    match should_crash (state_crash s) with
    | true => ((mkstate (state_storage s) ncrash), None)
    | false => ((mkstate (state_storage s) ncrash), Some (st_read (state_storage s) addr))
    end.

Definition write (addr: nat) (data: nat) : crashable unit :=
  fun (s: state) =>
    let ncrash := next_crash (state_crash s) in
    match should_crash (state_crash s) with
    | true => ((mkstate (state_storage s) ncrash), None)
    | false => ((mkstate (st_write (state_storage s) addr data) ncrash), Some tt)
    end.

Notation "a >>= f" := (mbind a f) (left associativity, at level 50).

Notation "'do' x <- y ; z" := (mbind y (fun x => z))
  (left associativity, at level 200, x ident, y at level 100, z at level 200).

(*

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
*)

Definition normally {R:Type} (c:crashable R) (P:R->Prop) : Prop :=
  forall (s:state),
  match c s with
  | (_, None) => True
  | (_, Some v) => P v
  end.

(*
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
*)

(* XXX: above axioms don't work well with crashes; perhaps instead the following read-backwards axioms *)

Axiom read_write_ok :
  forall n v v' r s s' s'',
  write n v s = (s', Some r) ->
  read n s' = (s'', Some v') ->
  v = v'.

(* even a read that crashes does not influence any other reads: *)
Axiom read_read_commute :
  forall n n' r v' s s' s'',
  read n s = (s', r) ->
  read n' s' = (s'', Some v') ->
  exists s''', read n' s = (s''', Some v').

(* even a write that crashes does not influence any other reads: *)
Axiom read_write_diff_commute :
  forall n n' v v' r s s' s'',
  n <> n' ->
  write n v s = (s', r) ->
  read n' s' = (s'', Some v') ->
  exists s''', read n' s = (s''', Some v').

(* XXX todo change Axioms to Lemmas, proved based on st_read/st_write axioms *)

Theorem simpl :
  normally (do _ <- write 0 3; do _ <- write 1 5; do a <- read 0; do b <- read 1; mret (a+b))
    (fun sum => sum = 8).
Proof.
  unfold normally, mbind, mret; intro.
  case_eq (write 0 3 s); intros; destruct o; [ idtac | auto ].
  case_eq (write 1 5 s0); intros; destruct o; [ idtac | auto ].
  case_eq (read 0 s1); intros; destruct o; [ idtac | auto ].
  case_eq (read 1 s2); intros; destruct o; [ idtac | auto ].

  assert (exists s', read 1 s1 = (s', Some n0)).
  apply read_read_commute with (n:=0) (r:=Some n) (s':=s2) (s'':=s3); assumption.
  crush.
  assert (5 = n0).
  apply read_write_ok with (n := 1) (s := s0) (s' := s1) (s'' := x) (r := u0); assumption.
  crush.

  assert (exists s', read 0 s0 = (s', Some n)).
  apply read_write_diff_commute with (n:=1) (v:=5) (r:=Some u0) (s':=s1) (s'':=s2); crush.
  crush.
  assert (3 = n).
  apply read_write_ok with (n := 0) (s := s) (s' := s0) (s'' := x0) (r := u); assumption.
  crush.
Qed.