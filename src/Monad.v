Require Import Arith.

Set Implicit Arguments.

(* general storage *)

Definition addr := nat.
Definition state := nat.
Definition storage := addr -> state.

Definition read_storage (st:storage) (a:addr) : state := st a.
Definition write_storage (st:storage) (a:addr) (v:state) : storage :=
  fun (x:addr) =>
    if eq_nat_dec a x then v else st x.

Definition st_init (v:state) : storage :=
  fun (_:addr) => v.

Definition st_write (st:storage) (a:addr) (v:state) : storage :=
  write_storage st a v.

Definition st_read (st:storage) (a:addr) : state := 
  read_storage st a.


(* IO monad *)

Definition IO (R:Set) := storage -> (storage * R).

Definition IOret (R:Set) (r:R) : IO R :=
  fun st => (st, r).

Definition IObind (A B:Set) (a:IO A) (f:A->IO B) : IO B :=
  fun st =>
    let (st', ra) := a st in f ra st'.

Notation "ra <- a ; b" := (IObind a (fun ra => b))
  (right associativity, at level 60).

Notation "a ;; b" := (IObind a (fun _ => b))
  (right associativity, at level 60).


Definition IOinit (v:state) : IO unit :=
  fun st => (st_init v, tt).

Definition IOread (a:addr) : IO state :=
  fun st => (st, st_read st a).

Definition IOwrite (a:addr) (v:state) : IO unit :=
  fun st => (st_write st a v, tt).
