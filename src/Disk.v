Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Load Closures.


Inductive dprog :=
  | DRead  (b:block) (rx:value -> dprog)
  | DWrite (b:block) ( v:value) (rx:dprog)
  | DHalt
  .


Bind Scope dprog_scope with dprog.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : dprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : dprog_scope.

Open Scope dprog_scope.

Record dstate := DSt {
  DSProg: dprog;
  DSDisk: storage
}.

(* An interpreter for the language that implements a log as a disk *)

Fixpoint dexec (p:dprog) (s:dstate) {struct p} : dstate :=
  let (_, dd) := s in
  match p with
  | DHalt         => s
  | DRead b rx    => dexec (rx (st_read dd b)) (DSt (rx (st_read dd b)) dd)
  | DWrite b v rx => dexec rx (DSt rx (st_write dd b v))
  end.

Definition drun (p:dprog) (s:storage) : storage :=
  DSDisk (dexec p (DSt p s)).

Inductive dsmstep : dstate -> dstate -> Prop :=
  | DsmHalt: forall d,
    dsmstep (DSt DHalt d) (DSt DHalt d)
  | DsmRead: forall d b rx,
    dsmstep (DSt (DRead b rx) d)
            (DSt (rx (st_read d b)) d)
  | DsmWrite: forall d b v rx,
    dsmstep (DSt (DWrite b v rx) d)
            (DSt rx (st_write d b v))
  .
