Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Util.
Require Import Recdef.

Inductive dprog :=
  | DRead  (b:block) (rx:value -> dprog)
  | DWrite (b:block) ( v:value) (rx:dprog)
  | DHalt.

Record dstate := DSt {
  DSProg: dprog;
  DSDisk: storage
}.

Inductive dstep : dstate -> dstate -> Prop :=
  | DsmRead: forall d b rx,
    dstep (DSt (DRead b rx) d)
            (DSt (rx (st_read d b)) d)
  | DsmWrite: forall d b v rx,
    dstep (DSt (DWrite b v rx) d)
            (DSt rx (st_write d b v)).

Hint Constructors dstep.


Theorem opp_dstep_wf:
  well_founded (opposite_rel dstep).
Proof.
  unfold well_founded; destruct a; generalize_type storage.
  induction DSProg0; constructor; intros; invert_rel (opposite_rel dstep);
  destruct_type dstate; crush.
Qed.

Function dexec (s:dstate) {wf (opposite_rel dstep) s} : dstate :=
  let (p, dd) := s in
  match p with
  | DHalt         => s
  | DRead b rx    => dexec (DSt (rx (st_read dd b)) dd)
  | DWrite b v rx => dexec (DSt rx (st_write dd b v))
  end.
Proof.
  - constructor.
  - constructor.
  - apply opp_dstep_wf.
Qed.

Fixpoint drun (p:dprog) (dd:storage) : storage :=
  match p with
  | DHalt         => dd
  | DRead b rx    => drun (rx (st_read dd b)) dd
  | DWrite b v rx => drun rx (st_write dd b v)
  end.



(* some helpful notation *)
Bind Scope dprog_scope with dprog.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : dprog_scope.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : dprog_scope.
