Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Arith.

Set Implicit Arguments.


(* Testing.. *)

Definition do_two_writes a1 a2 v1 v2 rx :=
  Write a1 v1 ;; Write a2 v2 ;; rx tt.

Example two_writes: forall a1 a2 v1 v2 rx rec,
  {{ exists v1' v2' F,
     a1 |-> v1' * a2 |-> v2' * F
   * [[{{ a1 |-> v1 * a2 |-> v2 * F }} rx tt >> rec]]
   * [[{{ (a1 |-> v1' * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec]]
  }} do_two_writes a1 a2 v1 v2 rx >> rec.
Proof.
  unfold do_two_writes.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq (do_two_writes _ _ _ _) _ >> _) => apply two_writes : prog.

Example read_write: forall a v rx rec,
  {{ exists v' F,
     a |-> v' * F
   * [[{{ a |-> v * F }} (rx v) >> rec]]
   * [[{{ (a |-> v' * F)
       \/ (a |-> v * F) }} rec >> rec]]
  }} Write a v ;; x <- Read a ; rx x >> rec.
Proof.
  hoare.
Qed.

Example four_writes: forall a1 a2 v1 v2 rx rec,
  {{ exists v1' v2' F,
     a1 |-> v1' * a2 |-> v2' * F
   * [[{{ a1 |-> v1 * a2 |-> v2 * F }} rx >> rec]]
   * [[{{ (a1 |-> v1' * a2 |-> v2' * F)
       \/ (a1 |-> v1 * a2 |-> v2' * F)
       \/ (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec]]
  }} do_two_writes a1 a2 v1 v2 ;; do_two_writes a1 a2 v1 v2 ;; rx >> rec.
Proof.
  hoare.
Qed.

Example inc_up_to_5: forall a rx rec,
  {{ exists v F,
     a |-> v * F
   * [[{{ [[v < 5]] * a |-> (S v) * F
       \/ [[v >= 5]] * a |-> v * F }} rx >> rec]]
   * [[{{ a |-> v * F
       \/ a |-> S v * F }} rec >> rec]]
  }} x <- !a;
  If (lt_dec x 5) {
    a <-- (S x) ;; rx
  } else {
    rx
  } >> rec.
Proof.
  hoare.
Qed.

Example count_up: forall (n:nat) rx rec F,
  {{ F
   * [[ {{ F }} (rx n) >> rec ]]
   * [[ {{ F }} rec >> rec ]]
  }} r <- For i < n
     Loopvar l <- 0
     Continuation lrx
     Invariant
       F * [[ l=i ]]
         * [[ {{ F }} rx n >> rec ]]
         * [[ {{ F }} rec >> rec ]]
     OnCrash
       any
     Begin
       lrx (S l)
     Rof; rx r
  >> rec.
Proof.
  hoare.
Qed.


Require Import Log.

Inductive onestate :=
| One (a: nat).

Module Type ONEINT.
  (* Methods *)
  Parameter read : xparams -> prog nat.
  Parameter write : xparams -> nat -> prog unit.

  Parameter rep : xparams -> onestate -> pred.

  Axiom read_ok : forall xp v,
    {{rep xp (One v) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One v)
      /\ [r = Crashed \/ r = Halted v]}}.

  Axiom write_ok : forall xp v0 v,
    {{rep xp (One v0) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (write xp v)
    {{r, rep xp (One v)
      \/ ([r = Crashed] /\ rep xp (One v0))}}.
End ONEINT.

Module Oneint : ONEINT.
  Definition read xp := $(mem:
    (Call (fun m : mem => Log.begin_ok xp m));;
    x <- (Call (fun m : mem => Log.read_ok xp 3 (m, m)));
    (Call (fun m : mem => Log.commit_ok xp m m));;
    (Halt x)
  ).

  Definition write xp v := $(mem:
    (Call (fun m : mem => Log.begin_ok xp m));;
    (Call (fun m : mem => Log.write_ok xp 3 v (m, upd m 3 v)));;
    (Call (fun m : mem => Log.commit_ok xp m (upd m 3 v)))
  ).

  Definition rep xp (os: onestate) :=
    match os with
    | One a => exists lm,
      Log.rep xp (NoTransaction lm) /\
      [lm (DataStart xp + 3) = a]
    end%pred.

  Theorem read_ok : forall xp a (m:mem),
    {{rep xp (One a) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One a)
      /\ [r = Crashed \/ r = Halted a]}}.
  Proof.
    hoare.













