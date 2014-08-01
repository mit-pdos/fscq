Require Import HoareLogicN.

Set Implicit Arguments.

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













