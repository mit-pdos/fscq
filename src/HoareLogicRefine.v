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
  Definition read xp := $((mem*mem):
    (Call (fun ms : mem*mem => Log.begin_ok xp (fst ms)));;
    x <- (Call (fun ms : mem*mem => Log.read_ok xp 3 ms));
    (Call (fun ms : mem*mem => Log.commit_ok xp (fst ms) (snd ms)));;
    (Halt x)
  ).

  Definition write xp v := $((mem*mem):
    (Call (fun ms : mem*mem => Log.begin_ok xp (fst ms)));;
    (Call (fun ms : mem*mem => Log.write_ok xp 3 v ms));;
    (Call (fun ms : mem*mem => Log.commit_ok xp (fst ms) (snd ms)))
  ).

  Definition rep xp (os: onestate) :=
    match os with
    | One a => exists lm,
      Log.rep xp (NoTransaction lm) /\
      [lm (DataStart xp + 3) = a]
    end%pred.

  Theorem read_ok : forall xp a (ms:mem*mem),
    {{rep xp (One a) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One a)
      /\ [r = Crashed \/ r = Halted a]}}.
  Proof.
    hoare.













