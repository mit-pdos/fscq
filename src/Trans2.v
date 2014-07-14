Set Implicit Arguments.
Require Import Storage.
Require Import Disk.

Inductive t2prog :=
  | T2Begin  (rx:t2prog)
  | T2DProg  (d:dprog) (rx:t2prog)
  | T2Commit (rx:t2prog)
  | T2Abort  (rx:t2prog)
  | T2Halt.

Record t2state := T2St {
  T2SProg: t2prog;
  T2SDisk: storage;           (* main disk *)
  T2SAltDisk: option storage  (* alternative disk for transactions, if in txn *)
}.

Inductive t2step : t2state -> t2state -> Prop :=
  | T2smHalt: forall d oad,
    t2step (T2St T2Halt d oad)                (T2St T2Halt d oad)
  | T2smBegin: forall d rx,
    t2step (T2St (T2Begin rx) d None)         (T2St rx d (Some d))
  | T2smProg: forall d ad dp rx,
    t2step (T2St (T2DProg dp rx) d (Some ad)) (T2St rx d (Some (drun dp ad)))
  | T2smCommit: forall d ad rx,
    t2step (T2St (T2Commit rx) d (Some ad))   (T2St rx ad None)
  | T2smAbort: forall d ad rx,
    t2step (T2St (T2Abort rx) d (Some ad))    (T2St rx d None).
