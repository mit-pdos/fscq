Set Implicit Arguments.
Require Import Storage.
Require Import Disk.

Inductive t2prog :=
  | T2DProg  (d:dprog) (rx:t2prog)
  | T2Commit (rx:t2prog)
  | T2Abort  (rx:t2prog)
  | T2Halt
  .

Record t2state := T2St {
  T2SProg: t2prog;
  T2SDisk: storage;       (* main disk *)
  T2SAltDisk: storage;    (* alternative disk for transactions *)
  T2SInTrans: bool        (* in transaction? the first write starts the transaction *)
}.

Inductive t2smstep : t2state -> t2state -> Prop :=
  | T2smHalt: forall d ad dt,
    t2smstep (T2St T2Halt d ad dt)          (T2St T2Halt d ad dt)
  | T2smProg: forall d ad dt dp rx,
    t2smstep (T2St (T2DProg dp rx) d ad dt) (T2St rx d (drun dp ad) dt)
  | T2smCommit: forall d ad dt rx,
    t2smstep (T2St (T2Commit rx) d ad dt)   (T2St rx ad ad false)
  | T2smAbort: forall d ad dt rx,
    t2smstep (T2St (T2Abort rx) d ad dt)    (T2St rx d d false)
  .
