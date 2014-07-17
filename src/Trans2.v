Set Implicit Arguments.
Require Import Storage.
Require Import Disk.

Inductive t2prog :=
  | T2Begin  (rx:t2prog)
  | T2DProg  (d:dprog) (rx:t2prog)
  | T2Commit (rx:t2prog)
  | T2Abort  (rx:t2prog)
  | T2Halt.

Record t2state_persist := T2PSt {
  T2PSDisk: storage (* main disk *)
}.

Record t2state_ephem := T2ESt {
  T2ESProg: t2prog;
  T2ESAltDisk: option storage (* alternative disk for transactions, if in txn *)
}.

Record t2state := T2St {
  T2SPersist: t2state_persist;
  T2SEphem: t2state_ephem
}.

Inductive t2step : t2state -> t2state -> Prop :=
  | T2smBegin: forall d rx,
    t2step (T2St (T2PSt d) (T2ESt (T2Begin rx) None))
           (T2St (T2PSt d) (T2ESt rx (Some d)))
  | T2smProg: forall d ad dp rx,
    t2step (T2St (T2PSt d) (T2ESt (T2DProg dp rx) (Some ad)))
           (T2St (T2PSt d) (T2ESt rx (Some (drun dp ad))))
  | T2smCommit: forall d ad rx,
    t2step (T2St (T2PSt d) (T2ESt (T2Commit rx) (Some ad)))
           (T2St (T2PSt ad) (T2ESt rx None))
  | T2smAbort: forall d ad rx,
    t2step (T2St (T2PSt d) (T2ESt (T2Abort rx) (Some ad)))
           (T2St (T2PSt d) (T2ESt rx None)).
