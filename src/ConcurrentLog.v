Require Import ConcurrentCache.
Require Import EventCSL.
Require Import EventCSLauto.
Require Import Word.
Require Import Hlist.
Import List.ListNotations.
Require Import Rec.

Record entry := { log_addr : addr;
                      log_valu : valu }.

(* we will store the log length in commit_sector *)
Definition max_entries := 5.
Definition commit_sector : addr := $ (max_entries * 2).

Hint Opaque max_entries.

Definition addr_record_type : Rec.type :=
  Rec.RecF [("addr", Rec.WordF addrlen);
             ("padding", Rec.WordF (valulen - addrlen))].

Definition serialize_addr (a:addr) : valu :=
  @Rec.to_word addr_record_type (a, ($0, tt)).

Definition read_addr (v:valu) : addr :=
  Eval compute_rec in
    @Rec.of_word addr_record_type v :-> "addr".

Inductive log_state :=
| Committed
| ActiveTxn
| TxnSynced
| WrittenUnsynced
| Synced.

Implicit Type (entries : list entry).

Fixpoint log_entries_unsynced entries k : DISK_PRED :=
  match entries with
  | nil => emp
  | {| log_addr := a; log_valu := v |} :: entries' =>
    let a := serialize_addr a in
    let addr_loc := $ (k * 2) in
    let valu_loc := $ (k * 2 + 1) in
    ((exists arest vrest, addr_loc |-> Valuset a arest * valu_loc |-> Valuset v vrest) *
     log_entries_unsynced entries' (k+1))%pred
  end.

Fixpoint log_entries_synced entries k : DISK_PRED :=
  match entries with
  | nil => emp
  | {| log_addr := a; log_valu := v |} :: entries' =>
    let a := serialize_addr a in
    let addr_loc := $ (k * 2) in
    let valu_loc := $ (k * 2 + 1) in
    (addr_loc |-> Valuset a nil * valu_loc |-> Valuset v nil *
     log_entries_synced entries' (k+1))%pred
  end.

Fixpoint log_entries_disk_pred (p: entry -> pred) entries : DISK_PRED :=
  match entries with
  | nil => emp
  | e :: entries' =>
    p e * log_entries_disk_pred p entries'
  end.

Definition log_entries_disk_unwritten :=
  log_entries_disk_pred
    (fun e =>
       let '{| log_addr := a; log_valu := _ |} := e in
       a |->?)%pred.

Definition log_entries_disk_unsynced :=
  log_entries_disk_pred
    (fun e =>
       let '{| log_addr := a; log_valu := v |} := e in
       exists rest, a |-> Valuset v rest)%pred.

Definition log_entries_disk_synced :=
  log_entries_disk_pred
    (fun e =>
       let '{| log_addr := a; log_valu := v |} := e in
       a |-> Valuset v nil)%pred.

Fixpoint remaining_entries n : DISK_PRED :=
  match n with
  | 0 => emp
  | Datatypes.S n' => let start_index := (max_entries - n) * 2 in
                      ($ start_index) |->? * ($ (start_index+1)) |->? *
                      remaining_entries n'
  end.

Definition log_rep st entries : DISK_PRED :=
  match st with
  | Committed => remaining_entries max_entries *
                 [[ entries = nil ]]
  | ActiveTxn => log_entries_unsynced entries 0 *
                 remaining_entries (max_entries - length entries) *
                 log_entries_disk_unwritten entries
  | TxnSynced => log_entries_synced entries 0 *
                 remaining_entries (max_entries - length entries) *
                 log_entries_disk_unwritten entries
  | WrittenUnsynced => log_entries_synced entries 0 *
                       remaining_entries (max_entries - length entries) *
                       log_entries_disk_unsynced entries
  | Synced => log_entries_synced entries 0 *
              remaining_entries (max_entries - length entries) *
              log_entries_disk_synced entries
  end.

Definition Mcontents : list Set := [nat].
Definition LogLength : var Mcontents _ := HFirst.

Definition Scontents : list Set := [list entry; log_state].
Definition S := hlist (fun T:Set => T) Scontents.

Definition GLogEntries : var Scontents _ := HFirst.
Definition LogState : var Scontents _ := HNext HFirst.

Definition log_inv : Invariant Mcontents S :=
  Eval cbn zeta in (* fold let bindings *)
  fun m s d =>
    let entries := get GLogEntries s in
    let st := get LogState s in
    get LogLength m = length entries /\
    (d |= log_rep st entries)%judgement.

Definition log_relation : ID -> Relation S :=
  fun tid s s' => True.

(* TODO: build these out of combinators in a common locking module *)
Definition lockR : ID -> Relation S :=
  fun tid s s' => True.

Definition lockI : Invariant Mcontents S :=
  fun m s d => True.

Definition logS : transitions Mcontents S :=
  Build_transitions log_relation lockR log_inv lockI.

Definition log_append {T} a v rx : prog Mcontents S T :=
  l <- Get LogLength;
  let off := (l+1)*2 in
  Write ($ off) (serialize_addr a);;
        Write ($ (off + 1)) v;;
        Assgn LogLength (l+1);;
  rx tt.

Definition read_entry {T} n rx : prog Mcontents S T :=
  av <- Read ($ (n * 2));
  v <- Read ($ (n * 2 + 1));
  rx (Build_entry (read_addr av) v).

Definition write_entry {T} e rx : prog Mcontents S T :=
  Write (log_addr e) (log_valu e);; rx tt.

Definition log_sync {T} rx : prog Mcontents S T :=
  l <- Get LogLength;
  _ <- For i < l
| Ghost [ (_:unit) ]
| Loopvar [ (_:unit) ]
| Continuation lrx
| LoopInv (fun d m s0 s => True)
| OnCrash (fun d => True)
| Begin
    Sync ($ (i * 2));;
    Sync ($ (i * 2 + 1));;
    lrx (tt, tt)
| Rof (tt, tt);
  Write commit_sector ($ l);;
        Sync commit_sector;;
        rx tt.

Definition log_write {T} rx : prog Mcontents S T :=
  l <- Get LogLength;
  _ <- For i < l
| Ghost [ (_:unit) ]
| Loopvar [ (_:unit) ]
| Continuation lrx
| LoopInv (fun d m s0 s => True)
| OnCrash (fun d => True)
| Begin
    e <- read_entry i;
  write_entry e;;
              lrx (tt, tt)

| Rof (tt, tt);
  rx tt.

Definition log_data_sync {T} rx : prog Mcontents S T :=
  l <- Get LogLength;
  _ <- For i < l
| Ghost [ (_:unit) ]
| Loopvar [ (_:unit) ]
| Continuation lrx
| LoopInv (fun d m s0 s => True)
| OnCrash (fun d => True)
| Begin
    e <- read_entry i;
  Sync (log_addr e);;
       lrx (tt, tt)
| Rof (tt, tt);
  rx tt.

Definition log_finish_commit {T} rx : prog Mcontents S T :=
  Write commit_sector $0;;
        Sync commit_sector;;
        rx tt.
