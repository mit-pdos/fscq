Require Import ConcurrentCache.
Require Import EventCSL.
Require Import EventCSLauto.
Require Import Word.
Import List.ListNotations.
Require Import Rec.

Record entry := { log_addr : addr;
                      log_valu : valu }.

Definition addr1_loc : addr := $0.
Definition valu1_loc : addr := $1.
Definition addr2_loc : addr := $2.
Definition valu2_loc : addr := $3.
Definition commit_sector : addr := $4.

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

Inductive log_entries :=
| Empty
| OneEntry (e: entry)
| TwoEntries (e1: entry) (e2: entry).

Implicit Type (entries : log_entries).

Definition entries_length entries :=
  match entries with
  | Empty => 0
  | OneEntry _ => 1
  | TwoEntries _ _ => 2
  end.

Definition log_entries_unsynced entries : DISK_PRED :=
  match entries with
  | Empty => emp
  | OneEntry e =>
    let a := serialize_addr (log_addr e) in
    let v := log_valu e in
    (exists arest vrest, addr1_loc |-> Valuset a arest *
                    valu1_loc |-> Valuset v vrest)%pred
  | TwoEntries e1 e2 =>
    let a1 := serialize_addr (log_addr e1) in
    let a2 := serialize_addr (log_addr e2) in
    let v1 := log_valu e1 in
    let v2 := log_valu e2 in
    (exists arest1 vrest1 arest2 vrest2, addr1_loc |-> Valuset a1 arest1 *
                                    valu1_loc |-> Valuset v1 vrest1 *
                                    addr2_loc |-> Valuset a2 arest2 *
                                    valu2_loc |-> Valuset v2 vrest2)%pred
  end.

Definition log_entries_synced entries : DISK_PRED :=
  match entries with
  | Empty => emp
  | OneEntry e =>
    let a := serialize_addr (log_addr e) in
    let v := log_valu e in
    (addr1_loc |-> Valuset a nil *
     valu1_loc |-> Valuset v nil)%pred
  | TwoEntries e1 e2 =>
    let a1 := serialize_addr (log_addr e1) in
    let a2 := serialize_addr (log_addr e2) in
    let v1 := log_valu e1 in
    let v2 := log_valu e2 in
    (addr1_loc |-> Valuset a1 nil *
     valu1_loc |-> Valuset v1 nil *
     addr2_loc |-> Valuset a2 nil *
     valu2_loc |-> Valuset v2 nil)%pred
  end.

Definition log_entries_disk_pred (p: entry -> pred) entries : DISK_PRED :=
  match entries with
  | Empty => emp
  | OneEntry e => p e
  | TwoEntries e1 e2 => p e1 * p e2
  end.

Definition log_entries_disk_unwritten entries :=
  log_entries_disk_pred
    (fun e =>
       let '{| log_addr := a; log_valu := _ |} := e in
       a |->?)%pred entries.

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

Fixpoint remaining_entries entries : DISK_PRED :=
  match entries with
  | Empty => (exists a1 v1 a2 v2,
                 addr1_loc |-> a1 *
                 valu1_loc |-> v1 *
                 addr2_loc |-> a2 *
                 valu2_loc |-> v2)%pred
  | OneEntry _ => (exists a2 v2,
                      addr2_loc |-> a2 *
                      valu2_loc |-> v2)%pred
  | TwoEntries _ _ => emp
  end.

Definition log_rep st entries : DISK_PRED :=
  match st with
  | Committed => remaining_entries entries *
                 [[ entries = Empty ]]
  | ActiveTxn => log_entries_unsynced entries *
                 remaining_entries entries *
                 log_entries_disk_unwritten entries
  | TxnSynced => log_entries_synced entries *
                 remaining_entries entries *
                 log_entries_disk_unwritten entries
  | WrittenUnsynced => log_entries_synced entries *
                       remaining_entries entries *
                       log_entries_disk_unsynced entries
  | Synced => log_entries_synced entries *
              remaining_entries entries *
              log_entries_disk_synced entries
  end.

Definition Mcontents : list Set := [nat].
Definition LogLength : var Mcontents _ := HFirst.

Definition Scontents : list Set := [log_entries; log_state].
Definition S := hlist (fun T:Set => T) Scontents.

Definition GLogEntries : var Scontents _ := HFirst.
Definition LogState : var Scontents _ := HNext HFirst.

Definition log_inv : Invariant Mcontents S :=
  Eval cbn zeta in (* fold let bindings *)
  fun m s d =>
    let entries := get GLogEntries s in
    let st := get LogState s in
    get LogLength m = entries_length entries /\
    (d |= log_rep st entries)%judgement.

Definition log_relation : ID -> Relation S :=
  fun tid s s' => True.

(* TODO: build these out of shared code in Locking *)
Definition lockR : ID -> Relation S :=
  fun tid s s' => True.

Definition lockI : Invariant Mcontents S :=
  fun m s d => True.

Definition logS : transitions Mcontents S :=
  Build_transitions log_relation lockR log_inv lockI.

Definition log_append {T} a v rx : prog Mcontents S T :=
  l <- Get LogLength;
  let off := l*2 in
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
  match l with
  | 0 => rx tt
  | 1 => Sync addr1_loc;;
              Sync valu1_loc;;
              Write commit_sector ($ l);;
              Sync commit_sector;;
              rx tt
  | 2 => Sync addr1_loc;;
              Sync valu1_loc;;
              Sync addr2_loc;;
              Sync valu2_loc;;
              Write commit_sector ($ l);;
              Sync commit_sector;;
              rx tt
  | _ => rx tt
  end.

Definition log_write {T} rx : prog Mcontents S T :=
  l <- Get LogLength;
  match l with
  | 0 => rx tt
  | 1 => e <- read_entry 0;
      write_entry e;;
                  rx tt
  | 2 => e1 <- read_entry 0;
      write_entry e1;;
                  e2 <- read_entry 1;
      write_entry e2;;
                  rx tt
  | _ => rx tt
  end.

Definition log_data_sync {T} rx : prog Mcontents S T :=
  l <- Get LogLength;
  match l with
  | 0 => rx tt
  | 1 => e <- read_entry 0;
      Sync (log_addr e);;
           rx tt
  | 2 => e1 <- read_entry 0;
      Sync (log_addr e1);;
           e2 <- read_entry 1;
      Sync (log_addr e2);;
           rx tt
  | _ => rx tt
  end.

Definition log_finish_commit {T} rx : prog Mcontents S T :=
  Write commit_sector $0;;
        Sync commit_sector;;
        rx tt.