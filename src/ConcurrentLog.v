Require Import ConcurrentCache.
Require Import EventCSL.
Require Import EventCSLauto.
Require Import Word.
Require Import Hlist.
Import List.ListNotations.
Require Import Rec.

Definition Mcontents : list Set := [nat].
Definition S : Set := True.

Definition LogLength : var Mcontents nat := HFirst.

(* we will store the log length in commit_sector *)
Definition commit_sector : addr := $10.

Record log_entry := { log_addr : addr;
                      log_valu : valu }.

Definition addr_record_type : Rec.type :=
  Rec.RecF [("addr", Rec.WordF addrlen);
             ("padding", Rec.WordF (valulen - addrlen))].

Definition serialize_addr (a:addr) : valu :=
  @Rec.to_word addr_record_type (a, ($0, tt)).

Definition read_addr (v:valu) : addr :=
  Eval compute_rec in
    @Rec.of_word addr_record_type v :-> "addr".

Definition log_append {T} a v rx : prog Mcontents S T :=
  l <- Get LogLength;
  let off := (l+1)*2 in
  Write ($ off) (serialize_addr a);;
  Write ($ (off + 1)) v;;
  rx tt.

Definition read_entry {T} n rx : prog Mcontents S T :=
  av <- Read ($ (n * 2));
  v <- Read ($ (n * 2 + 1));
  rx (Build_log_entry (read_addr av) v).

Definition write_entry {T} e rx : prog Mcontents S T :=
  Write (log_addr e) (log_valu e);; rx tt.

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

Definition log_sync {T} rx : prog Mcontents S T :=
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

Definition log_commit {T} rx : prog Mcontents S T :=
  Write commit_sector $0;;
        Sync commit_sector;;
        rx tt.
