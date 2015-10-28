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

Inductive log_entry :=
| LogEntry (a:addr) (v:valu).

Definition addr_record_type : Rec.type :=
  Rec.RecF [("addr", Rec.WordF addrlen);
             ("padding", Rec.WordF (valulen - addrlen))].

Definition serialize_addr (a:addr) : valu :=
  @Rec.to_word addr_record_type (a, ($0, tt)).

Definition read_addr (v:valu) : addr :=
  Eval compute_rec in
    @Rec.of_word addr_record_type v :-> "addr".

Definition log_write {T} a v rx : prog Mcontents S T :=
  l <- Get LogLength;
  let off := (l+1)*2 in
  Write ($ off) (serialize_addr a);;
  Write ($ (off + 1)) v;;
  rx tt.

Definition log_commit {T} rx : prog Mcontents S T :=
  l <- Get LogLength;
  (* need a For loop... *)