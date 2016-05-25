Require Import CoopConcur.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Automation.
Require Import DiskReaders.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Section WriteBuffer.

  Implicit Type a:addr.

  Inductive wb_entry : Type :=
  | Written (v:valu)
  | WbMissing (* never stored in buffer - represents completely missing entries *).

  Definition WriteBuffer : Type := Map.t wb_entry.

  Definition emptyWriteBuffer : WriteBuffer :=
    Map.empty wb_entry.

  Variable (wb:WriteBuffer).

  Definition wb_get a : wb_entry :=
    match Map.find a wb with
    | Some ce => ce
    | None => WbMissing
    end.

  Definition wb_write a v :=
    Map.add a (Written v) wb.

  Definition wb_val a : option valu :=
    match wb_get a with
    | Written v => Some v
    | _ => None
    end.

  Definition wb_entries : list (addr * wb_entry) :=
    Map.elements wb.

End WriteBuffer.

Definition wb_rep (d:DISK) (wb: WriteBuffer) (vd:Disk) :=
  forall a, match wb_get wb a with
       | Written v => exists rdr,
                     vd a = Some v /\
                     d a = Some (v, rdr)
       | Missing =>
         match d a with
         | None => vd a = None
         | Some (v, rdr) => vd a = Some v
         end
       end.

Ltac t :=
  repeat match goal with
         | [ H: wb_rep _ _ _, a: addr |- _ ] =>
           learn that (H a)
         end;
  destruct matches in *;
  repeat deex; destruct_ands.

Theorem wb_rep_same_domain : forall d wb vd,
    wb_rep d wb vd ->
    same_domain (hide_readers d) vd.
Proof.
  unfold hide_readers, same_domain, subset;
    split; intros;
    t; (eauto || congruence).
Qed.

Hint Opaque wb_rep.
