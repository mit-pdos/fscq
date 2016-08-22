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

Section GetModify.

  Theorem wb_get_write_eq : forall wb a a' v,
    a = a' ->
    wb_get (wb_write wb a v) a' = Written v.
  Proof.
    unfold wb_get, wb_write; intros.
    rewrite MapFacts.add_eq_o by auto; auto.
  Qed.

  Theorem wb_get_write_neq : forall wb a a' v,
      a <> a' ->
      wb_get (wb_write wb a v) a' = wb_get wb a'.
  Proof.
    unfold wb_get, wb_write; intros.
    rewrite MapFacts.add_neq_o by auto; auto.
  Qed.

End GetModify.

Hint Rewrite wb_get_write_eq using (now auto) : cache.
Hint Rewrite wb_get_write_neq using (now auto) : cache.

Definition wb_rep (d:Disk) (wb: WriteBuffer) (vd:Disk) :=
  forall a, match wb_get wb a with
       | Written v =>
         vd a = Some v /\
         exists v0, d a = Some v0
       | Missing => vd a = d a
       end.

Section RepTheorems.

  Ltac t :=
    unfold wb_val; intros;
    repeat match goal with
           | [ H: wb_rep _ _ _, a: addr |- _ ] =>
             learn that (H a)
           end;
    destruct matches in *;
    destruct_ands; repeat deex;
    complete_mem_equalities;
    eauto;
    try congruence.

  Theorem wb_rep_same_domain : forall d wb vd,
      wb_rep d wb vd ->
      same_domain d vd.
  Proof.
    unfold same_domain, subset;
      split; t.
  Qed.

  Theorem wb_val_vd : forall d wb vd a v v',
      wb_rep d wb vd ->
      vd a = Some v ->
      wb_val wb a = Some v' ->
      v' = v.
  Proof.
    t.
  Qed.

  Lemma wb_get_val_missing : forall wb a,
      wb_get wb a = WbMissing ->
      wb_val wb a = None.
  Proof.
    unfold wb_val; intros; simpl_match; auto.
  Qed.

 Theorem wb_val_none : forall d wb vd a v,
    wb_rep d wb vd ->
    wb_val wb a = None ->
    vd a = Some v ->
    d a = Some v.
 Proof.
   t.
 Qed.

End RepTheorems.