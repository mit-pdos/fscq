Require Import MemCache.
Require Import AsyncDisk.
Require Import List.
Require Import Automation.

Section WriteBuffer.

  Inductive wb_entry :=
  | Written (v:valu)
  | WbMissing (* never stored in write buffer, used to represent missing entries *).

  Definition WriteBuffer:Type := Map.t valu.

  Definition empty_writebuffer := Map.empty valu.

  Implicit Types (wb:WriteBuffer) (a:addr).

  Definition wb_get wb a : wb_entry :=
    match Map.find a wb with
    | Some v => Written v
    | None => WbMissing
    end.

  Definition wb_add wb a v : WriteBuffer :=
    Map.add a v wb.

  Theorem wb_get_add_eq : forall wb a v,
      wb_get (wb_add wb a v) a = Written v.
  Proof.
    unfold wb_get, wb_add; intros.
    rewrite MapFacts.add_eq_o; auto.
  Qed.

  Theorem wb_get_add_neq : forall wb a a' v,
      a <> a' ->
      wb_get (wb_add wb a v) a' = wb_get wb a'.
  Proof.
    unfold wb_get, wb_add; intros.
    rewrite MapFacts.add_neq_o by auto; auto.
  Qed.

  Definition wb_writes wb : list (addr * valu) :=
    Map.elements wb.

  Theorem wb_get_writes : forall wb a v,
      wb_get wb a = Written v <->
      In (a,v) (wb_writes wb).
  Proof.
    unfold wb_get, wb_writes.
    split; intros.
    - case_eq (Map.find (elt:=valu) a wb); intros;
        simpl_match; try congruence.
      inversion H; subst.
      pose proof (MapFacts.elements_mapsto_iff wb a v).
      apply MapFacts.find_mapsto_iff in H0; intuition.
      apply SetoidList.InA_alt in H1; deex.
      destruct y; cbn in *.
      compute in *; intuition subst; auto.
    - pose proof (MapFacts.elements_mapsto_iff wb a v); intuition.
      clear H1.
      match type of H2 with
      | ?P -> _ => assert P
      end.
      apply SetoidList.In_InA; auto with typeclass_instances.
      intuition.
      apply Map.find_1 in H1; simpl_match; auto.
  Qed.

  Theorem wb_writes_nodup_addr : forall wb,
      NoDup (map fst (wb_writes wb)).
  Proof.
    unfold wb_writes; intros.

    pose proof (Map.elements_3w wb).
    generalize dependent (Map.elements wb).
    induction l; simpl; intros.
    constructor.

    inversion H; subst; eauto.
    econstructor; eauto.
    contradict H2.
    clear IHl H H3.
    induction l; simpl in *; intuition auto.
    destruct a, a0; simpl in *; subst.
    constructor.
    reflexivity.
  Qed.

End WriteBuffer.

Hint Rewrite wb_get_add_eq : cache.
Hint Rewrite wb_get_add_neq using (solve [ auto ]) : cache.
