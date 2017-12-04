Require Export PermSec.
Require Import ProofIrrelevance.

Set Implicit Arguments.

  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall pr tr d bm hm tr' out,
        exec pr tr d bm hm p1 out tr' <-> exec pr tr d bm hm p2 out tr'.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    inv_exec_perm.
    {
      inv_exec_perm.
      repeat econstructor; eauto.
    }
    split_ors.
    {
      inv_exec_perm; cleanup.
      split_ors; cleanup.
      eapply CrashBind; auto.
      
      econstructor; eauto.
      eapply CrashBind; eauto.
    }
    
    {
      inv_exec_perm.
      repeat econstructor; eauto.
    }
  
    inv_exec_perm.
    {
      inv_exec_perm.
      repeat econstructor; eauto.
    }
    {
      split_ors.
      repeat eapply CrashBind; eauto.
      inv_exec_perm.
      split_ors.
      eapply CrashBind;
      econstructor; eauto.
      repeat econstructor; eauto.
    }
  Qed.

  Theorem security_equivalence:
    forall T pr d bm hm (p1 p2: prog T),
      permission_secure pr d bm hm p1 ->
      prog_equiv p2 p1 ->
      permission_secure pr d bm hm p2.
  Proof.
    unfold permission_secure; intros.
    match goal with
    | [ H: _ ~= _ |- _ ] =>
      edestruct H; eauto
    end.
  Qed.
