Require Export PermSec.
Require Import ProofIrrelevance.

Set Implicit Arguments.

  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall pr d bm hm tr' out,
        exec pr d bm hm p1 out tr' <-> exec pr d bm hm p2 out tr'.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - repeat inv_exec_perm; cleanup.
      rewrite List.app_assoc.
      repeat econstructor; eauto.

      split_ors.
      inv_exec_perm; cleanup.
      split_ors; cleanup.
      eapply CrashBind; auto.      
      econstructor; eauto.
      eapply CrashBind; eauto.
      inv_exec_perm.
      rewrite List.app_assoc.
      repeat econstructor; eauto.
    
      split_ors.
      inv_exec_perm; cleanup.
      split_ors; cleanup.      
      econstructor; eauto.
      eapply ExecBind; eauto.  
      repeat econstructor; eauto.
      inv_exec_perm; cleanup.
      rewrite List.app_assoc.
      repeat (eapply ExecBind; eauto).
    
    - repeat inv_exec_perm; cleanup.
      rewrite <- List.app_assoc.
      repeat (eapply ExecBind; eauto).
      
      split_ors.
      repeat econstructor; eauto.
      inv_exec_perm.
      split_ors.
      eapply CrashBind; eauto.
      econstructor; eauto.
      rewrite <- List.app_assoc.
      repeat econstructor; eauto.

      split_ors.
      repeat econstructor; eauto.
      inv_exec_perm.
      split_ors.
      eapply FailBind; eauto.
      econstructor; eauto.
      rewrite <- List.app_assoc.
      repeat econstructor; eauto.
  Qed.

