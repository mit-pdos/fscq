Require Import PermProg PermProgAuto.
Require Import PermSec PermHoare.
Require Import ProofIrrelevance.

Set Implicit Arguments.

(*Ltac inj_existT :=
  match goal with
  | [ H: existT ?P ?p _ = existT ?P ?p _ |- _ ] =>
    apply inj_pair2 in H
  end.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ _ _ _ _ _ _ |- _ ] =>
    inversion H;
    repeat inj_existT;
    subst;
    clear H
  end.

Ltac inv_fail_step :=
  try match goal with
      | [ H: exec _ _ _ _ (Failed _) |- _ ] =>
        inversion H; repeat inj_existT; subst; clear H
      end;
  match goal with
  | [ H: fail_step _ _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

Ltac inv_crash_step :=
  try match goal with
      | [ H: exec _ _ _ _ (Crashed _ _ _) |- _ ] =>
        inversion H; repeat inj_existT; subst; clear H
      end;
  match goal with
  | [ H: crash_step _ |- _ ] =>
    inversion H; subst; clear H
  end.

Ltac inv_exec' H :=
    inversion H;
    repeat inj_existT; subst;
    try inv_step;
    try inv_fail_step;
    try inv_crash_step;
    subst;
    clear H.

Ltac inv_exec :=
  lazymatch goal with
  | [ H: exec _ _ _ (Ret _) _ |- _ ] =>
    inv_exec' H
  | [ H: exec _ _ _ (AlertModified) _ |- _ ] =>
    inv_exec' H
  | [ H: exec _ _ _ (Debug _ _) _ |- _ ] =>
    inv_exec' H
  | [ H: exec _ _ _ (Bind _ _) _ |- _ ] =>
    inv_exec' H
  | [ H: exec _ _ _ _ _ |- _ ] =>
    inv_exec' H
  end.
 *)

Section MonadLaws.

  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall pr tr d bm tr' out,
        exec pr tr d bm p1 out tr' <-> exec pr tr d bm p2 out tr'.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_left_id : forall T T' v (p: T -> prog T'),
      Bind (Ret v) p ~= p v.
  Proof.
    split; intros.
    - inv_exec_perm.
      inv_exec_perm; eauto.
    - repeat econstructor; eauto.
  Qed.

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - repeat inv_exec_perm; eauto;
      repeat econstructor; eauto.
    - repeat inv_exec_perm; eauto.
      repeat econstructor; eauto.
  Qed.

  Theorem security_equivalence:
    forall T pr d bm (p1 p2: prog T),
      permission_secure pr d bm p1 ->
      prog_equiv p2 p1 ->
      permission_secure pr d bm p2.
  Proof.
    unfold permission_secure; intros.
    match goal with
    | [ H: _ ~= _ |- _ ] =>
      edestruct H; eauto
    end.
  Qed.
  
  Theorem corr2_equivalence :
    forall T pr (p p': prog T) pre,
      corr2 pr pre p' ->
      prog_equiv p p' ->
      corr2 pr pre p.
  Proof.
    unfold corr2; intros.
    match goal with
    | [ H: _ ~= _ |- _ ] =>
      edestruct H; eauto
    end.
    edestruct H; eauto.
    intuition.
    eapply security_equivalence; eauto.
  Qed.

End MonadLaws.
Print corr2.
Ltac monad_simpl_one :=
  match goal with
  | [ |- corr2 _ _ (Bind (Bind _ _) _) ] =>
    eapply corr2_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.
