Require Import CCLProg.
Require Import Eqdep.
Require Import Mem Pred.
Require Import AsyncDisk.
Require Import Word.
Require Import FunctionalExtensionality.

Section Primitives.

  Variable St:StateTypes.
  Variable G: TID -> Sigma St -> Sigma St -> Prop.

  Theorem cprog_ok_weaken : forall T tid (pre pre': _ -> _ -> Prop) (p: cprog T),
      cprog_ok G tid pre p ->
      (forall st donecond, pre' st donecond -> pre st donecond) ->
      cprog_ok G tid pre' p.
  Proof.
    intros.
    unfold cprog_ok; intros.
    apply H0 in H1.
    eapply H; eauto.
  Qed.

  Definition exec_equiv T (p p': cprog T) :=
    forall tid st out, exec G tid st p out <-> exec G tid st p' out.

  Hint Constructors exec.

  Ltac inj_pair2 :=
    match goal with
    | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
      apply inj_pair2 in H; subst
    end.

  Ltac inv_bind :=
    match goal with
    | [ H: exec _ _ _ (Bind _ _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ _ _ _ |- _ ] =>
            solve [ inversion H ]
          | [ H: fail_step _ _ |- _ ] =>
            solve [ inversion H ]
          end;
      clear H
    end.

  Ltac inv_ret :=
    match goal with
    | [ H: exec _ _ _ (Ret _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ (Ret _) _ _ |- _ ] =>
            solve [ inversion H ]
          | [ H: fail_step _ (Ret _) |- _ ] =>
            solve [ inversion H ]
          end;
      clear H
    end.

  Theorem monad_right_id : forall T (p: cprog T),
      exec_equiv (Bind p Ret) p.
  Proof.
    split; intros.
    - inv_bind; eauto.
      inv_ret; eauto.
    - destruct out, st; eauto.
  Qed.

  Theorem monad_left_id : forall T T' (p: T -> cprog T') v,
      exec_equiv (Bind (Ret v) p) (p v).
  Proof.
    split; intros.
    - inv_bind.
      inv_ret; eauto.
      inv_ret.
    - destruct out, st; eauto.
  Qed.

  Theorem monad_assoc : forall T T' T''
                          (p1: cprog T)
                          (p2: T -> cprog T')
                          (p3: T' -> cprog T''),
      exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun x => Bind (p2 x) p3)).
  Proof.
    split; intros;
      repeat (inv_bind; eauto).
  Qed.

  Theorem cprog_ok_respects_exec_equiv : forall T (p p': cprog T) tid pre,
      exec_equiv p p' ->
      cprog_ok G tid pre p' ->
      cprog_ok G tid pre p.
  Proof.
    unfold cprog_ok, exec_equiv; intros.
    eapply H0; eauto.
    apply H; eauto.
  Qed.

  Ltac begin_prim :=
    unfold cprog_triple, ReflectDouble, cprog_ok; simpl; intros;
    repeat deex.

  Ltac inv_exec :=
    let inv H := inversion H; subst; repeat inj_pair2 in
    match goal with
    | [ H: exec _ _ _ _ (Finished _ _ _) |- _ ] => inv H
    | [ H: exec _ _ _ _ Error |- _ ] => inv H
    end; try match goal with
             | [ H: step _ _ _ _ _ |- _ ] => inv H
             | [ H: fail_step _ _ |- _ ] => inv H
             end; try congruence.

  Theorem BeginRead_ok : forall tid a,
      cprog_triple G tid
                   (fun v '(sigma_i, sigma) =>
                      {| precondition := Sigma.disk sigma a = Some (v, NoReader);
                         postcondition :=
                           fun '(sigma_i', sigma') _ =>
                             sigma_i' = sigma_i /\
                             sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, Pending)); |})
                   (BeginRead a).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
    (* why does congruence not solve this? *)
    assert (v0 = a0) by congruence; subst; auto.
  Qed.

  Theorem WaitForRead_ok : forall tid a,
      cprog_triple G tid
                   (fun v '(sigma_i, sigma) =>
                      {| precondition :=
                           Sigma.disk sigma a = Some (v, Pending);
                         postcondition :=
                           fun '(sigma_i', sigma') r =>
                             sigma_i' = sigma_i /\
                             sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, NoReader)) /\
                             r = v; |})
                   (WaitForRead a).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
    (* why does congruence not solve this? *)
    assert (v = a0) by congruence; subst; auto.
    congruence.
  Qed.

  Theorem Write_ok : forall tid a v,
      cprog_triple G tid
                   (fun v0 '(sigma_i, sigma) =>
                      {| precondition :=
                           Sigma.disk sigma a = Some (v0, NoReader);
                         postcondition :=
                           fun '(sigma_i', sigma') _ =>
                             sigma_i' = sigma_i /\
                             sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, NoReader)); |})
                   (Write a v).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Get_ok : forall tid,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition := True;
                         postcondition :=
                           fun  '(sigma_i', sigma') r =>
                             sigma_i' = sigma_i /\
                             sigma' = sigma /\
                             r = Sigma.mem sigma; |})
                   Get.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Assgn_ok : forall tid m',
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition := True;
                         postcondition :=
                           fun '(sigma_i', sigma') _ =>
                             sigma_i' = sigma_i /\
                             sigma' = Sigma.set_mem sigma m'; |})
                   (Assgn m').
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Hash_ok : forall tid sz (buf: word sz),
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition := True;
                         postcondition :=
                           fun '(sigma_i', sigma') r =>
                             sigma_i' = sigma_i /\
                             sigma' = Sigma.upd_hm sigma buf; |})
                   (Hash buf).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem GhostUpdate_ok : forall tid up,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition := True;
                         postcondition :=
                           fun '(sigma_i', sigma') _ =>
                             sigma_i' = sigma_i /\
                             sigma' = Sigma.upd_s sigma (up tid); |})
                   (GhostUpdate up).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Yield_ok : forall tid,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition := G tid sigma_i sigma;
                         postcondition :=
                           fun '(sigma_i', sigma') _ =>
                             Rely G tid sigma sigma' /\
                             sigma_i' = sigma'; |})
                   Yield.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
    eauto.
  Qed.

End Primitives.

Hint Extern 0 {{ BeginRead _; _ }} => apply BeginRead_ok : prog.
Hint Extern 0 {{ WaitForRead _; _ }} => apply WaitForRead_ok : prog.
Hint Extern 0 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 0 {{ Get; _ }} => apply Get_ok : prog.
Hint Extern 0 {{ Assgn _; _ }} => apply Assgn_ok : prog.
Hint Extern 0 {{ Hash _; _ }} => apply Hash_ok : prog.
Hint Extern 0 {{ GhostUpdate _; _ }} => apply GhostUpdate_ok : prog.
Hint Extern 0 {{ Yield; _ }} => apply Yield_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
