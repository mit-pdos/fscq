Require Import Prog.
Require Import Automation.
Require Import AsyncDisk.
Require Import Pred PredCrash.
Require Import Hashmap.
Require Hoare.
Require SepAuto.

Set Implicit Arguments.

(* a sequential spec consists mostly of a SeqSpecParams, though SeqSpec includes
some additional parameters that can apply to all three parts *)
Record SeqSpecParams T :=
  { seq_pre : rawdisk -> Prop;
    seq_post : varmem -> hashmap -> T -> rawdisk -> Prop;
    seq_crash : hashmap -> rawdisk -> Prop; }.

(* a sequential spec is parametrized by some ghost state of type A and the
initial hashmap/memory state *)
Definition SeqSpec A T := A -> varmem -> hashmap -> SeqSpecParams T.

Definition prog_quadruple A T (spec: SeqSpec A T) (p: prog T) :=
  forall a hm vm d,
    seq_pre (spec a vm hm) d ->
    forall out, Prog.exec d vm hm p out ->
           match out with
           | Prog.Finished d' vm' hm' v => seq_post (spec a vm hm) vm' hm' v d'
           | Prog.Failed _ => False
           | Prog.Crashed _ d' hm' => seq_crash (spec a vm hm) hm' d' /\
                                     (exists l, hashmap_subset l hm hm')
           end.

Definition prog_spec A T (spec: SeqSpec A T) (p: prog T) :=
  forall T' (rx: T -> prog T'),
    Hoare.corr2 (fun vm hm donecond crashcond =>
                   exists a,
                     seq_pre (spec a vm hm) *
                     [[ forall r, Hoare.corr2
                               (fun vm' hm' donecond_rx crashcond_rx =>
                                  seq_post (spec a vm hm) vm' hm' r *
                                  [[ donecond_rx = donecond ]] *
                                  [[ crashcond_rx = crashcond ]]) (rx r) ]] *
                     [[ forall hm_crash,
                          seq_crash (spec a vm hm) hm_crash *
                          [[ exists l, hashmap_subset l hm hm_crash ]] =p=>
                        crashcond hm_crash ]])%pred
                (Prog.Bind p rx).

Lemma exec_ret : forall T m vm hm (v:T) out,
    exec m vm hm (Ret v) out ->
    out = Finished m vm hm v.
Proof.
  intros.
  inversion H; repeat inj_pair2; eauto;
    repeat match goal with
           | [ H: _ |- _ ] =>
             solve [ inversion H ]
           end.
Qed.

Lemma step_hashmap_le : forall T m vm hm (p: prog T) m' vm' hm' v,
    step m vm hm p m' vm' hm' v ->
    hashmap_le hm hm'.
Proof.
  inversion 1; intros; repeat (subst; inj_pair2); eauto using hashmap_le_refl.
  unfold hashmap_le.
  eauto using HS_nil, HS_cons.
Qed.

Theorem exec_hashmap_le : forall T m vm hm (p: prog T) out,
    exec m vm hm p out ->
    match out with
    | Finished _ _ hm' _ => hashmap_le hm hm'
    | Crashed _ _ hm' => hashmap_le hm hm'
    | Failed _ => True
    end.
Proof.
  induction 1; intros; eauto using hashmap_le_refl.

  eapply step_hashmap_le; eauto.
  destruct out; eauto; try solve [ etransitivity; eauto ].
Qed.

Theorem prog_quadruple_spec_equiv : forall A T (spec: SeqSpec (A*rawpred) T) (p: prog T),
    prog_spec spec p <->
    prog_quadruple spec p.
Proof.
  unfold prog_spec, prog_quadruple.
  split; intros.
  - specialize (H _ Ret).
    unfold Hoare.corr2 at 1 in H.
    specialize (H (fun vm' hm' v => seq_post (spec a vm hm) vm' hm' v)).
    specialize (H (fun hm' => (seq_crash (spec a vm hm) hm')%pred)).
    specialize (H d vm hm out).
    intuition eauto.

    edestruct H; repeat deex; intuition eauto.
    + exists a.

      SepAuto.pred_apply; SepAuto.cancel.

      unfold Hoare.corr2; intros.

      repeat match goal with
             | [ H: (_ * [[ _ ]])%pred _ |- _ ] =>
               apply sep_star_lift_apply in H; intuition eauto
             end; subst.
      match goal with
      | [ H: exec _ _ _ (Ret _) _ |- _ ] =>
        apply exec_ret in H; subst
      end.
      eauto 10.

      SepAuto.cancel.
    + apply ProgMonad.bind_right_id; auto.
    + match goal with
      | [ H: exec _ _ _ _ (Crashed _ _ _) |- _ ] =>
        eapply exec_hashmap_le in H; eauto
      end.
  - unfold Hoare.corr2; intros.
    unfold exis in H0; repeat deex.

    repeat match goal with
           | [ H: (_ * [[ _ ]])%pred _ |- _ ] =>
             apply sep_star_lift_apply in H; intuition eauto
           end; subst.
    inversion H1; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ _ _ _ _ _ _ |- _ ] => solve [ inversion H ]
          | [ H: fail_step _ _ _ |- _ ] => solve [ inversion H ]
          | [ H: crash_step _ |- _ ] => solve [ inversion H ]
          end;
      repeat match goal with
             | [ H: context[exec _ _ _ ?p _],
                    Hexec: exec _ _ _ ?p _ |- _ ] =>
               eapply H in Hexec; eauto
             end;
      try contradiction.
    + match goal with
      | [ Hexec: exec _ _ _ (rx _) _ |- _ ] =>
        eapply H4 in Hexec; eauto
      end.
      SepAuto.pred_apply; SepAuto.cancel.
    + right; repeat eexists; intuition eauto.
      eapply H3.
      SepAuto.pred_apply; SepAuto.cancel.
Qed.
