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
    seq_post : hashmap -> T -> rawdisk -> Prop;
    seq_crash : hashmap -> rawdisk -> Prop; }.

(* a sequential spec is parametrized by some ghost state of type A, a frame
 predicate, and the initial hashmap state *)
Definition SeqSpec A T := A -> PredCrash.rawpred -> hashmap -> SeqSpecParams T.

Definition prog_quadruple A T (spec: SeqSpec A T) (p: prog T) :=
  forall a F hm d,
    seq_pre (spec a F hm) d ->
    sync_invariant F ->
    forall out, Prog.exec d hm p out ->
           match out with
           | Prog.Finished d' hm' v => seq_post (spec a F hm) hm' v d'
           | Prog.Failed _ => False
           | Prog.Crashed _ d' hm' => seq_crash (spec a F hm) hm' d' /\
                                     (exists l, hashmap_subset l hm hm')
           end.

Definition prog_spec A T (spec: SeqSpec A T) (p: prog T) :=
  forall T' (rx: T -> prog T'),
    Hoare.corr2 (fun hm donecond crashcond =>
                   exists a F_,
                     seq_pre (spec a F_ hm) *
                     [[ sync_invariant F_ ]] *
                     [[ forall r, Hoare.corr2
                               (fun hm' donecond_rx crashcond_rx =>
                                  seq_post (spec a F_ hm) hm' r *
                                  [[ donecond_rx = donecond ]] *
                                  [[ crashcond_rx = crashcond ]]) (rx r) ]] *
                     [[ forall hm_crash,
                          seq_crash (spec a F_ hm) hm_crash *
                          [[ exists l, hashmap_subset l hm hm_crash ]] =p=>
                        crashcond hm_crash ]])%pred
                (Prog.Bind p rx).

Lemma exec_ret : forall T m hm (v:T) out,
    exec m hm (Ret v) out ->
    out = Finished m hm v.
Proof.
  intros.
  inversion H; repeat inj_pair2; eauto.
  inversion H5.
  inversion H5.
  inversion H5.
Qed.

Definition hashmap_le hm hm' :=
  exists l, hashmap_subset l hm hm'.

Lemma hashmap_le_refl : forall hm,
    hashmap_le hm hm.
Proof.
  intros.
  exists nil.
  constructor.
Qed.

Hint Resolve hashmap_le_refl.

Instance hashmap_le_preorder : RelationClasses.PreOrder hashmap_le.
Proof.
  unfold hashmap_le.
  constructor; hnf; intros.
  - auto.
  - repeat deex.
    eexists.
    eapply hashmap_subset_trans; eauto.
Qed.

Lemma step_hashmap_le : forall T m hm (p: prog T) m' hm' v,
    step m hm p m' hm' v ->
    hashmap_le hm hm'.
Proof.
  inversion 1; intros; repeat (subst; inj_pair2); eauto.
  unfold hashmap_le.
  eauto using HS_nil, HS_cons.
Qed.

Theorem exec_hashmap_le : forall T m hm (p: prog T) out,
    exec m hm p out ->
    match out with
    | Finished _ hm' _ => hashmap_le hm hm'
    | Crashed _ _ hm' => hashmap_le hm hm'
    | Failed _ => True
    end.
Proof.
  induction 1; intros; eauto.

  eapply step_hashmap_le; eauto.
  destruct out; eauto; try solve [ etransitivity; eauto ].
Qed.

Theorem prog_quadruple_spec_equiv : forall A T (spec: SeqSpec A T) (p: prog T),
    prog_spec spec p <->
    prog_quadruple spec p.
Proof.
  unfold prog_spec, prog_quadruple.
  split; intros.
  - specialize (H _ Ret).
    unfold Hoare.corr2 at 1 in H.
    specialize (H (fun hm' v d' => seq_post (spec a F hm) hm' v d')).
    specialize (H (fun hm' d' => seq_crash (spec a F hm) hm' d')).
    specialize (H d hm out).
    intuition eauto.

    edestruct H; repeat deex; intuition eauto.
    + exists a, F.

      SepAuto.pred_apply; SepAuto.cancel.

      unfold Hoare.corr2; intros.

      repeat match goal with
             | [ H: (_ * [[ _ ]])%pred _ |- _ ] =>
               apply sep_star_lift_apply in H; intuition eauto
             end; subst.
      match goal with
      | [ H: exec _ _ (Ret _) _ |- _ ] =>
        apply exec_ret in H; subst
      end.
      eauto 10.

      SepAuto.cancel.
    + apply ProgMonad.bind_right_id; auto.
    + eapply exec_hashmap_le in H2; eauto.
  - unfold Hoare.corr2; intros.
    unfold exis in H0; repeat deex.

    repeat match goal with
           | [ H: (_ * [[ _ ]])%pred _ |- _ ] =>
             apply sep_star_lift_apply in H; intuition eauto
           end; subst.
    inversion H1; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ _ _ _ _ |- _ ] => solve [ inversion H ]
          | [ H: fail_step  _ _ |- _ ] => solve [ inversion H ]
          | [ H: crash_step _ |- _ ] => solve [ inversion H ]
          end.
    + eapply H in H10; eauto.
      eapply H4 in H13; eauto.
      SepAuto.pred_apply; SepAuto.cancel.
    + eapply H in H9; eauto; contradiction.
    + eapply H in H9; intuition eauto.
      right; repeat eexists; eauto.
      eapply H3.
      SepAuto.pred_apply; SepAuto.cancel.
Qed.

Notation "'SPEC' {< a1 .. an , 'PRE' : hm pre 'POST' : hm' post 'CRASH' : hm'c crash >}" :=
  (fun a1 => .. (fun an =>
                (fun F_ =>
                   fun hm => {|
                       seq_pre := sep_star F_ pre%pred;
                       seq_post := fun hm' => post F_%pred;
                       seq_crash := fun hm'c => crash%pred;
                     |}
             )) .. )
    (at level 0,
     hm at level 0, hm' at level 0, hm'c at level 0,
     a1 binder, an binder).