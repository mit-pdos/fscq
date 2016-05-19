Require Import Prog.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import List.
Require Import AsyncDisk.
Require Import EqdepFacts.
Require Import Hashmap.
Require Import ListUtils.

Set Implicit Arguments.


(** * Some helpful [prog] combinators and proofs *)

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ ?p _ |- _ ] => remember p; induction H; subst; try congruence
  end.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ ?p _ _ _|- _ ] => remember p; induction H; inversion Heqp; subst; try congruence
  end.

Theorem read_ok:
  forall (a:addr),
  {< v,
  PRE        a |+> v
  POST RET:r a |+> v * [[ r = (fst v) ]]
  CRASH      a |+> v
  >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_step.
    + eapply H4; eauto.
      apply sep_star_comm in H as H'. apply ptsto_subset_valid in H'; repeat deex.
      pred_apply; cancel.
    + eapply IHexec; eauto.
      eapply upd_sync_invariant; eauto.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    apply H0. repeat eexists. econstructor. eauto.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} progseq (Read _) _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu),
  {< v0,
  PRE        a |+> v0
  POST RET:r a |+> (v, vsmerge v0)
  CRASH      a |+> v0
  >} Write a v.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_step.
    + eapply H4; eauto.
      apply sep_star_comm in H as H'. apply ptsto_subset_valid in H'; repeat deex.
      apply sep_star_comm in H as H'. rewrite ptsto_subset_pimpl_ptsto_ex in H'. destruct_lift H'.
      rewrite H0 in H6; inversion H6; subst.
      eapply pimpl_trans; [ | | eapply ptsto_upd; pred_apply; cancel ].
      eauto.
      rewrite ptsto_pimpl_ptsto_subset.
      erewrite ptsto_subset_pimpl. cancel.
      unfold vsmerge; simpl.
      eapply incl_cons2; eauto.
    + eapply IHexec; eauto.
      eapply upd_sync_invariant; eauto.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    apply H0. repeat eexists. econstructor. eauto.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} progseq (Write _ _) _) => apply write_ok : prog.

Theorem sync_ok:
  {!< F,
  PRE        F * [[ sync_invariant F ]]
  POST RET:r sync_xform F
  CRASH      F
  >!} @Sync _.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_step.
    + eapply H4; eauto.
      eapply pimpl_trans; [ | | eapply sync_xform_pred_apply; pred_apply; reflexivity ].
      eauto.
      cancel.
    + eapply IHexec; eauto.
      eapply upd_sync_invariant; eauto.
  - exfalso.
    apply H0. repeat eexists. econstructor.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} progseq Sync _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} progseq (@Sync _) _) => apply sync_ok : prog.

Theorem trim_ok:
  forall (a:addr),
  {< v0,
  PRE        a |+> v0
  POST RET:r a |+>?
  CRASH      a |+>?
  >} Trim a.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_step.
    + eapply H4; eauto.
      apply sep_star_comm in H as H'. apply ptsto_subset_valid in H'; repeat deex.
      apply sep_star_comm in H as H'. rewrite ptsto_subset_pimpl_ptsto_ex in H'. destruct_lift H'.
      rewrite H0 in H6; inversion H6; subst.
      eapply pimpl_trans; [ | | eapply ptsto_upd; pred_apply; cancel ].
      eauto.
      rewrite ptsto_pimpl_ptsto_subset.
      cancel.
    + eapply IHexec; eauto.
      eapply upd_sync_invariant; eauto.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    apply H0. repeat eexists. econstructor. eauto.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.

  Grab Existential Variables.
  eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Trim _) _) => apply trim_ok : prog.

Theorem hash_ok:
  forall sz (buf : word sz),
  {< (_: unit),
  PRE:hm    emp
  POST:hm'
    RET:h   emp *
              [[ hash_safe hm h buf ]] *
              [[ h = hash_fwd buf ]] *
              [[ hm' = upd_hashmap' hm h buf ]]
  CRASH:hm' emp * [[ hm' = hm ]]
  >} Hash buf.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_step.
    + eapply H4; eauto.
      pred_apply.
      assert (Hbufeq: buf = buf0).
        pose proof (eq_sigT_snd H8).
        autorewrite with core in *. congruence.
      cancel.
    + eapply IHexec; eauto.
      eapply upd_sync_invariant; eauto.
  - exfalso.
    apply H2. repeat eexists.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} progseq (Hash _) _) => apply hash_ok : prog.

Theorem done_ok:
  forall T (r : T),
  {{ fun hm done crash => done hm r *
                          [[ sync_invariant (done hm r) ]] *
                          [[ forall hm, done hm r =p=> crash hm ]] }} Done r.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_step.
    eapply IHexec; eauto.
    eapply upd_sync_invariant; eauto.
  - exfalso.
    apply H1. eauto.
  - right. eexists; eexists; intuition eauto.
    apply H3; auto.
  - left. do 3 eexists; split. eauto. congruence.
Qed.

Hint Extern 1 ({{_}} progseq (Done _) _) => apply done_ok : prog.

Definition If_ T P Q (b : {P} + {Q}) (p1 p2 : prog T) :=
  if b then p1 else p2.

Theorem if_ok:
  forall T P Q (b : {P}+{Q}) (p1 p2 : prog T),
  {{ fun hm done crash => exists pre, pre
   * [[ {{ fun hm' done' crash' => pre * [[P]] * [[ hm = hm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} p1 ]]
   * [[ {{ fun hm' done' crash' => pre * [[Q]] * [[ hm = hm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} p2 ]]
  }} If_ b p1 p2.
Proof.
  unfold corr2, corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  destruct b.
  - eapply H2; eauto.
    eapply pimpl_apply; [|apply H].
    cancel.
  - eapply H1; eauto.
    eapply pimpl_apply; [|apply H].
    cancel.
Qed.

Hint Extern 1 ({{_}} If_ _ _ _) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

Definition IfRx_ T P Q R (b : {P} + {Q}) (p1 p2 : (R -> prog T) -> prog T) (rx : R -> prog T) : prog T :=
  If_ b (p1 rx) (p2 rx).

Theorem ifrx_ok:
  forall T P Q R (b : {P}+{Q}) (p1 p2 : (R -> prog T) -> prog T) rx,
  {{ fun hm done crash => exists pre, pre
   * [[ {{ fun hm' done' crash' => pre * [[P]] * [[ hm = hm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} p1 rx ]]
   * [[ {{ fun hm' done' crash' => pre * [[Q]] * [[ hm = hm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} p2 rx ]]
  }} IfRx_ b p1 p2 rx.
Proof.
  unfold IfRx_; intros.
  apply if_ok.
Qed.

Hint Extern 1 ({{_}} progseq (IfRx_ _ _ _) _) => apply ifrx_ok : prog.

Notation "'IfRx' rx b { p1 } 'else' { p2 }" :=
  (IfRx_ b (fun rx => p1) (fun rx => p2)) (at level 9, rx at level 0, b at level 0).

Record For_args (L : Type) := {
  For_args_i : waddr;
  For_args_n : waddr;
  For_args_l : L
}.

Theorem for_args_wf: forall L,
  well_founded (fun a b => wlt a.(@For_args_n L) b.(@For_args_n L)).
Proof.
  intros.
  apply well_founded_lt_compat with (f:=fun a => wordToNat (a.(For_args_n))).
  intros.
  apply wlt_lt; auto.
Qed.

Definition For_ (T: Type)
                (L : Type) (G : Type) (f : waddr -> L -> (L -> prog T) -> prog T)
                (i n : waddr)
                (nocrash : G -> waddr -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L)
                (rx: L -> prog T) : prog T.
  refine (Fix (@for_args_wf L) (fun _ => prog T)
          (fun args For_ => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 $0 then rx For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0); _).
  refine (For_ {| For_args_i := For_args_i0 ^+ $1;
                  For_args_n := For_args_n0 ^- $1;
                  For_args_l := l' |} _).

  assert (wordToNat For_args_n0 <> 0).
  unfold not in *; intros; apply n.
  rewrite <- H.
  rewrite natToWord_wordToNat; auto.

  simpl.
  rewrite wminus_Alt.
  rewrite wminus_Alt2.
  unfold wordBinN.
  rewrite (@wordToNat_natToWord_idempotent' addrlen 1);
    [| replace (1) with (wordToNat (natToWord addrlen 1)) by auto; apply wordToNat_bound ].
  apply lt_wlt.

  rewrite wordToNat_natToWord_idempotent';
    [| assert (wordToNat For_args_n0 < pow2 addrlen) by apply wordToNat_bound;
       unfold goodSize in *; omega ].
  apply PeanoNat.Nat.sub_lt; omega.

  unfold wlt, not in *; intro Hn.
  apply H.
  apply Nlt_out in Hn.
  repeat rewrite wordToN_nat in Hn.
  repeat rewrite Nat2N.id in Hn.
  simpl in Hn.
  omega.
Defined.

Lemma For_step: forall T L G f i n l nocrash crashed (rx: _ -> prog T),
  @For_ T L G f i n nocrash crashed l rx =
    if weq n $0
    then rx l
    else l' <- (f i l);
         @For_ T L G f
               (i ^+ $1)
               (n ^- $1)
               nocrash crashed l' rx.
Proof.
  intros.
  unfold For_.
  rewrite Fix_eq.

  destruct (weq n $0); f_equal.

  intros.

  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; f_equal
  end.

  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; try reflexivity
  end.

  apply f_equal.
  apply functional_extensionality; auto.
Qed.

Theorem for_ok':
  forall T (n i : waddr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> waddr -> L -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g i li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (m ^+ $1) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} f m lm rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g (n ^+ i) lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} (For_ f i n nocrash crashed li rx).
Proof.
  intro T.
  wlt_ind.

  intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  case_eq (weq x $0); intros; subst.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_step.
      eapply pimpl_ok2.
      simpl; eauto.
      intros.
      apply pimpl_refl.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). cancel.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + assert (wordToNat x <> 0).
      unfold not in *; intros; apply n.
      rewrite <- H6; rewrite natToWord_wordToNat; auto.

      unfold pimpl, lift; intros.
      rewrite For_step.
      rewrite H0.
      apply H4.

      apply eq_le; auto.
      rewrite wplus_comm.
      apply lt_wlt.
      omega.

      intros.
      eapply pimpl_ok2.
      apply H.

      apply lt_wlt.
      rewrite wminus_Alt.
      rewrite wminus_Alt2.
      unfold wordBinN.
      rewrite wordToNat_natToWord_idempotent'.
      simpl; omega.
      simpl (wordToNat $1).
      eapply Nat.lt_le_trans; [| apply (wordToNat_bound x) ].
      omega.
      unfold not in *; intros; apply n.
      apply wlt_lt in H8; simpl in H8.
      rewrite <- natToWord_wordToNat with (w:=x).
      f_equal.
      omega.

      intros.
      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      apply pimpl_exists_r; exists a1.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      cancel.

      subst; apply H4; eauto.
      intros; apply H9; clear H9.
      apply wlt_lt in H12.
      unfold wlt.
      repeat rewrite wordToN_nat.
      apply Nlt_in.
      repeat rewrite Nat2N.id.
      rewrite wplus_alt.
      unfold wplusN, wordBinN.
      simpl (wordToNat $1).
      rewrite wordToNat_natToWord_idempotent'.
      omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      rewrite wminus_Alt.
      rewrite wminus_Alt2.
      repeat rewrite wplus_alt.
      repeat unfold wplusN, wordBinN.

      simpl (wordToNat $1).
      repeat rewrite wordToNat_natToWord_idempotent'.
      omega.
      rewrite H2; apply wordToNat_bound.

      eapply Nat.le_lt_trans; [| apply (wordToNat_bound x) ]; omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      unfold not; intros; apply H6.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H9; simpl in H9; auto.
    + cancel.
Qed.

Theorem for_ok:
  forall T (n : waddr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> waddr -> L -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g $0 li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (m ^+ $1) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} f m lm rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g n lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} For_ f $0 n nocrash crashed li rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply for_ok'.
  fold (wzero addrlen); ring_simplify (wzero addrlen ^+ n).
  simpl (wordToNat (wzero addrlen)); replace (0 + wordToNat n) with (wordToNat n) by omega.
  ring_simplify (n ^+ wzero addrlen).
  cancel.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (For_ _ _ _ _ _ _) _) => apply for_ok : prog.

Notation "'For' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => (fun lrx => body)))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   lrx at level 0,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'For' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => (fun lrx => body)))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   lrx at level 0,
   l1 closed binder, l2 closed binder,
   body at level 9).

Fixpoint ForN_ (T: Type)
                (L : Type) (G : Type) (f : nat -> L -> (L -> prog T) -> prog T)
                (i n : nat)
                (nocrash : G -> nat -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L)
                (rx: L -> prog T) : prog T :=
  match n with
  | 0 =>   rx l
  | S m => l' <- f i l;  ForN_ f (S i) m nocrash crashed l' rx
  end.


Theorem forN_ok':
  forall T (n i : nat)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g i li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      i <= m ->
      m < n + i ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (S m) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} f m lm rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g (n + i) lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} (ForN_ f i n nocrash crashed li rx).
Proof.
  induction n; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2.
      apply H1. omega. omega.
      intros.
      eapply pimpl_ok2.
      eapply IHn.
      cancel.
      cancel.
      eapply pimpl_ok2.
      apply H0.
      intros.
      cancel.
      replace (n + S i) with (S (n + i)) by omega.
      cancel.
      intros.
      apply pimpl_refl.
    + cancel.
Qed.

Theorem forN_ok:
  forall T (n : nat)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g 0 li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      m < n ->
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g (S m) lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g m lm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} f m lm rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g n lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} ForN_ f 0 n nocrash crashed li rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply forN_ok'.
  cancel.
  cancel.
  eapply pimpl_ok2.
  eauto.
  cancel.
  replace (n + 0) with n by omega; auto.
Qed.

Hint Extern 1 ({{_}} progseq (ForN_ _ _ _ _ _ _) _) => apply forN_ok : prog.

Notation "'ForN' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => (fun lrx => body)))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   lrx at level 0,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => (fun lrx => body)))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun hm => nocrash%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   lrx at level 0,
   l1 closed binder, l2 closed binder,
   body at level 9).


Fixpoint ForEach_ (T: Type) (ITEM : Type)
                (L : Type) (G : Type) (f : ITEM -> L -> (L -> prog T) -> prog T)
                (lst : list ITEM)
                (nocrash : G -> list ITEM -> L -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) (rx: L -> prog T) : prog T :=
  match lst with
  | nil => rx l
  | elem :: lst' =>
    l' <- f elem l;
    ForEach_ f lst' nocrash crashed l' rx
  end.

Theorem foreach_ok:
  forall T ITEM (lst : list ITEM)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> list ITEM -> L -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun hm done crash => exists F (g:G) hm', F * nocrash g lst li hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall elem lst' lm rxm,
      (forall lSm,
       {{ fun hm'' done' crash' => F * nocrash g lst' lSm hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]]  * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun hm'' done' crash' => F * nocrash g (elem :: lst') lm hm'' *
         [[ exists l, hashmap_subset l hm' hm'' ]] *
         [[ exists prefix, prefix ++ elem :: lst' = lst ]] *
         [[ done' = done ]] * [[ crash' = crash ]]
      }} f elem lm rxm]]
   * [[forall lfinal,
       {{ fun hm'' done' crash' => F * nocrash g nil lfinal hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} ForEach_ f lst nocrash crashed li rx.
Proof.
  intros T ITEM.
  induction lst; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply IHlst.
      cancel.
      eassign lst.
      cancel.
      eapply pimpl_ok2.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply H2.
      cancel.
      cancel.
      exists (a :: prefix); auto.

      intros.
      apply pimpl_refl.
    + cancel.
      exists nil; auto.
Qed.

Hint Extern 1 ({{_}} progseq (ForEach_ _ _ _ _ _) _) => apply foreach_ok : prog.

Notation "'ForEach' elem rest lst 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => (fun lrx => body))) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun hm => nocrash%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   lrx at level 0,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => (fun lrx => body))) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun hm => nocrash%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   lrx at level 0,
   l1 closed binder, l2 closed binder,
   body at level 9).
