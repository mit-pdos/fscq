Require Import Prog ProgMonad.
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
Require Import Hashmap.
Require Import ListUtils.
Require Import ProofIrrelevance.

Set Implicit Arguments.

(** * Some helpful [prog] combinators and proofs *)

Lemma sync_invariant_possible_sync : forall (F: rawpred) (m: rawdisk),
    F m ->
    sync_invariant F ->
    possible_sync m =p=> F.
Proof.
  unfold sync_invariant; eauto.
Qed.

Hint Resolve sync_invariant_possible_sync.

Theorem read_ok:
  forall (a:addr),
  {< v,
  PRE:hm         a |+> v
  POST:hm' RET:r a |+> v * [[ r = (fst v) ]]
  CRASH:hm'      a |+> v
  >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_subset_valid' in H; deex.
    unfold possible_sync in *.
    destruct (H15 a).
    intuition congruence.
    repeat deex; simpl in *.
    congruence.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} Bind (Read _) _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu),
  {< v0,
  PRE:hm         a |+> v0
  POST:hm' RET:r a |+> (v, vsmerge v0)
  CRASH:hm'      a |+> v0
  >} Write a v.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    repeat apply sep_star_lift_apply'; eauto.

    pose proof (ptsto_subset_valid' H); deex; eauto; simpl in *.
    rewrite H1 in H16; inversion H16; subst; clear H16.

    eapply pimpl_apply.
    cancel.

    eapply sync_invariant_possible_sync; eauto.
    eapply ptsto_subset_upd; eauto.
    unfold vsmerge; simpl.
    eapply incl_cons.
    constructor; auto.
    eapply incl_tl; eauto.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.

Hint Extern 1 ({{_}} Bind (Write _ _) _) => apply write_ok : prog.

Theorem possible_sync_from_sync : forall A AEQ (m m': @Mem.mem A AEQ _),
    possible_sync (sync_mem m) m' ->
    m' = sync_mem m.
Proof.
  unfold possible_sync, sync_mem; intros.
  extensionality a.
  specialize (H a).
  destruct (m a) as [ [? ?] | ];
    intuition; repeat deex; try congruence.
  inversion H0; subst.
  apply incl_in_nil in H2; subst; eauto.
Qed.

Theorem sync_ok:
  {!< F,
  PRE:vm,hm          F * [[ sync_invariant F ]]
  POST:vm',hm' RET:r sync_xform F * [[ vm' = vm ]]
  CRASH:hm'          F
  >!} Sync.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.

    eapply pimpl_apply.
    cancel.

    apply possible_sync_from_sync in H15; subst.
    eapply pimpl_apply; [ | eapply sync_xform_pred_apply; pred_apply; reflexivity ].
    cancel.
Qed.

Hint Extern 1 ({{_}} Bind Sync _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (@Sync _) _) => apply sync_ok : prog.

Theorem trim_ok:
  forall (a:addr),
  {< v0,
  PRE:hm         a |+> v0
  POST:hm' RET:r a |+>?
  CRASH:hm'      a |+>?
  >} Trim a.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - eapply H4; eauto.
    apply sep_star_comm in H as H'. apply ptsto_subset_valid in H'; repeat deex.
    apply sep_star_comm in H as H'. rewrite ptsto_subset_pimpl_ptsto_ex in H'. destruct_lift H'.
    apply ptsto_valid in H0.
    rewrite H0 in H1; inversion H1; subst.
    inv_exec' H10.
    destruct vs'.

    repeat apply sep_star_lift_apply'; eauto.
    eapply sync_invariant_possible_sync; eauto.

    eapply pimpl_apply.
    2: eapply ptsto_subset_upd.
    cancel.
    eauto.
    eapply incl_refl.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
Qed.

Hint Extern 1 ({{_}} Bind (Trim _) _) => apply trim_ok : prog.

Theorem hash_ok:
  forall sz (buf : word sz),
  {< (_: unit),
  PRE:hm    emp
  POST:hm'
    RET:h     emp *
              [[ hash_safe hm h buf ]] *
              [[ h = hash_fwd buf ]] *
              [[ hm' = upd_hashmap' hm h buf ]]
  CRASH:hm' emp * [[ hm' = hm ]]
  >} Hash buf.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
Qed.

Hint Extern 1 ({{_}} Bind (Hash _) _) => apply hash_ok : prog.

(** program equivalence and monad laws *)

Definition If_ T P Q (b : {P} + {Q}) (p1 p2 : prog T) :=
  if b then p1 else p2.

Theorem if_ok:
  forall T T' P Q (b : {P}+{Q}) (p1 p2 : prog T) (p': T -> prog T'),
  {{ fun vm hm done crash => exists pre, pre
   * [[ {{ fun vm' hm' done' crash' => pre * [[P]] * [[ hm = hm' ]] * [[ vm = vm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} Bind p1 p' ]]
   * [[ {{ fun vm' hm' done' crash' => pre * [[Q]] * [[ hm = hm' ]] * [[ vm = vm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} Bind p2 p' ]]
  }} Bind (If_ b p1 p2) p'.
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

(* helper to use If with an option *)
Definition is_some A (a: option A) : {a <> None} + {a = None}.
Proof.
  destruct a; left + right; congruence.
Defined.

Hint Extern 1 ({{_}} Bind (If_ _ _ _) _) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

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

Lemma word_minus_1 : forall sz (w: word sz),
    w <> $ 0 ->
    (w ^- $1 < w)%word.
Proof.
  intros.
  apply weq_minus1_wlt; auto.
Qed.

Definition For_ (L : Type) (G : Type) (f : waddr -> L -> prog L)
                (i n : waddr)
                (nocrash : G -> waddr -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L.
Proof.
  refine (Fix (@for_args_wf L) (fun _ => prog L)
          (fun args For_ => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 $0 then Ret For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0); _).
  refine (For_ {| For_args_i := For_args_i0 ^+ $1;
                  For_args_n := For_args_n0 ^- $1;
                  For_args_l := l' |} _).

  simpl.
  apply word_minus_1; auto.
Defined.

Lemma For_step: forall L G (f: waddr -> L -> prog L) i n l nocrash crashed,
  @For_ L G f i n nocrash crashed l =
    if weq n $0
    then Ret l
    else l' <- (f i l);
         @For_ L G f
             (i ^+ $1)
             (n ^- $1)
             nocrash crashed l'.
Proof.
  intros.
  unfold For_.
  rewrite Fix_eq.
  simpl.

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
         (f: waddr -> L -> prog L) (rx: L -> prog T)
         (nocrash : G -> waddr -> L -> varmem -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g i li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (m ^+ $1) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (n ^+ i) lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (For_ f i n nocrash crashed li) rx.
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
      simpl; monad_simpl; eauto.
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
      monad_simpl.
      apply H4.

      apply eq_le; auto.
      rewrite wplus_comm.
      apply lt_wlt.
      omega.

      intros.
      eapply pimpl_ok2.
      apply H.

      apply word_minus_1; auto.

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
         (nocrash : G -> waddr -> L -> varmem -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g $0 li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (m ^+ $1) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g n lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (For_ f $0 n nocrash crashed li) rx.
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

Hint Extern 1 ({{_}} Bind (For_ _ _ _ _ _ _) _) => apply for_ok : prog.

Notation "'For' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'For' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Fixpoint ForN_  (L : Type) (G : Type) (f : nat -> L -> prog L)
                (i n : nat)
                (nocrash : G -> nat -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;  ForN_ f (S i) m nocrash crashed l'
  end.


Theorem forN_ok':
  forall T (n i : nat)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> varmem -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g i li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      i <= m ->
      m < n + i ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (S m) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (n + i) lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForN_ f i n nocrash crashed li) rx.
Proof.
  induction n; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.

      eapply pimpl_ok2; monad_simpl.
      apply H1. omega. omega.
      intros.
      eapply pimpl_ok2.
      eapply IHn.
      cancel.
      cancel.

      2: intros; apply pimpl_refl.

      eapply pimpl_ok2.
      eauto.
      intros.
      cancel.

      replace (n + S i) with (S (n + i)) by omega.
      eauto.
    + cancel.
Qed.

Theorem forN_ok:
  forall (n : nat)
         T (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> varmem -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g 0 li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      m < n ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (S m) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g n lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForN_ f 0 n nocrash crashed li) rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply forN_ok'.
  cancel.
  cancel.
  eapply pimpl_ok2.
  eauto.
  replace (n + 0) with n by omega; auto.
Qed.

Hint Extern 1 ({{_}} Bind (ForN_ _ _ _ _ _ _) _) => apply forN_ok : prog.

Notation "'ForN' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).


Fixpoint ForEach_ (ITEM : Type)
                (L : Type) (G : Type) (f : ITEM -> L -> prog L)
                (lst : list ITEM)
                (nocrash : G -> list ITEM -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match lst with
  | nil => Ret l
  | elem :: lst' =>
    l' <- f elem l;
    ForEach_ f lst' nocrash crashed l'
  end.

Theorem foreach_ok:
  forall T ITEM (lst : list ITEM)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> list ITEM -> L -> varmem -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g lst li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall elem lst' lm rxm,
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g lst' lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]]  * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g (elem :: lst') lm vm'' hm'' *
         [[ exists l, hashmap_subset l hm' hm'' ]] *
         [[ exists prefix, prefix ++ elem :: lst' = lst ]] *
         [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f elem lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g nil lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForEach_ f lst nocrash crashed li) rx.
Proof.
  intros ITEM.
  induction lst; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl.
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

Hint Extern 1 ({{_}} Bind (ForEach_ _ _ _ _ _) _) => apply foreach_ok : prog.

Notation "'ForEach' elem rest lst 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))  )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))  )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

(* TODO: need a good spec for this. Probably want a predicate
describing early breaks, so that we can guarantee something if the
function terminates without breaking (otherwise the spec would equally
apply to a loop that didn't do anything) *)
Fixpoint ForNBreak_  (L : Type) (G : Type) (f : nat -> L -> prog (L+L))
                (i n : nat)
                (nocrash : G -> nat -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;
            match l' with
            | inl l' => ForNBreak_ f (S i) m nocrash crashed l'
            | inr l' => Ret l'
            end
  end.

Definition Continue L (l:L) : L + L := inl l.
Definition Break L (l:L) : L + L := inr l.


Theorem var_get_ok:
  forall (Tv : Type) (i : addr),
  {< (x : Tv) Fv,
  PRE::vm,hm          emp * [[ (Fv * i |-> Any x)%pred vm ]]
  POST::vm',hm' RET:r emp * [[ r = x ]] * [[ vm' = vm ]]
  CRASH:hm'           [[ False ]]
  >} VarGet i.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H11.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_valid' in H6.
    rewrite H6 in *.
    inversion H17.
    apply inj_pair2 in H1; eauto.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
Qed.

Hint Extern 1 ({{_}} Bind (VarGet _) _) => apply var_get_ok : prog.

Theorem var_set_ok:
  forall (T : Type) (i : addr) (v : T),
  {< v0 Fv,
  PRE::vm,hm          emp * [[ (Fv * i |-> v0)%pred vm ]]
  POST::vm',hm' RET:_ emp * [[ (Fv * i |-> Any v)%pred vm' ]]
  CRASH:hm'           [[ False ]]
  >} VarSet i v.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H11.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_upd'.
    eauto.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
Qed.

Hint Extern 1 ({{_}} Bind (VarSet _ _) _) => apply var_set_ok : prog.

Theorem var_alloc_ok:
  forall (T : Type) (v : T),
  {< Fv,
  PRE::vm,hm          emp * [[ Fv vm ]]
  POST::vm',hm' RET:r emp * [[ (Fv * r |-> Any v)%pred vm' ]]
  CRASH:hm'           [[ False ]]
  >} VarAlloc v.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  inv_exec' H11.
  eapply H4; eauto.
  pred_apply; cancel.
  eauto.
  eapply ptsto_insert_disjoint; eauto.
Qed.

Hint Extern 1 ({{_}} Bind (VarAlloc _) _) => apply var_alloc_ok : prog.

Theorem var_delete_ok:
  forall (i : addr),
  {< v Fv,
  PRE::vm,hm          emp * [[ (Fv * i |-> v)%pred vm ]]
  POST::vm',hm' RET:_ emp * [[ Fv vm' ]]
  CRASH:hm'           [[ False ]]
  >} VarDelete i.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H11.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_delete'.
    pred_apply; cancel.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
Qed.

Hint Extern 1 ({{_}} Bind (VarDelete _) _) => apply var_delete_ok : prog.
