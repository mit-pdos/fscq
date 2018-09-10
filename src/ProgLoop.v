Require Import Pred Mem Word Arith.
Require Import Nomega NArith Omega List ListUtils.
Require Import Morphisms FunctionalExtensionality ProofIrrelevance.
Require Export Instr.

Set Implicit Arguments.


Definition If_ T P Q (b : {P} + {Q}) (p1 p2 : prog T) :=
  if b then p1 else p2.

Theorem if_ok:
  forall T T' P Q (b : {P}+{Q}) (p1 p2 : prog T) (p': T -> prog T') pr,
  (corr2 pr (fun bm hm done crash => exists pre, pre
   * [[ corr2 pr (fun bm' hm' done' crash' => pre * [[P]] * [[ hm = hm' ]] * [[ bm = bm' ]] * [[ done' = done ]] * [[ crash' = crash ]]) (Bind p1 p') ]]
   * [[ corr2 pr (fun bm' hm' done' crash' => pre * [[Q]] * [[ hm = hm' ]] * [[ bm = bm' ]] * [[ done' = done ]] * [[ crash' = crash ]]) (Bind p2 p') ]]
  ))%pred (Bind (If_ b p1 p2) p').
Proof.
  unfold corr2, corr2, exis; intros; cleanup.
  repeat ( apply sep_star_lift2and in H; destruct H).
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

Hint Extern 1 ({{_|_}} Bind (If_ _ _ _) _) => apply if_ok : prog.
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
  apply well_founded_lt_compat with (f:=fun a => wordToNat (@For_args_n L a)).
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
                (nocrash : G -> waddr -> L -> taggedmem -> domainmem -> rawpred tagged_block)
                (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block)
                (l : L) : prog L.
Proof.
  refine (Fix (@for_args_wf L) (fun _ => prog L)
          (fun args For_ => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 $0 then Ret For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0);; _).
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
    else l' <- (f i l);;
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
         (nocrash : G -> waddr -> L -> taggedmem -> domainmem -> rawpred tagged_block)
         (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block)
         (li : L) pr,
    {{ pr | fun done crash bm hm =>
      (exists F (g:G) bm' hm',
          F * nocrash g i li bm hm *
          [[ bm' c= bm ]] * [[ hm' c= hm ]] *
      [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm,
       {{ pr |  fun  done' crash' bm'' hm'' => F * nocrash g (m ^+ $1) lSm bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ pr | fun done' crash' bm'' hm'' => F * nocrash g m lm bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]] *
     [[forall lfinal,
       {{ pr | fun done' crash' bm'' hm''  => F * nocrash g (n ^+ i) lfinal bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]] *
     [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]] *
     [[forall bm'' hm'',
         F * crashed g bm'' hm'' * [[ hm' c= hm'' ]] *
         [[ bm' c= bm'' ]] =p=> crash bm'' hm'' ]])%pred
  }} Bind (For_ f i n nocrash crashed li) rx.
Proof.
  intro T.
  wlt_ind.

  intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  case_eq (weq x $0); intros; subst.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_step.
      eapply pimpl_ok2.
      simpl; monad_simpl; eauto.
      apply ret_secure'.
      intros.
      apply pimpl_refl.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). cancel.
      eassign (fun bm hm => (nocrash a0 i li bm hm * a)%pred); simpl; cancel.
      eapply pimpl_ok2. eauto. intros; simpl. safecancel.
      fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). cancel.
      intros _ _; eauto.
      unfold false_pred; cancel; eauto.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + assert (wordToNat x <> 0).
      unfold not in *; intros; apply n.
      rewrite <- H7; rewrite natToWord_wordToNat; auto.

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
      apply pimpl_exists_r; exists a2.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      cancel.
      eauto.

      subst; eapply H4; eauto.
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

      unfold not; intros; apply H7.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H9; simpl in H9; auto.
    + cancel; eauto.
      Unshelve.
      unfold EqDec; apply handle_eq_dec.
Qed.

Theorem for_ok:
  forall T (n : waddr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> waddr -> L -> taggedmem -> domainmem -> rawpred tagged_block)
         (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block)
         (li : L) pr,
    {{ pr | fun done crash bm hm =>
         (exists F (g:G) bm' hm', F * nocrash g $0 li bm hm * [[ hm' c= hm ]]
   * [[ bm' c= bm ]]
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g (m ^+ $1) lSm bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ pr | fun done' crash' bm'' hm'' => F * nocrash g m lm bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g n lfinal bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall bm'' hm'',
         F * crashed g bm'' hm'' * [[ hm' c= hm'' ]] *
         [[ bm' c= bm'' ]] =p=> crash bm'' hm'' ]])%pred
  }} Bind (For_ f $0 n nocrash crashed li) rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply for_ok'.
  fold (wzero addrlen); ring_simplify (wzero addrlen ^+ n).
  simpl (wordToNat (wzero addrlen)); replace (0 + wordToNat n) with (wordToNat n) by omega.
  ring_simplify (n ^+ wzero addrlen).
  safecancel.
  cancel; apply pimpl_refl.
  eassign bm'; cancel.
  eauto.
  eauto.
  eauto.
  eauto.

  Unshelve.
  all: unfold EqDec; intros; apply handle_eq_dec.
Qed.

Hint Extern 1 ({{_ | _}} Bind (For_ _ _ _ _ _ _) _) => apply for_ok : prog.

Notation "'For' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'For' i < n 'Blockmem' bm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).


Notation "'For' i < n 'Blockmem' bm 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).


Fixpoint ForN_  (L : Type) (G : Type) (f : nat -> L -> prog L)
                (i n : nat)
                (nocrash : G -> nat -> L -> taggedmem -> domainmem -> rawpred tagged_block)
                (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;;  ForN_ f (S i) m nocrash crashed l'
  end.


Theorem forN_ok':
  forall T (n i : nat)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> taggedmem -> domainmem -> pred)
         (crashed : G -> taggedmem -> domainmem -> pred)
         (li : L) pr,
    {{ pr | fun done crash bm hm => (exists F (g:G) bm' hm',
   F * nocrash g i li bm hm * [[ hm' c= hm ]] 
   * [[ bm' c= bm ]]
   * [[forall m lm rxm,
      i <= m ->
      m < n + i ->
      (forall lSm,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g (S m) lSm bm'' hm'' *
           [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ pr | fun done' crash' bm'' hm'' => F * nocrash g m lm bm'' hm'' *
           [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ pr | fun done' crash' bm'' hm''=> F * nocrash g (n + i) lfinal bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall bm'' hm'',
        F * crashed g bm'' hm'' * [[ hm' c= hm'' ]] * [[ bm' c= bm'' ]] =p=> crash bm'' hm'' ]])%pred
  }} Bind (ForN_ f i n nocrash crashed li) rx.
Proof.
  induction n; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl.
      apply ret_secure'.
      intros.
      apply pimpl_refl.
    + simpl. cancel.
      eassign (fun bm hm => nocrash a0 i li bm hm * a)%pred.
      apply pimpl_refl.
      eapply pimpl_ok2; eauto.
      intros; cancel.
      eauto.
      unfold false_pred; cancel; auto.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.

      eapply pimpl_ok2; monad_simpl.
      apply H1. omega. omega.
      intros.
      eapply pimpl_ok2.
      eapply IHn.
      safecancel.
      cancel.
      apply pimpl_refl.
      eauto.
      eauto.

      apply H1.
      omega.
      omega.
      auto.

      replace (n + S i) with (S (n + i)) by omega.
      eauto.

      rewrite <- H; cancel; eauto.
      intros; apply pimpl_refl.
    + cancel; eauto.
 Unshelve.
 all: unfold EqDec; apply handle_eq_dec.     
Qed.

Theorem forN_ok:
  forall (n : nat)
         T (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> taggedmem -> domainmem -> pred)
         (crashed : G -> taggedmem -> domainmem -> pred)
         (li : L) pr,
  {{ pr | fun done crash bm hm => (exists F (g:G) bm' hm', F * nocrash g 0 li bm hm
   * [[ bm' c= bm ]] * [[ hm' c= hm ]] 
   * [[forall m lm rxm,
      m < n ->
      (forall lSm,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g (S m) lSm bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ pr | fun done' crash' bm'' hm'' => F * nocrash g m lm bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g n lfinal bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall bm'' hm'',
         F * crashed g bm'' hm'' * [[ hm' c= hm'' ]] *
         [[ bm' c= bm'' ]] =p=> crash bm'' hm'' ]])%pred
  }} Bind (ForN_ f 0 n nocrash crashed li) rx.
Proof.
  intros.
  eapply pimpl_ok2.
  apply forN_ok'.
  safecancel.
  cancel; apply pimpl_refl.
  eauto.
  eauto.
  apply H3.
  omega.
  auto.
  eapply pimpl_ok2.
  eauto.
  replace (n + 0) with n by omega; auto.
  rewrite <- H1; cancel; eauto.
  Unshelve.
  all: unfold EqDec; apply handle_eq_dec.
Qed.

Hint Extern 1 ({{_ | _}} Bind (ForN_ _ _ _ _ _ _) _) => apply forN_ok : prog.

Notation "'ForN' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' i < n 'Blockmem' bm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' i < n 'Blockmem' bm 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' x <= i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        x (n - x)
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0, x at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' x <= i < n 'Blockmem' bm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        x (n - x)
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0, x at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).


Notation "'ForN' x <= i < n 'Blockmem' bm 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        x (n - x)
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun bm hm => (nocrash)%pred)) ..))
        )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0, x at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Fixpoint ForEach_ (ITEM : Type)
                (L : Type) (G : Type) (f : ITEM -> L -> prog L)
                (lst : list ITEM)
                (nocrash : G -> list ITEM -> L -> taggedmem -> domainmem -> rawpred tagged_block)
                (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block)
                (l : L) : prog L :=
  match lst with
  | nil => Ret l
  | elem :: lst' =>
    l' <- f elem l;;
    ForEach_ f lst' nocrash crashed l'
  end.

Theorem foreach_ok:
  forall T ITEM (lst : list ITEM)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> list ITEM -> L -> taggedmem -> domainmem -> pred)
         (crashed : G -> taggedmem -> domainmem -> pred)
         (li : L) pr,
  {{ pr | fun done crash bm hm => (exists F (g:G) bm' hm', F * nocrash g lst li bm hm
   * [[ bm' c= bm ]] * [[ hm' c= hm ]] 
   * [[forall elem lst' lm rxm,
      (forall lSm,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g lst' lSm bm'' hm'' *
           [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]]  * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ pr | fun done' crash' bm'' hm'' => F * nocrash g (elem :: lst') lm bm'' hm'' *
         [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
         [[ exists prefix, prefix ++ elem :: lst' = lst ]] *
         [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f elem lm) rxm]]
   * [[forall lfinal,
       {{ pr | fun done' crash' bm'' hm'' => F * nocrash g nil lfinal bm'' hm'' *
          [[ bm' c= bm'' ]] * [[ hm' c= hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall bm'' hm'',
         F * crashed g bm'' hm'' * [[ hm' c= hm'' ]] *
         [[ bm' c= bm ]] =p=> crash bm'' hm'' ]])%pred
  }} Bind (ForEach_ f lst nocrash crashed li) rx.
Proof.
  intros ITEM.
  induction lst; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl.
      apply ret_secure'.
      intros.
      apply pimpl_refl.
    + safecancel.
      eassign (fun bm hm => nocrash a0 nil li bm hm * a)%pred.
      apply pimpl_refl.
      eapply pimpl_ok2; eauto.
      cancel; eauto.
      unfold false_pred; cancel; eauto.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      monad_simpl; apply H1.
      intros.
      eapply pimpl_ok2.
      apply IHlst.
      safecancel.
      eassign lst.
      cancel; apply pimpl_refl.
      eauto.
      eauto.
      eapply pimpl_ok2.
      apply H1.
      intros.
      auto.
      cancel; eauto.
      exists (a :: prefix); auto.
      auto.
      rewrite <- H; cancel; eauto.
    + cancel.
      eauto.
      exists nil; auto.
 Unshelve.
 all: unfold EqDec; apply handle_eq_dec.     
Qed.

Hint Extern 1 ({{_ | _}} Bind (ForEach_ _ _ _ _ _) _) => apply foreach_ok : prog.

Notation "'ForEach' elem rest lst 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun bm hm => (nocrash)%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Blockmem' bm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun bm hm => (nocrash)%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun bm hm => (nocrash)%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Blockmem' bm 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun bm hm => (nocrash)%pred)) ..))  )) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun bm hm => crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

