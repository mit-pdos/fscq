Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import List.

Set Implicit Arguments.


(** * Some helpful [prog] combinators and proofs *)

Ltac inv_option :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H; subst
  | [ H: ?a = Some ?b |- _ ] =>
    match goal with
    | [ H': a = Some ?c |- _ ] =>
      match b with
      | c => fail 1
      | _ => rewrite H in H'
      end
    end
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Theorem read_ok:
  forall (a:addr),
  {< v,
  PRE    a |-> v
  POST:r a |-> v * [[ r = (fst v) ]]
  CRASH  a |-> v
  >} Read a.
Proof.
  unfold corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec.
  - apply sep_star_comm in H; apply ptsto_valid in H.
    repeat deex.
    congruence.
  - eapply H2. repeat ( apply sep_star_and2lift; split; unfold lift; eauto ).
    apply sep_star_assoc. apply sep_star_and2lift; split; unfold lift; eauto.
    apply sep_star_comm in H; apply ptsto_valid in H.
    repeat deex.
    repeat inv_option. eauto.
  - right. eexists; intuition eauto.
Qed.
Check read_ok.
Hint Extern 1 ({{_}} progseq (Read _) _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu),
  {< v0,
  PRE    a |-> v0
  POST:r a |-> (v, valuset_list v0)
  CRASH  a |-> v0
  >} Write a v.
Proof.
  unfold corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec.
  - apply sep_star_comm in H; apply ptsto_valid in H.
    repeat deex.
    congruence.
  - eapply H2; eauto.
    repeat ( apply sep_star_and2lift; split; unfold lift; eauto ).
    apply sep_star_comm. apply sep_star_comm in H.
    apply ptsto_valid in H as H'.
    rewrite H' in H8. inversion H8; subst.
    eapply pimpl_trans; [ apply pimpl_refl | | ].
    apply pimpl_sep_star; [ | apply pimpl_refl ].
    unfold valuset_list; simpl.
    apply pimpl_refl.
    eapply ptsto_upd.
    eauto.
  - right. eexists; intuition eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Write _ _) _) => apply write_ok : prog.

Theorem sync_ok:
  forall (a:addr),
  {< v,
  PRE    a |-> v
  POST:r a |-> (fst v, nil)
  CRASH  a |-> v
  >} Sync a.
Proof.
  unfold corr2, exis; intros; repeat deex.
  destruct_lift H.
  inv_exec.
  - apply sep_star_comm in H; apply ptsto_valid in H.
    repeat deex.
    congruence.
  - eapply H4; eauto.
    apply sep_star_and2lift; split; firstorder.
    apply sep_star_and2lift; split; firstorder.
    apply sep_star_comm.

    apply sep_star_comm in H as H'.
    apply ptsto_valid in H'.
    rewrite H' in H6.
    inversion H6; simpl in *; subst.

    eapply ptsto_upd.
    apply sep_star_comm.
    eauto.
  - right. eexists; intuition eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Sync _) _) => apply sync_ok : prog.

Definition If_ T P Q (b : {P} + {Q}) (p1 p2 : prog T) :=
  if b then p1 else p2.

Theorem if_ok:
  forall T P Q (b : {P}+{Q}) (p1 p2 : prog T),
  {{ fun done crash => exists pre, pre
   * [[ {{ fun done' crash' => pre * [[P]] * [[ done' = done ]] * [[ crash' = crash ]] }} p1 ]]
   * [[ {{ fun done' crash' => pre * [[Q]] * [[ done' = done ]] * [[ crash' = crash ]] }} p2 ]]
  }} If_ b p1 p2.
Proof.
  unfold corr2, exis; intros; repeat deex.
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
  {{ fun done crash => exists pre, pre
   * [[ {{ fun done' crash' => pre * [[P]] * [[ done' = done ]] * [[ crash' = crash ]] }} p1 rx ]]
   * [[ {{ fun done' crash' => pre * [[Q]] * [[ done' = done ]] * [[ crash' = crash ]] }} p2 rx ]]
  }} IfRx_ b p1 p2 rx.
Proof.
  unfold IfRx_; intros.
  apply if_ok.
Qed.

Hint Extern 1 ({{_}} IfRx_ _ _ _) => apply ifrx_ok : prog.
Notation "'IfRx' rx b { p1 } 'else' { p2 }" :=
  (IfRx_ b (fun rx => p1) (fun rx => p2)) (at level 9, rx at level 0, b at level 0).

Record For_args (L : Type) := {
  For_args_i : addr;
  For_args_n : addr;
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
                (L : Type) (G : Type) (f : addr -> L -> (L -> prog T) -> prog T)
                (i n : addr) (l : L)
                (nocrash : G -> addr -> L -> @pred addr (@weq addrlen) valuset)
                (crashed : G -> @pred addr (@weq addrlen) valuset)
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
  @For_ T L G f i n l nocrash crashed rx =
    if weq n $0
    then rx l
    else l' <- (f i l);
         @For_ T L G f
               (i ^+ $1)
               (n ^- $1)
               l' nocrash crashed rx.
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
  forall T (n i : addr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> addr -> L -> pred)
         (crashed : G -> pred)
         (li : L),
  {{ fun done crash => exists F (g:G), F * nocrash g i li
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm,
       {{ fun done' crash' => F * nocrash g (m ^+ $1) lSm * [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun done' crash' => F * nocrash g m lm * [[ done' = done ]] * [[ crash' = crash ]]
      }} f m lm rxm]]
   * [[forall lfinal,
       {{ fun done' crash' => F * nocrash g (n ^+ i) lfinal * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]]
   * [[F * crashed g =p=> crash]]
  }} (For_ f i n li nocrash crashed rx).
Proof.
  intro T.
  wlt_ind.

  intros.
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
      rewrite <- H5; rewrite natToWord_wordToNat; auto.

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
      apply wlt_lt in H7; simpl in H7.
      rewrite <- natToWord_wordToNat with (w:=x).
      f_equal.
      omega.

      intros.
      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      cancel.

      subst; apply H4; eauto.
      intros; apply H7; clear H7.
      apply wlt_lt in H9.
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

      subst; eauto.

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

      unfold not; intros; apply H5.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H7; simpl in H7; auto.
      subst; auto.
    + cancel.
Qed.

Theorem for_ok:
  forall T (n : addr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> addr -> L -> pred)
         (crashed : G -> pred)
         (li : L),
  {{ fun done crash => exists F (g:G), F * nocrash g $0 li
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm,
       {{ fun done' crash' => F * nocrash g (m ^+ $1) lSm * [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun done' crash' => F * nocrash g m lm * [[ done' = done ]] * [[ crash' = crash ]]
      }} f m lm rxm]]
   * [[forall lfinal,
       {{ fun done' crash' => F * nocrash g n lfinal * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[F * crashed g =p=> crash]]
  }} For_ f $0 n li nocrash crashed rx.
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
Notation "'For' i < n 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        $0 n l0
        (fun (_:unit) i l => nocrash%pred)
        (fun (_:unit) => crashed%pred))
  (at level 9, i at level 0, n at level 0, lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).

Notation "'For' i < n 'Ghost' g1 .. g2 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        $0 n l0
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i l => nocrash%pred)) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 binder, g2 binder,
   lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).


Fixpoint ForEach_ (T: Type) (ITEM : Type)
                (L : Type) (G : Type) (f : ITEM -> L -> (L -> prog T) -> prog T)
                (lst : list ITEM) (l : L)
                (nocrash : G -> list ITEM -> L -> @pred addr (@weq addrlen) valuset)
                (crashed : G -> @pred addr (@weq addrlen) valuset)
                (rx: L -> prog T) : prog T :=
  match lst with
  | nil => rx l
  | elem :: lst' =>
    l' <- f elem l;
    ForEach_ f lst' l' nocrash crashed rx
  end.

Theorem foreach_ok:
  forall T ITEM (lst : list ITEM)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> list ITEM -> L -> pred)
         (crashed : G -> pred)
         (li : L),
  {{ fun done crash => exists F (g:G), F * nocrash g lst li
   * [[forall elem lst' lm rxm,
      (forall lSm,
       {{ fun done' crash' => F * nocrash g lst' lSm * [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun done' crash' => F * nocrash g (elem :: lst') lm * [[ done' = done ]] * [[ crash' = crash ]]
      }} f elem lm rxm]]
   * [[forall lfinal,
       {{ fun done' crash' => F * nocrash g nil lfinal * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[F * crashed g =p=> crash]]
  }} ForEach_ f lst li nocrash crashed rx.
Proof.
  intros T ITEM.
  induction lst; intros;
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
      instantiate (lst' := lst).
      instantiate (a0 := a1).
      cancel.
      eapply pimpl_ok2.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply H3.
      cancel.
      cancel.
      eapply pimpl_ok2.
      apply H0.
      cancel.
      cancel.

      intros.
      apply pimpl_refl.
    + cancel.
Qed.

Hint Extern 1 ({{_}} progseq (ForEach_ _ _ _ _ _) _) => apply foreach_ok : prog.
Notation "'ForEach' elem rest lst 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem l lrx => body)
        lst l0
        (fun (_:unit) rest l => nocrash%pred)
        (fun (_:unit) => crashed%pred))
  (at level 9, elem at level 0, lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).

Notation "'ForEach' elem rest lst 'Ghost' g1 .. g2 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem l lrx => body)
        lst l0
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest l => nocrash%pred)) .. ))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         crashed%pred)) .. )))
  (at level 9, elem at level 0, rest at level 0,
   g1 binder, g2 binder,
   lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).
