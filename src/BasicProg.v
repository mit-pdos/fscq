Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.

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

(*
Ltac inv_exec_recover :=
  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.
*)

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Theorem read_ok:
  forall (a:addr) (rx:valu->prog),
  {{ fun done crash => exists v F, a |-> v * F
   * [[ {{ fun done' crash' => a |-> v * F
         * [[ done' = done ]] * [[ crash' = crash ]] }} rx v ]]
   * [[ a |-> v * F ==> crash ]]
  }} Read a rx.
Proof.
  unfold corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec.
  - apply ptsto_valid in H. congruence.
  - eapply H2. repeat ( apply sep_star_and2lift; split; unfold lift; eauto ).
    apply ptsto_valid in H. repeat inv_option.
    eauto.
  - right. eexists; intuition eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Read _) _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu) (rx:unit->prog),
  {{ fun done crash => exists v0 F, a |-> v0 * F
   * [[ {{ fun done' crash' => a |-> v * F
         * [[ done' = done ]] * [[ crash' = crash ]] }} rx tt ]]
   * [[ a |-> v0 * F ==> crash ]]
  }} Write a v rx.
Proof.
  unfold corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec.
  - apply ptsto_valid in H. congruence.
  - eapply H2. instantiate (1:=upd m a v).
    repeat ( apply sep_star_and2lift; split; unfold lift; eauto ).
    eapply ptsto_upd; eauto.
    eauto.
  - right. eexists; intuition eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Write _ _) _) => apply write_ok : prog.

Definition If_ P Q (b : {P} + {Q}) (p1 p2 : prog) :=
  if b then p1 else p2.

Theorem if_ok:
  forall P Q (b : {P}+{Q}) p1 p2,
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

Record For_args (L : Set) := {
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

Definition For_ (L : Set) (G : Type) (f : addr -> L -> (L -> prog) -> prog)
                (i n : addr) (l : L)
                (nocrash : G -> addr -> L -> pred)
                (crashed : G -> pred)
                (rx: L -> prog) : prog.
  refine (Fix (@for_args_wf L) (fun _ => prog)
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
    [| assert (wordToNat For_args_n0 < pow2 addrlen) by apply wordToNat_bound; omega ].
  apply PeanoNat.Nat.sub_lt; omega.

  unfold wlt, not in *; intro Hn.
  apply H.
  apply Nlt_out in Hn.
  repeat rewrite wordToN_nat in Hn.
  repeat rewrite Nat2N.id in Hn.
  simpl in Hn.
  omega.
Defined.

Lemma For_step: forall L G f i n l nocrash crashed rx,
  @For_ L G f i n l nocrash crashed rx =
    if weq n $0
    then rx l
    else l' <- (f i l);
         @For_ L G f
               (i ^+ $1)
               (n ^- $1)
               l' nocrash crashed rx.
Proof.
  intros.
  unfold For_.
  rewrite Fix_eq.

  destruct (weq n $0); f_equal.

  intros.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; f_equal
  end.
  apply functional_extensionality; auto.
Qed.

Theorem for_ok':
  forall (n i : addr)
         (L : Set) (G : Type)
         f rx
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
   * [[F * crashed g ==> crash]]
  }} (For_ f i n li nocrash crashed rx).
Proof.
  match goal with
  | [ |- forall (n: addr), ?P ] =>
    refine (well_founded_ind (@wlt_wf addrlen) (fun n => P) _)
  end.

  intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  case_eq (weq x $0); intros; subst.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_step.
      eapply pimpl_ok2.
      simpl; eauto.
      instantiate (1:=(fun _ _ => a * nocrash a0 ($ (0) ^+ i) li)%pred).
      intros; simpl.
      cancel.
      (* XXX something wrong with the done'=done requirements *)
Admitted.

(*
      eapply H3.
      apply H1.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). cancel.

  - eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
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
      eapply pimpl_ok.
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

      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      cancel.

      apply H4; eauto.
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

      unfold not; intros; apply H5.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H9; simpl in H9; auto.
    + cancel.
Qed.
*)

Theorem for_ok:
  forall (n : addr)
         (L : Set) (G : Type)
         f rx
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
   * [[F * crashed g ==> crash]]
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

Definition read_array a rx :=
  v <- Read a;
  rx v.

Local Hint Extern 1 (diskIs ?m =!=> _) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match R with
    | context[(?a |-> ?v)%pred] =>
      apply diskIs_split; eauto
    end
  end : norm_hint_left.

Local Hint Extern 1 (_ =!=> diskIs ?m) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match L with
    | context[(?a |-> ?v)%pred] =>
      match L with
      | context[diskIs (mem_except m a)] =>
        apply diskIs_merge_except; eauto
      end
    end
  end : norm_hint_right.

Theorem read_array_ok : forall a rx,
  {{ fun done crash => exists m v F, diskIs m * F * [[ m @ a |-> v ]]
   * [[ {{ fun done' crash' => diskIs m * F * [[ done' = done ]] * [[ crash' = crash ]] }} rx v ]]
   * [[ diskIs m * F ==> crash ]]
  }} read_array a rx.
Proof.
  unfold read_array.
  hoare.
Qed.

Definition write_array a v rx :=
  Write a v ;;
  rx tt.

Local Hint Extern 1 (_ =!=> diskIs (upd ?m ?a ?v)) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match L with
    | context[(?a |-> ?v')%pred] =>
      match L with
      | context[diskIs (mem_except m a)] =>
        apply diskIs_merge_upd; eauto
      end
    end
  end : norm_hint_right.

Theorem write_array_ok : forall a v rx,
  {{ fun done crash => exists m F, diskIs m * F * [[ indomain a m ]]
   * [[ {{ fun done' crash' => diskIs (upd m a v) * F
      * [[ done' = done ]] * [[ crash' = crash ]] }} rx tt ]]
   * [[ diskIs m * F \/ diskIs (upd m a v) * F ==> crash ]]
  }} write_array a v rx.
Proof.
  unfold write_array, indomain.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq (read_array _) _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} progseq (write_array _ _) _) => apply write_array_ok : prog.
