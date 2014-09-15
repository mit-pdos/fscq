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

Ltac inv_exec_recover :=
  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Theorem read_ok:
  forall (a:addr) (rx:valu->prog) (rec:prog),
  {{ exists v F, a |-> v * F
   * [[{{ a |-> v * F }} (rx v) >> rec]]
   * [[{{ a |-> v * F }} rec >> rec]]
  }} Read a rx >> rec.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec_recover; auto; inv_exec.
  - apply ptsto_valid in H. congruence.
  - eapply H2. eauto.
    apply ptsto_valid in H. repeat inv_option.
    eauto.
  - eapply H2. eauto.
    apply ptsto_valid in H. repeat inv_option.
    eauto.
  - eapply H1; eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Read _) _ >> _) => apply read_ok : prog.

(* write_ok' : start with a in domain of m and (diskIs m), end with (diskIs (upd m a v)) *)

Theorem write_ok:
  forall (a:addr) (v:valu) (rx:unit->prog) (rec:prog),
  {{ exists v0 F, a |-> v0 * F
   * [[{{ a |-> v * F }} rx tt >> rec]]
   * [[{{ a |-> v * F \/ a |-> v0 * F }} rec >> rec]]
  }} Write a v rx >> rec.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec_recover; auto; inv_exec.
  - apply ptsto_valid in H. congruence.
  - eapply H2. instantiate (1:=upd m a v).
    eapply ptsto_upd; eauto.
    eauto.
  - eapply H2. instantiate (1:=upd m a v).
    eapply ptsto_upd; eauto.
    eauto.
  - eapply H1; unfold or; eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Write _ _) _ >> _) => apply write_ok : prog.

Definition If_ P Q (b : {P} + {Q}) (p1 p2 : prog) :=
  if b then p1 else p2.

Theorem if_ok:
  forall P Q (b : {P}+{Q}) p1 p2 rec,
  {{ exists pre, pre
   * [[{{ pre * [[P]] }} p1 >> rec]]
   * [[{{ pre * [[Q]] }} p2 >> rec]]
  }} If_ b p1 p2 >> rec.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  destruct b.
  - eapply H2; eauto.
    eapply pimpl_apply; [|apply H].
    apply sep_star_lift_r.
    split; pred.
  - eapply H1; eauto.
    eapply pimpl_apply; [|apply H].
    apply sep_star_lift_r.
    split; pred.
Qed.

Hint Extern 1 ({{_}} If_ _ _ _ >> _) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

Fixpoint For_ (L : Set) (G : Type) (f : nat -> L -> (L -> prog) -> prog)
              (i n : nat) (l : L)
              (nocrash : G -> nat -> L -> pred)
              (crashed : G -> pred)
              (rx: L -> prog) : prog :=
  match n with
    | O => rx l
    | S n' => l' <- (f i l); (For_ f (S i) n' l' nocrash crashed rx)
  end.

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

Definition For_loop (L : Set) (G : Type) (f : addr -> L -> (L -> prog) -> prog)
                    (i n : addr) (l : L)
                    (nocrash : G -> addr -> L -> pred)
                    (crashed : G -> pred)
                    (rx: L -> prog)
                    : prog.
  refine (Fix (@for_args_wf L) (fun _ => prog)
          (fun args For_loop => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 (natToWord addrlen 0) then rx For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0); _).
  refine (For_loop {| For_args_i := For_args_i0 ^+ (natToWord addrlen 1);
                      For_args_n := For_args_n0 ^- (natToWord addrlen 1);
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

Lemma For_loop_step: forall L G f i n l nocrash crashed rx,
  @For_loop L G f i n l nocrash crashed rx =
    if weq n (natToWord addrlen 0)
    then rx l
    else l' <- (f i l);
         @For_loop L G f
                   (i ^+ (natToWord addrlen 1))
                   (n ^- (natToWord addrlen 1))
                   l' nocrash crashed rx.
Proof.
  intros.
  unfold For_loop.
  rewrite Fix_eq.

  destruct (weq n (natToWord addrlen 0)); f_equal.

  intros.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; f_equal
  end.
  apply functional_extensionality; auto.
Qed.

Theorem word_for_ok:
  forall (n i : addr)
         (L : Set) (G : Type)
         f rx rec (nocrash : G -> addr -> L -> pred) (crashed : G -> pred)
         (li : L),
  {{ exists F (g:G), F * nocrash g i li
   * [[forall m l, F * nocrash g m l ==> F * crashed g]]
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm, {{ F * nocrash g (m ^+ (natToWord addrlen 1)) lSm }} (rxm lSm) >> rec) ->
      {{ F * nocrash g m lm }} f m lm rxm >> rec]]
   * [[forall lfinal, {{ F * nocrash g (n ^+ i) lfinal }} (rx lfinal) >> rec]]
  }} (For_loop f i n li nocrash crashed rx) >> rec.
Proof.
  match goal with
  | [ |- forall (n: addr), ?P ] =>
    refine (well_founded_ind (@wlt_wf addrlen) (fun n => P) _)
  end.

  intros.
  apply corr_exists; intros.
  apply corr_exists; intros.
  case_eq (weq x (natToWord addrlen 0)); intros; subst.

  - eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_loop_step.
      apply H1.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). auto.

  - eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_loop_step.
      rewrite H0.
      apply H2.

      apply eq_le; auto.
      (* XXX i < x ^+ i: need something to prove non-overflow? *)
      admit.

      intros.
      eapply pimpl_ok.
      apply H.

      (* XXX [x ^- natToWord addrlen 1 < x] given [x <> natToWord addrlen 0] *)
      admit.
      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      repeat ( apply sep_star_lift_r; apply pimpl_and_split );
        unfold pimpl, lift; intuition eauto.

      apply H2; eauto.
      (* XXX *)
      admit.
      (* XXX *)
      admit.

      ring_simplify (x ^- natToWord addrlen 1 ^+ (i ^+ natToWord addrlen 1)).
      eauto.
    + auto.
Qed.

Theorem for_ok:
  forall (L : Set) (G : Type)
         f rx rec (nocrash : G -> nat -> L -> pred) (crashed : G -> pred)
         n i (li : L),
  {{ exists F (g:G), F * nocrash g i li
   * [[forall m l, F * nocrash g m l ==> F * crashed g]]
   * [[forall m lm rxm,
      i <= m < n + i ->
      (forall lSm, {{ F * nocrash g (S m) lSm }} (rxm lSm) >> rec) ->
      {{ F * nocrash g m lm }} f m lm rxm >> rec]]
   * [[forall lfinal, {{ F * nocrash g (n+i) lfinal }} (rx lfinal) >> rec]]
  }} (For_ f i n li nocrash crashed rx) >> rec.
Proof.
  induction n.
  - intros.
    apply corr_exists; intros.
    apply corr_exists; intros.
    eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl; intuition pred.
    + unfold pimpl; pred.
  - intros.
    apply corr_exists; intros.
    apply corr_exists; intros.
    eapply pimpl_pre; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl; intuition idtac.
      eapply H0; try omega.
      intros.
      eapply pimpl_ok.
      apply IHn.
      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      repeat ( apply sep_star_lift_r; apply pimpl_and_split );
        unfold pimpl, lift; intuition eauto.
      apply H0; eauto; omega.
      replace (n + S i) with (S (n + i)) by omega; eauto.
    + unfold pimpl; pred.
Qed.

Hint Extern 1 ({{_}} progseq (For_ _ _ _ _ _ _) _ >> _) => apply for_ok : prog.
Notation "'For' i < n 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        0 n l0
        (fun (_:unit) i l => nocrash%pred)
        (fun (_:unit) => crashed%pred))
  (at level 9, i at level 0, n at level 0, lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).

Notation "'For' i < n 'Ghost' g1 .. g2 'Loopvar' l <- l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        0 n l0
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

Theorem read_array_ok : forall a rx rec,
  {{ exists m v F, diskIs m * F * [[ m @ a |-> v ]]
   * [[ {{ diskIs m * F }} rx v >> rec ]]
   * [[ {{ diskIs m * F }} rec >> rec ]]
  }} read_array a rx >> rec.
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

Theorem write_array_ok : forall a v rx rec,
  {{ exists m F, diskIs m * F * [[ indomain a m ]]
   * [[ {{ diskIs (upd m a v) * F }} rx tt >> rec ]]
   * [[ {{ diskIs m * F
        \/ diskIs (upd m a v) * F }} rec >> rec ]]
  }} write_array a v rx >> rec.
Proof.
  unfold write_array, indomain.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq (read_array _) _ >> _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} progseq (write_array _ _) _ >> _) => apply write_array_ok : prog.
