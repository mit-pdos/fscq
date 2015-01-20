Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Omega.
Require Import Ring.
Require Import SepAuto.

Set Implicit Arguments.

(**
 * This module is meant to generalize separation logic to arbitrary functions
 * from some address-like thing to some value-like thing.  The motivating use
 * case is in files: we want to think of the disk as a mapping from inode numbers
 * to file objects, where each file object includes metadata and the entire file
 * contents.  Current separation logic is not quite good enough, because we want
 * to have values that are bigger than a 512-byte block.
 *)

(**
 * list2mem is meant to convert a list representation of files into a memory-like
 * object that maps inode numbers (list positions) into files (or None, if the
 * inode number is too big).  For now, this always uses [addr] as the index.
 *)
Definition list2mem (A: Type) (l: list A) : (addr -> option A) :=
  fun a => sel (map (@Some A) l) a None.

Theorem list2mem_ptsto_bounds: forall A F (l: list A) i x,
  (F * i |-> x)%pred (list2mem l) -> wordToNat i < length l.
Proof.
  intros.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  destruct (lt_dec (wordToNat i) (length l)); auto.
  unfold sel in H. rewrite nth_selN_eq in H.
  rewrite nth_overflow in H by (rewrite map_length; omega); discriminate.
Qed.


Theorem list2mem_oob : forall A (l : list A) i,
  wordToNat i >= length l
  -> (list2mem l) i = None.
Proof.
  unfold list2mem; intros.
  unfold sel; rewrite selN_oob; auto.
  rewrite map_length; auto.
Qed.


Theorem list2mem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2mem l)
  -> wordToNat i < length l.
Proof.
  intros.
  destruct (lt_dec (wordToNat i) (length l)); auto; exfalso.
  apply not_lt in n.
  apply list2mem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.


Theorem list2mem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2mem l)
  -> x = sel l i def.
Proof.
  intros.
  assert (wordToNat i < length l).
  eapply list2mem_inbound; eauto.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  erewrite sel_map in H by auto.
  inversion H; eauto.
Qed.


Lemma listupd_progupd: forall A l i (v : A),
  wordToNat i < length l
  -> list2mem (upd l i v) = Prog.upd (list2mem l) i v.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, sel, upd, Prog.upd.
  autorewrite with core.

  destruct (addr_eq_dec x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.
  erewrite selN_updN_ne; auto.
  word2nat_simpl; omega.
Qed.

Theorem list2mem_upd: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2mem l)
  -> (F * i |-> y)%pred (list2mem (upd l i y)).
Proof.
  intros.
  rewrite listupd_progupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2mem_inbound; eauto.
Qed.


Theorem listapp_progupd: forall A l (a : A) (b : addr),
  length l <= wordToNat b
  -> list2mem (l ++ a :: nil) = Prog.upd (list2mem l) $ (length l) a.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, sel, upd, Prog.upd.

  destruct (wlt_dec x $ (length l)).
  - apply wlt_lt in w.
    erewrite wordToNat_natToWord_bound in w; eauto.
    subst; rewrite selN_map with (default' := a).
    destruct (addr_eq_dec x $ (length l)); subst.
    + erewrite wordToNat_natToWord_bound in *; eauto.
      rewrite selN_last; auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
    + rewrite app_length; simpl; omega.
  - destruct (addr_eq_dec x $ (length l)).
    + subst; erewrite selN_map with (default' := a).
      rewrite selN_last; auto.
      eapply wordToNat_natToWord_bound; eauto.
      erewrite wordToNat_natToWord_bound; eauto.
      rewrite app_length; simpl; omega.
    + apply wle_le in n.
      erewrite wordToNat_natToWord_bound in n; eauto.
      repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      rewrite app_length; simpl; intuition.
      rewrite Nat.add_1_r; apply lt_le_S.
      apply le_lt_or_eq in n; intuition.
      contradict n0; rewrite H0.
      apply wordToNat_inj.
      erewrite wordToNat_natToWord_bound; eauto.
Qed.


Theorem list2mem_app: forall A (F : @pred A) l a (b : addr),
  length l <= wordToNat b
  -> F (list2mem l)
  -> (F * $ (length l) |-> a)%pred (list2mem (l ++ a :: nil)).
Proof.
  intros.
  erewrite listapp_progupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2mem, sel.
  rewrite selN_oob; auto.
  rewrite map_length.
  erewrite wordToNat_natToWord_bound; eauto.
Qed.


Theorem list2mem_removelast_is : forall A l (def : A) (b : addr),
  l <> nil -> length l <= wordToNat b
  -> list2mem (removelast l) =
     fun i => if (wlt_dec i $ (length l - 1)) then Some (sel l i def) else None.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (wlt_dec x $ (length l - 1)); unfold list2mem, sel.
  - assert (wordToNat x < length l - 1); apply wlt_lt in w.
    erewrite wordToNat_natToWord_bound with (bound:=b) in w by omega; auto.
    rewrite selN_map with (default' := def).
    rewrite selN_removelast by omega; auto.
    rewrite length_removelast by auto; omega.
  - rewrite selN_oob; auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    apply wle_le in n.
    rewrite wordToNat_natToWord_bound with (bound:=b) in n by omega; auto.
Qed.


Theorem list2mem_removelast_list2mem : forall A (l : list A) (def : A) (b : addr),
  l <> nil -> length l <= wordToNat b
  -> list2mem (removelast l) =
     fun i => if (weq i $ (length l - 1)) then None else (list2mem l) i.
Proof.
  intros; apply functional_extensionality; intros.
  erewrite list2mem_removelast_is with (def := def) by eauto.
  unfold list2mem, sel.
  destruct (wlt_dec x $ (length l - 1));
  destruct (weq x $ (length l - 1)); subst; intuition.
  apply wlt_lt in w; omega.
  erewrite selN_map with (default' := def); auto.
  apply wlt_lt in w; rewrite wordToNat_natToWord_bound with (bound:=b) in w by omega; omega.
  erewrite selN_oob; auto.
  rewrite map_length.
  assert ($ (length l - 1) < x)%word.
  destruct (weq $ (length l - 1) x); intuition.
  apply wlt_lt in H1; rewrite wordToNat_natToWord_bound with (bound:=b) in H1 by omega; omega.
Qed.


Lemma mem_disjoint_either: forall V (m1 m2 : @mem V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
Proof.
  unfold mem_disjoint; intros; firstorder.
  pose proof (H a); firstorder.
  pose proof (H1 v); firstorder.
  destruct (m2 a); auto.
  pose proof (H2 v0); firstorder.
Qed.


Theorem list2mem_removelast: forall A F (l : list A) v (b : addr),
  l <> nil -> length l <= wordToNat b
  -> (F * $ (length l - 1) |-> v)%pred (list2mem l)
  -> F (list2mem (removelast l)).
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (x = list2mem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2mem_removelast_list2mem with (b:=b); auto.

  destruct (weq x1 $ (length l - 1)); subst.
  apply mem_disjoint_comm in H1. 
  eapply mem_disjoint_either; eauto.

  rewrite H2; unfold mem_union.
  destruct (x x1); subst; simpl; auto.
  apply eq_sym; apply H6; auto.
Qed.


Theorem list2mem_array: forall  A (l : list A) (b : addr),
  length l <= wordToNat b
  -> array $0 l $1 (list2mem l).
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  rewrite app_length in H; simpl in H.
  erewrite listapp_progupd with (b := b); try omega.
  eapply array_app_progupd with (b := b); try omega.
  apply IHl with (b := b); omega.
Qed.


Theorem list2mem_array_eq: forall A (l' l : list A) (b : addr),
  length l <= wordToNat b -> length l = length l'
  -> array $0 l $1 (list2mem l')
  -> l = l'.
Proof.
  induction l' using rev_ind; destruct l using rev_ind;
  intros; firstorder; repeat rewrite app_length in *; simpl in *.
  contradict H0; omega.
  contradict H0; omega.
  rewrite IHl' with (l := l) (b := b); try omega.

  repeat f_equal.
  assert (exists F, (F * $ (length l) |-> x0)%pred (list2mem (l' ++ x :: nil))).
  pred_apply; eapply isolate_last with (b:=b); omega.
  destruct H2.
  eapply list2mem_sel with (def := x) in H2; eauto.
  unfold sel in H2; rewrite selN_last in H2; auto.
  rewrite wordToNat_natToWord_bound with (bound:=b); omega.

  replace l' with (removelast (l' ++ x :: nil)).
  eapply list2mem_removelast with (b := b) (v := x0).
  firstorder.
  rewrite app_length; simpl; omega.
  pred_apply; cancel. 
  erewrite isolate_last with (b:=b) by try omega.
  rewrite app_length; simpl.
  replace (length l' + 1 - 1) with (length l) by omega.
  cancel.
  rewrite removelast_app; simpl; firstorder.
Qed.



Ltac list2mem_cancel' t := match goal with
  [ |- (_ * ?p |-> ?a)%pred (list2mem ?l) ] =>
    assert (array $0 l $1 (list2mem l)); 
    [ eapply list2mem_array; t |
      pred_apply; rewrite isolate_fwd with (i := p);
      try autorewrite with defaults;
      [ cancel | t ] ]
end.

Ltac list2mem_cancel := list2mem_cancel' idtac.



