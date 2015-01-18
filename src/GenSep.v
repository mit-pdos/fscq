Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Omega.

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


Theorem list2mem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2mem l)
  -> wordToNat i < length l
  -> x = sel l i def.
Proof.
  intros.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  erewrite sel_map in H by auto.
  inversion H.
  eauto.
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
  wordToNat i < length l
  -> (F * i |-> x)%pred (list2mem l)
  -> (F * i |-> y)%pred (list2mem (upd l i y)).
Proof.
  intros.
  rewrite listupd_progupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H0.
  eapply ptsto_upd; eauto.
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


Theorem list2mem_removelast: forall A F (l : list A),
  l <> nil
  -> (F * $ (length l - 1) |->?)%pred (list2mem l)
  -> F (list2mem (removelast l)).
Proof.
  admit.
Qed.



