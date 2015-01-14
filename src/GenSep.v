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


