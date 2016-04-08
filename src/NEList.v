Require Import Arith.
Require Import Omega.
Require Import Bool.
Require Import List.
Require Import ListUtils.
Require Import Word.

Import ListNotations.

Set Implicit Arguments.


Section NonEmptyList.

  Variable T : Type.

  Definition nelist  := (T * list T)%type.

  Definition singular x : nelist := (x, nil).

  Definition latest (ds : nelist) := hd (fst ds) (snd ds).

  Definition latest_cons : forall d0 d ds, latest (d0, d :: ds) = d.
  Proof.
    firstorder.
  Qed.

  (* return the n-th disk in the diskset *)
  Definition nthd n (ds : nelist) := selN (snd ds) (length (snd ds) - n) (fst ds).

  Lemma nthd_0 : forall ds, nthd 0 ds = fst ds.
  Proof.
    unfold nthd; intros; rewrite selN_oob; auto; omega.
  Qed.

  Lemma nthd_oob : forall ds n, n >= length (snd ds) -> nthd n ds = latest ds.
  Proof.
    unfold nthd, latest; intros; destruct ds; simpl in *.
    replace (length l - n) with 0 by omega.
    destruct l; firstorder.
  Qed.

  (* append a new diskstate to a diskset *)
  Definition pushd (d : T) (ds : nelist) : nelist :=
      (fst ds, d :: snd ds).

  (* pop out n oldest disks for a diskset *)
  Definition popn (n : nat) (ds : nelist) : nelist :=
      (nthd n ds, cuttail n (snd ds)).

  Lemma popn_0 : forall ds,
    popn 0 ds = ds.
  Proof.
    unfold popn; intros.
    rewrite nthd_0, cuttail_0.
    rewrite surjective_pairing; auto.
  Qed.

  Lemma popn_oob : forall ds n,
    n >= length (snd ds) -> popn n ds = (latest ds, nil).
  Proof.
    unfold popn; intros.
    rewrite nthd_oob by omega.
    rewrite cuttail_oob by omega; auto.
  Qed.

  Lemma singular_latest : forall ds, snd ds = nil -> latest ds = fst ds.
  Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.

  Lemma singular_nthd : forall ds n, snd ds = nil -> nthd n ds = fst ds.
  Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.

  Lemma popn_oob_singular' : forall ds n,
    n >= length (snd ds) -> snd (popn n ds) = nil.
  Proof.
    unfold popn; intros.
    rewrite cuttail_oob by omega; auto.
  Qed.

  Lemma popn_oob_singular : forall ds n,
    n >= length (snd ds) -> popn n ds = singular (latest ds).
  Proof.
    unfold popn, singular; intros.
    rewrite cuttail_oob by omega.
    rewrite nthd_oob; auto.
  Qed.


  Lemma popn_popn : forall ds m n,
    popn m (popn n ds) = popn (n + m) ds.
  Proof.
    unfold popn; intros; simpl.
    rewrite cuttail_cuttail; f_equal.
    unfold nthd; simpl.
    rewrite cuttail_length.
    destruct (le_dec n (length (snd ds))).
    replace (length (snd ds) - (n + m)) with (length (snd ds) - n - m) by omega.
    unfold cuttail.
    destruct (lt_dec (length (snd ds) - n - m) (length (snd ds) - n)).
    rewrite selN_firstn at 1; auto.
    apply selN_inb; omega.
    rewrite selN_oob.
    f_equal; omega.
    rewrite firstn_length; apply Nat.min_case_strong; omega.
    rewrite cuttail_oob by omega.
    simpl; f_equal; omega.
  Qed.


  Lemma popn_tail : forall n d0 d ds,
    popn (S n) (d0, ds ++ [d]) = popn n (d, ds).
  Proof.
    intros.
    replace (S n) with (1 + n) by omega.
    rewrite <- popn_popn.
    unfold popn at 2; simpl.
    rewrite cuttail_tail, cuttail_0.
    unfold nthd; simpl.
    rewrite app_length; simpl.
    rewrite selN_app2 by omega.
    replace (length ds + 1 - 1 - length ds) with 0 by omega; simpl; auto.
  Qed.

End NonEmptyList.


Notation " ds '!!'" := (latest ds) (at level 1).

