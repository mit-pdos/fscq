Require Import Arith.
Require Import Omega.
Require Import Bool.
Require Import List.
Require Import ListUtils.
Require Import Word.

Import ListNotations.

Set Implicit Arguments.



Section ListRevSel.

  Variable T : Type.
  Variable l : (list T).

  Definition selR n def :=
    if lt_dec n (length l) then selN l (length l - n - 1) def else def.

  Lemma selR_oob : forall n def,
    n >= length l -> selR n def = def.
  Proof.
    unfold selR; intros.
    destruct (lt_dec n (length l)); try omega; auto.
  Qed.

  Lemma selR_inb : forall n def,
    n < length l -> selR n def = selN l (length l - n - 1) def.
  Proof.
    unfold selR; intros.
    destruct (lt_dec n (length l)); auto; congruence.
  Qed.

End ListRevSel.



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

  Fixpoint pushdlist (dlist : list T) (ds : nelist) : nelist :=
      match dlist with
      | nil => ds
      | d :: dlist' => pushdlist dlist' (pushd d ds)
      end.
  

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

  Lemma pushdlist_app : forall d l' l,
    pushdlist l' (d, l) = (d, (rev l') ++ l)%list.
  Proof.
    induction l'; simpl; unfold pushd; simpl; intros; auto.
    rewrite IHl'.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  Definition d_in d (l : nelist) := d = fst l \/ In d (snd l).

  Theorem d_in_pushdlist : forall dlist ds d,
    d_in d (pushdlist dlist ds) ->
    In d dlist \/ d_in d ds.
  Proof.
    induction dlist; simpl; intros; auto.
    edestruct (IHdlist _ _ H).
    intuition.
    destruct ds.
    inversion H0; simpl in *.
    right. left. eauto.
    intuition.
    right. right. eauto.
  Qed.

  Theorem d_in_app : forall d a l1 l2,
    d_in d (a, (l1 ++ l2)) ->
    In d l1 \/ d_in d (a, l2).
  Proof.
    intros.
    assert (In d (rev l1) \/ d_in d (a, l2)).
    apply d_in_pushdlist.
    rewrite pushdlist_app. rewrite rev_involutive. eauto.
    intuition.
    left. apply in_rev. eauto.
  Qed.

  Theorem nthd_in_ds : forall ds n,
    d_in (nthd n ds) ds.
  Proof.
    unfold nthd, d_in.
    destruct ds.
    destruct n.
    - left.
      apply selN_oob. omega.
    - destruct l; simpl snd.
      + eauto.
      + right.
        apply in_selN.
        simpl; omega.
  Qed.

  Theorem latest_in_ds : forall ds,
    d_in (latest ds) ds.
  Proof.
    unfold d_in, latest.
    destruct ds; simpl.
    destruct l; simpl; intuition.
  Qed.

  Theorem d_in_In : forall d d' l,
    d_in d (d', l) -> In d (d' :: l).
  Proof.
    unfold d_in; simpl; intuition.
  Qed.

  Theorem d_in_In' : forall d d' l,
    In d (d' :: l) -> d_in d (d', l).
  Proof.
    unfold d_in; simpl; intuition.
  Qed.

  Lemma d_in_pushd : forall ds d d',
    d_in d (pushd d' ds) ->
    d = d' \/ d_in d ds.
  Proof.
    destruct ds; unfold d_in; simpl; intuition.
  Qed.

  (** The second non-empty list's is a subset, in
    * the same order, of the first non-empty list
    *)
  Inductive NEListSubset : nelist -> nelist -> Prop :=
  | NESubsetNil : forall d, NEListSubset (d, nil) (d, nil)
  | NESubsetHead : forall ds d d',
      NEListSubset ds (d, nil)
      -> NEListSubset (pushd d' ds) (d', nil)
  | NESubsetIn : forall ds ds' d,
      NEListSubset ds ds'
      -> NEListSubset (pushd d ds) (pushd d ds')
  | NESubsetNotIn : forall ds ds' d,
      NEListSubset ds ds'
      -> NEListSubset (pushd d ds) ds'.

  Lemma nelist_subset_equal : forall ds,
    NEListSubset ds ds.
  Proof.
    destruct ds.
    induction l.
    constructor.
    eapply NESubsetIn in IHl.
    eauto.
  Qed.

  Lemma nelist_subset_oldest : forall l t,
    NEListSubset (t, l) (t, nil).
  Proof.
    induction l; intros; simpl.
    constructor.

    replace t with (fst (t, l)) at 1 by auto.
    econstructor.
    eauto.
  Qed.

  Lemma nelist_subset_latest : forall ds,
    NEListSubset ds (latest ds, nil).
  Proof.
    unfold latest.
    destruct ds, l; simpl.
    constructor.
    replace (_, _) with (pushd t0 (t, l)) by auto.
    eapply NESubsetHead; eauto.
    eapply nelist_subset_oldest.
  Qed.

  Lemma nelist_subset_oldest_latest' : forall l t,
    length l > 0
    -> NEListSubset (t, l) (t, hd t l :: nil).
  Proof.
    destruct l; intros; simpl.
    inversion H.

    replace t0 with (fst (t0, l)) at 1 by auto.
    replace t0 with (fst (t0, @nil T)) at 2 by auto.
    replace l with (snd (t0, l)) by auto.
    replace nil with (snd (t0, @nil T)) by auto.
    econstructor.
    apply nelist_subset_oldest.
  Qed.

  Lemma nelist_subset_oldest_latest : forall ds,
    length (snd ds) > 0
    -> NEListSubset ds (fst ds, latest ds :: nil).
  Proof.
    destruct ds; simpl.
    eapply nelist_subset_oldest_latest'.
  Qed.

  Lemma pushd_length : forall ds d,
    length (snd (pushd d ds)) = S (length (snd ds)).
  Proof.
    intros; unfold pushd; simpl; auto.
  Qed.
  
  Lemma pushdlist_length: forall dlist ds, length(snd(pushdlist dlist ds)) =
           length(dlist) + length(snd ds).
  Proof.
  induction dlist.
  reflexivity.
  simpl.
  intros.
  rewrite IHdlist.
  rewrite pushd_length.
  omega.
  Qed.
  
  Lemma nthd_pushd : forall l t n d,
    n <= length l
    -> nthd n (pushd d (t, l)) = nthd n (t, l).
  Proof.
    unfold nthd, pushd; intros.
    destruct (Nat.eq_dec n 0).

    subst; simpl.
    f_equal; omega.

    replace (snd (_)) with ([d] ++ l) by auto.
    rewrite selN_app2; simpl.
    destruct n; intuition.
    f_equal; omega.
    destruct n; intuition.
  Qed.

  Lemma nthd_pushd_latest : forall l t d n,
    n = S (length l)
    -> nthd n (pushd d (t, l)) = d.
  Proof.
    unfold nthd, pushd; intros.
    simpl; subst.
    rewrite minus_diag; auto.
  Qed.

  Lemma nelist_subset_nthd : forall ds ds',
    NEListSubset ds ds'
    -> forall n' d,
        n' <= length (snd ds')
        -> nthd n' ds' = d
        -> exists n, n <= length (snd ds) /\ nthd n ds = d.
  Proof.
    induction 1; intros; simpl.

    exists 0.
    rewrite nthd_0; eauto.

    simpl in *.
    inversion H0; subst.
    exists (S (length (snd ds))); intuition.
    rewrite nthd_0.
    setoid_rewrite nthd_pushd_latest; eauto.

    destruct (lt_dec n' (length (snd (pushd d ds'))));
    destruct ds, ds'.
    rewrite nthd_pushd in H1.
    apply IHNEListSubset in H1.
    inversion H1.
    exists x; intuition.
    rewrite nthd_pushd; auto.
    rewrite pushd_length in l; omega.
    rewrite pushd_length in l; simpl in *; omega.

    rewrite nthd_pushd_latest in H1; subst.
    exists (S (length l)); intuition.
    rewrite nthd_pushd_latest; auto.
    replace l0 with (snd (t0, l0)) by auto.
    rewrite <- pushd_length with (d:=d).
    omega.

    apply IHNEListSubset in H1; auto.
    inversion H1.
    intuition.
    exists x; intuition.
    setoid_rewrite nthd_pushd; auto.
  Qed.



End NonEmptyList.


Notation " ds '!!'" := (latest ds) (at level 1).

Definition d_map A B (f : A -> B) (ds : nelist A) :=
  (f (fst ds), map f (snd ds)).

Lemma d_map_latest : forall A B (f : A -> B) ds,
  latest (d_map f ds) = f (latest ds).
Proof.
  unfold latest, d_map; intros.
  destruct ds, l; simpl; auto.
Qed.

Lemma d_map_fst : forall A B (f : A -> B) ds,
  fst (d_map f ds) = f (fst ds).
Proof.
  unfold d_map; intros; auto.
Qed.

Lemma d_map_nthd : forall A B (f : A -> B) ds n,
  nthd n (d_map f ds) = f (nthd n ds).
Proof.
  unfold d_map; intros; simpl.
  destruct n.
  repeat rewrite nthd_0; auto.
  unfold nthd; destruct (lt_dec n (length (snd ds))); simpl.
  erewrite selN_map, map_length; auto.
  rewrite map_length; omega.
  rewrite map_length.
  replace (length (snd ds) - S n) with 0 by omega.
  destruct ds, l; simpl; auto.
Qed.

Lemma d_in_d_map : forall A B ds (f : A -> B) d,
  d_in d (d_map f ds) ->
  exists d', d_in d' ds /\ d = f d'.
Proof.
  intros.
  apply d_in_In in H.
  replace (f (fst ds) :: map f (snd ds)) with (map f ((fst ds) :: (snd ds))) in H by reflexivity.
  apply in_map_iff in H.
  destruct H.
  eexists; intuition eauto.
  apply d_in_In'; eauto.
Qed.
