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
Require Import ListPred.

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
 * list2nmem is meant to convert a list representation of files into a memory-like
 * object that maps inode numbers (list positions) into files (or None, if the
 * inode number is too big).  [list2nmem] always uses [nat] as the index.
 *)
Definition list2nmem (A: Type) (l: list A) : (@mem nat eq_nat_dec A) :=
  fun a => selN (map (@Some A) l) a None.


Theorem list2nmem_oob : forall A (l : list A) i,
  i >= length l
  -> (list2nmem l) i = None.
Proof.
  unfold list2nmem; intros.
  rewrite selN_oob; auto.
  rewrite map_length; auto.
Qed.


Theorem list2nmem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2nmem l)
  -> i < length l.
Proof.
  intros.
  destruct (lt_dec i (length l)); auto; exfalso.
  apply not_lt in n.
  apply list2nmem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.


Theorem list2nmem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2nmem l)
  -> x = selN l i def.
Proof.
  intros.
  assert (i < length l).
  eapply list2nmem_inbound; eauto.
  unfold list2nmem in H.
  apply ptsto_valid' in H.
  erewrite selN_map in H by auto.
  inversion H; eauto.
Qed.


Lemma listupd_progupd: forall A l i (v : A),
  i < length l
  -> list2nmem (updN l i v) = Prog.upd (list2nmem l) i v.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Prog.upd.
  autorewrite with core.

  destruct (eq_nat_dec x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.
  erewrite selN_updN_ne; auto.
Qed.

Theorem list2nmem_upd: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2nmem l)
  -> (F * i |-> y)%pred (list2nmem (updN l i y)).
Proof.
  intros.
  rewrite listupd_progupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2nmem_inbound; eauto.
Qed.


Theorem listapp_progupd: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Prog.upd (list2nmem l) (length l) a.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Prog.upd.

  destruct (lt_dec x (length l)).
  - subst; rewrite selN_map with (default' := a).
    destruct (eq_nat_dec x (length l)); subst.
    + rewrite selN_last; auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
    + rewrite app_length; simpl; omega.
  - destruct (eq_nat_dec x (length l)).
    + subst; erewrite selN_map with (default' := a).
      rewrite selN_last; auto.
      rewrite app_length; simpl; omega.
    + repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      omega.
      rewrite app_length; simpl; intuition.
Qed.


Theorem list2nmem_app: forall A (F : @pred _ _ A) l a,
  F (list2nmem l)
  -> (F * (length l) |-> a)%pred (list2nmem (l ++ a :: nil)).
Proof.
  intros.
  erewrite listapp_progupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2nmem, sel.
  rewrite selN_oob; auto.
  rewrite map_length.
  omega.
Qed.


Theorem list2nmem_removelast_is : forall A l (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (lt_dec i (length l - 1)) then Some (selN l i def) else None.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (lt_dec x (length l - 1)); unfold list2nmem, sel.
  - rewrite selN_map with (default' := def).
    rewrite selN_removelast by omega; auto.
    rewrite length_removelast by auto; omega.
  - rewrite selN_oob; auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    omega.
Qed.


Theorem list2nmem_removelast_list2nmem : forall A (l : list A) (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (eq_nat_dec i (length l - 1)) then None else (list2nmem l) i.
Proof.
  intros; apply functional_extensionality; intros.
  erewrite list2nmem_removelast_is with (def := def) by eauto.
  unfold list2nmem.
  destruct (lt_dec x (length l - 1));
  destruct (eq_nat_dec x (length l - 1)); subst; intuition.
  omega.
  erewrite selN_map with (default' := def); auto.
  omega.
  erewrite selN_oob; auto.
  rewrite map_length.
  omega.
Qed.


Lemma mem_disjoint_either: forall AT AEQ V (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
Proof.
  unfold mem_disjoint; intros; firstorder.
  pose proof (H a); firstorder.
  pose proof (H1 v); firstorder.
  destruct (m2 a); auto.
  pose proof (H2 v0); firstorder.
Qed.


Theorem list2nmem_removelast: forall A F (l : list A) v,
  l <> nil
  -> (F * (length l - 1) |-> v)%pred (list2nmem l)
  -> F (list2nmem (removelast l)).
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (x = list2nmem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2nmem_removelast_list2nmem; auto.

  destruct (eq_nat_dec x1 (length l - 1)); subst.
  apply mem_disjoint_comm in H0. 
  eapply mem_disjoint_either; eauto.

  rewrite H1; unfold mem_union.
  destruct (x x1); subst; simpl; auto.
  apply eq_sym; apply H5; auto.
Qed.


Theorem list2nmem_array: forall  A (l : list A),
  arrayN 0 l (list2nmem l).
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  erewrite listapp_progupd; try omega.
  eapply arrayN_app_progupd; try omega.
  eauto.
Qed.


(* Alternative variants of [list2nmem] that are more induction-friendly *)
Definition list2nmem_off (A: Type) (start : nat) (l: list A) : (nat -> option A) :=
  fun a => if lt_dec a start then None
                             else selN (map (@Some A) l) (a - start) None.

Theorem list2nmem_off_eq : forall A (l : list A), list2nmem l = list2nmem_off 0 l.
Proof.
  unfold list2nmem, list2nmem_off, sel; intros.
  apply functional_extensionality; intros.
  rewrite <- minus_n_O.
  reflexivity.
Qed.

Fixpoint list2nmem_fix (A : Type) (start : nat) (l : list A) : (nat -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if eq_nat_dec a start then Some h else list2nmem_fix (S start) l' a
  end.

Lemma list2nmem_fix_below : forall (A : Type) (l : list A) start a,
  a < start -> list2nmem_fix start l a = None.
Proof.
  induction l; auto; simpl; intros.
  destruct (eq_nat_dec a0 start); [omega |].
  apply IHl; omega.
Qed.

Theorem list2nmem_fix_off_eq : forall A (l : list A) n,
  list2nmem_off n l = list2nmem_fix n l.
Proof.
  induction l; intros; apply functional_extensionality; intros.
  unfold list2nmem_off; destruct (lt_dec x n); auto.

  unfold list2nmem_off; simpl in *.

  destruct (lt_dec x n).
  destruct (eq_nat_dec x n); [omega |].
  rewrite list2nmem_fix_below by omega.
  auto.

  destruct (eq_nat_dec x n).
  rewrite e; replace (n-n) with (0) by omega; auto.

  assert (x - n <> 0) by omega.
  destruct (x - n) eqn:Hxn; try congruence.

  rewrite <- IHl.
  unfold list2nmem_off.

  destruct (lt_dec x (S n)); [omega |].
  f_equal; omega.
Qed.

Theorem list2nmem_fix_eq : forall A (l : list A),
  list2nmem l = list2nmem_fix 0 l.
Proof.
  intros.
  rewrite list2nmem_off_eq.
  eapply list2nmem_fix_off_eq.
Qed.


Lemma list2nmem_nil_array : forall A (l : list A) start,
  arrayN start l (list2nmem nil) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2nmem, sel; simpl; intros.
  repeat deex.
  unfold mem_union in H0.
  apply equal_f with (start) in H0.
  rewrite H2 in H0.
  congruence.
Qed.

Lemma list2nmem_array_nil : forall A (l : list A) start,
  arrayN start nil (list2nmem_fix start l) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold list2nmem, sel, emp; intros.
  pose proof (H start).
  destruct (eq_nat_dec start start); simpl in *; congruence.
Qed.

Theorem list2nmem_array_eq': forall A (l' l : list A) start,
  arrayN start l (list2nmem_fix start l')
  -> l' = l.
Proof.
  induction l'; simpl; intros.
  - erewrite list2nmem_nil_array; eauto.
  - destruct l.
    + eapply list2nmem_array_nil with (start:=start).
      auto.
    + simpl in *.
      unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
      repeat deex.
      unfold ptsto in H1; destruct H1.
      f_equal.
      * eapply equal_f with (start) in H0 as H0'.
        unfold mem_union in H0'.
        rewrite H1 in H0'.
        destruct (eq_nat_dec start start); congruence.
      * apply IHl' with (start:=S start); eauto; try omega.
        assert (x0 = list2nmem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H0.
        apply equal_f with x1 in H0.
        destruct (eq_nat_dec x1 start).

        rewrite list2nmem_fix_below by omega.
        eapply mem_disjoint_either.
        eauto.
        rewrite <- e in H1.
        eauto.

        rewrite H0.
        rewrite H2; auto.
Qed.

Theorem list2nmem_array_eq: forall A (l' l : list A),
  arrayN 0 l (list2nmem l')
  -> l' = l.
Proof.
  intros; eapply list2nmem_array_eq' with (start:=0); try rewrite <- plus_n_O; eauto.
  erewrite <- list2nmem_fix_eq; eauto.
Qed.


Theorem list2nmem_array_app_eq: forall A (l l' : list A) a,
  (arrayN 0 l * (length l) |-> a)%pred (list2nmem l')
  -> l' = (l ++ a :: nil).
Proof.
  intros.
  rewrite list2nmem_array_eq with (l':=l') (l:=l++a::nil); eauto.
  pred_apply.
  rewrite <- isolateN_bwd with (vs:=l++a::nil) (i:=length l) by
    ( rewrite app_length; simpl; omega ).
  rewrite firstn_app by auto.
  replace (S (length l)) with (length (l ++ a :: nil)) by (rewrite app_length; simpl; omega).
  rewrite skipn_oob by omega; simpl.
  instantiate (1:=a).
  rewrite selN_last by auto.
  cancel.
Qed.


Definition arrayN_ex A (vs : list A) i :=
  (arrayN 0 (firstn i vs) * arrayN (i + 1) (skipn (S i) vs))%pred.


Theorem arrayN_except : forall V vs (def : V) i,
  i < length vs
  -> arrayN 0 vs <=p=> (arrayN_ex vs i) * (i |-> selN vs i def).
Proof.
  intros; unfold arrayN_ex.
  erewrite arrayN_isolate with (default := def); eauto.
  simpl.
  unfold piff; split; cancel.
Qed.


Theorem arrayN_except_upd : forall V vs (v : V) i,
  i < length vs
  -> arrayN 0 (updN vs i v) <=p=> (arrayN_ex vs i) * (i |-> v).
Proof.
  intros; unfold arrayN_ex.
  erewrite arrayN_isolate_upd; eauto.
  simpl.
  unfold piff; split; cancel.
Qed.


Theorem arrayN_ex_updN_eq : forall A l i (v : A),
  arrayN_ex (updN l i v) i <=p=> arrayN_ex l i.
Proof.
  unfold arrayN_ex; intros; autorewrite with core;
  split; simpl; rewrite skipn_updN; eauto.
Qed.

Theorem list2nmem_array_pick : forall V l (def : V) i,
  i < length l
  -> (arrayN_ex l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
  intros.
  eapply arrayN_except; eauto.
  eapply list2nmem_array; eauto.
Qed.

Theorem list2nmem_array_upd : forall V ol nl (v : V) i,
  (arrayN_ex ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> nl = updN ol i v.
Proof.
  intros.
  eapply list2nmem_array_eq; autorewrite with core; auto.
  pred_apply.
  rewrite arrayN_except_upd; auto.
Qed.

Theorem list2nmem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> updN ol i v = nl.
Proof.
  intros; apply eq_sym.
  eapply list2nmem_array_upd; eauto.
Qed.

Theorem list2nmem_array_removelast_eq : forall V (nl ol : list V),
  (arrayN_ex ol (length ol - 1))%pred (list2nmem nl)
  -> length ol > 0
  -> nl = removelast ol.
Proof.
  unfold arrayN_ex; intros.
  destruct ol.
  inversion H0.

  eapply list2nmem_array_eq with (l' := nl); eauto.
  pred_apply.
  rewrite firstn_removelast_eq; auto.
  rewrite skipn_oob by omega.
  unfold arrayN at 2.
  clear H; cancel.
Qed.


Theorem list2nmem_array_exis : forall V l (def : V) i,
  (arrayN_ex l i * i |-> selN l i def)%pred (list2nmem l)
  -> (arrayN_ex l i * i |->?)%pred (list2nmem l).
Proof.
  intros; pred_apply; cancel.
Qed.


(* Ltacs *)

Ltac rewrite_list2nmem_pred_bound H :=
  let Hi := fresh in
  eapply list2nmem_inbound in H as Hi.

Ltac rewrite_list2nmem_pred_sel H :=
  let Hx := fresh in
  eapply list2nmem_sel in H as Hx;
  try autorewrite with defaults in Hx;
  unfold sel in Hx.

Ltac rewrite_list2nmem_pred_upd H:=
  let Hx := fresh in
  eapply list2nmem_array_upd in H as Hx;
  [ unfold upd in Hx | .. ].

Ltac rewrite_list2nmem_pred :=
  match goal with
  | [ H : (?prd * ?ix |-> ?v)%pred (list2nmem ?l) |- _ ] =>
    rewrite_list2nmem_pred_bound H;
    first [
      is_var v; rewrite_list2nmem_pred_sel H; subst v |
      match prd with
      | arrayN_ex ?ol ix =>
        is_var l; rewrite_list2nmem_pred_upd H;
        [ subst l | clear H .. ]
      end ]
  end.

Ltac list2nmem_ptsto_cancel :=
  match goal with
  | [ |- (_ * ?p |-> ?a)%pred (list2nmem ?l) ] =>
    let Hx := fresh in
    assert (arrayN 0 l (list2nmem l)) as Hx by eapply list2nmem_array;
      pred_apply; erewrite arrayN_except; clear Hx;
      try autorewrite with defaults; eauto
  end.

Ltac destruct_listmatch_n :=
  match goal with
    | [  H : context [ listmatch ?prd ?a _ ],
        H2 : ?p%pred (list2nmem ?a) |- _ ] =>
      match p with
        | context [ (wordToNat ?ix |-> _)%pred ] =>
            let Hb := fresh in
            apply list2nmem_inbound in H2 as Hb;
            extract_listmatch_at ix;
            clear Hb
      end
  end.

Ltac list2nmem_cancel :=
    repeat rewrite_list2nmem_pred;
    repeat destruct_listmatch_n;
    subst; eauto;
    try list2nmem_ptsto_cancel; eauto.


Ltac list2nmem_bound :=
   match goal with
    | [ H : ( _ * ?p |-> ?i)%pred (list2nmem ?l) |- ?p < length ?l' ] =>
          let Ha := fresh in assert (length l = length l') by solve_length_eq;
          let Hb := fresh in apply list2nmem_inbound in H as Hb;
          eauto; (omega || setoid_rewrite <- Ha; omega); clear Hb Ha
  end.
