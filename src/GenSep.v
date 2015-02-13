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
 * list2mem is meant to convert a list representation of files into a memory-like
 * object that maps inode numbers (list positions) into files (or None, if the
 * inode number is too big).  For now, this always uses [addr] as the index.
 *)
Definition list2mem (A: Type) (l: list A) : (@mem nat eq_nat_dec A) :=
  fun a => selN (map (@Some A) l) a None.


Theorem list2mem_oob : forall A (l : list A) i,
  i >= length l
  -> (list2mem l) i = None.
Proof.
  unfold list2mem; intros.
  rewrite selN_oob; auto.
  rewrite map_length; auto.
Qed.


Theorem list2mem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2mem l)
  -> i < length l.
Proof.
  intros.
  destruct (lt_dec i (length l)); auto; exfalso.
  apply not_lt in n.
  apply list2mem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.


Theorem list2mem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2mem l)
  -> x = selN l i def.
Proof.
  intros.
  assert (i < length l).
  eapply list2mem_inbound; eauto.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  erewrite selN_map in H by auto.
  inversion H; eauto.
Qed.


Lemma listupd_progupd: forall A l i (v : A),
  i < length l
  -> list2mem (updN l i v) = Prog.upd (list2mem l) i v.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, Prog.upd.
  autorewrite with core.

  destruct (eq_nat_dec x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.
  erewrite selN_updN_ne; auto.
Qed.

Theorem list2mem_upd: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2mem l)
  -> (F * i |-> y)%pred (list2mem (updN l i y)).
Proof.
  intros.
  rewrite listupd_progupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2mem_inbound; eauto.
Qed.


Theorem listapp_progupd: forall A l (a : A),
  list2mem (l ++ a :: nil) = Prog.upd (list2mem l) (length l) a.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, Prog.upd.

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


Theorem list2mem_app: forall A (F : @pred _ _ A) l a,
  F (list2mem l)
  -> (F * (length l) |-> a)%pred (list2mem (l ++ a :: nil)).
Proof.
  intros.
  erewrite listapp_progupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2mem, sel.
  rewrite selN_oob; auto.
  rewrite map_length.
  omega.
Qed.


Theorem list2mem_removelast_is : forall A l (def : A),
  l <> nil
  -> list2mem (removelast l) =
     fun i => if (lt_dec i (length l - 1)) then Some (selN l i def) else None.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (lt_dec x (length l - 1)); unfold list2mem, sel.
  - rewrite selN_map with (default' := def).
    rewrite selN_removelast by omega; auto.
    rewrite length_removelast by auto; omega.
  - rewrite selN_oob; auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    omega.
Qed.


Theorem list2mem_removelast_list2mem : forall A (l : list A) (def : A),
  l <> nil
  -> list2mem (removelast l) =
     fun i => if (eq_nat_dec i (length l - 1)) then None else (list2mem l) i.
Proof.
  intros; apply functional_extensionality; intros.
  erewrite list2mem_removelast_is with (def := def) by eauto.
  unfold list2mem.
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


Theorem list2mem_removelast: forall A F (l : list A) v,
  l <> nil
  -> (F * (length l - 1) |-> v)%pred (list2mem l)
  -> F (list2mem (removelast l)).
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (x = list2mem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2mem_removelast_list2mem; auto.

  destruct (eq_nat_dec x1 (length l - 1)); subst.
  apply mem_disjoint_comm in H0. 
  eapply mem_disjoint_either; eauto.

  rewrite H1; unfold mem_union.
  destruct (x x1); subst; simpl; auto.
  apply eq_sym; apply H5; auto.
Qed.


Theorem list2mem_array: forall  A (l : list A),
  arrayN 0 l (list2mem l).
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  erewrite listapp_progupd; try omega.
  eapply arrayN_app_progupd; try omega.
  eauto.
Qed.


(* Alternative variants of [list2mem] that are more induction-friendly *)
Definition list2mem_off (A: Type) (start : nat) (l: list A) : (nat -> option A) :=
  fun a => if lt_dec a start then None
                             else selN (map (@Some A) l) (a - start) None.

Theorem list2mem_off_eq : forall A (l : list A), list2mem l = list2mem_off 0 l.
Proof.
  unfold list2mem, list2mem_off, sel; intros.
  apply functional_extensionality; intros.
  rewrite <- minus_n_O.
  reflexivity.
Qed.

Fixpoint list2mem_fix (A : Type) (start : nat) (l : list A) : (nat -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if eq_nat_dec a start then Some h else list2mem_fix (S start) l' a
  end.

Lemma list2mem_fix_below : forall (A : Type) (l : list A) start a,
  a < start -> list2mem_fix start l a = None.
Proof.
  induction l; auto; simpl; intros.
  destruct (eq_nat_dec a0 start); [omega |].
  apply IHl; omega.
Qed.

Theorem list2mem_fix_off_eq : forall A (l : list A) n,
  list2mem_off n l = list2mem_fix n l.
Proof.
  induction l; intros; apply functional_extensionality; intros.
  unfold list2mem_off; destruct (lt_dec x n); auto.

  unfold list2mem_off; simpl in *.

  destruct (lt_dec x n).
  destruct (eq_nat_dec x n); [omega |].
  rewrite list2mem_fix_below by omega.
  auto.

  destruct (eq_nat_dec x n).
  rewrite e; replace (n-n) with (0) by omega; auto.

  assert (x - n <> 0) by omega.
  destruct (x - n) eqn:Hxn; try congruence.

  rewrite <- IHl.
  unfold list2mem_off.

  destruct (lt_dec x (S n)); [omega |].
  f_equal; omega.
Qed.

Theorem list2mem_fix_eq : forall A (l : list A),
  list2mem l = list2mem_fix 0 l.
Proof.
  intros.
  rewrite list2mem_off_eq.
  eapply list2mem_fix_off_eq.
Qed.


Lemma list2mem_nil_array : forall A (l : list A) start,
  arrayN start l (list2mem nil) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2mem, sel; simpl; intros.
  repeat deex.
  unfold mem_union in H0.
  apply equal_f with (start) in H0.
  rewrite H2 in H0.
  congruence.
Qed.

Lemma list2mem_array_nil : forall A (l : list A) start,
  arrayN start nil (list2mem_fix start l) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold list2mem, sel, emp; intros.
  pose proof (H start).
  destruct (eq_nat_dec start start); simpl in *; congruence.
Qed.

Theorem list2mem_array_eq': forall A (l' l : list A) start,
  arrayN start l (list2mem_fix start l')
  -> l' = l.
Proof.
  induction l'; simpl; intros.
  - erewrite list2mem_nil_array; eauto.
  - destruct l.
    + eapply list2mem_array_nil with (start:=start).
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
        assert (x0 = list2mem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H0.
        apply equal_f with x1 in H0.
        destruct (eq_nat_dec x1 start).

        rewrite list2mem_fix_below by omega.
        eapply mem_disjoint_either.
        eauto.
        rewrite <- e in H1.
        eauto.

        rewrite H0.
        rewrite H2; auto.
Qed.

Theorem list2mem_array_eq: forall A (l' l : list A),
  arrayN 0 l (list2mem l')
  -> l' = l.
Proof.
  intros; eapply list2mem_array_eq' with (start:=0); try rewrite <- plus_n_O; eauto.
  erewrite <- list2mem_fix_eq; eauto.
Qed.


Theorem list2mem_array_app_eq: forall A V (F : @pred _ eq_nat_dec V) (l l' : list A) a,
  (arrayN 0 l * (length l) |-> a)%pred (list2mem l')
  -> l' = (l ++ a :: nil).
Proof.
  intros.
  rewrite list2mem_array_eq with (l':=l') (l:=l++a::nil); eauto.
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


Theorem list2mem_array_pick : forall V l (def : V) i,
  i < length l
  -> (arrayN_ex l i * i |-> selN l i def)%pred (list2mem l).
Proof.
  intros.
  eapply arrayN_except; eauto.
  eapply list2mem_array; eauto.
Qed.

Theorem list2mem_array_upd : forall V ol nl (v : V) i,
  (arrayN_ex ol i * i |-> v)%pred (list2mem nl)
  -> i < length ol
  -> nl = updN ol i v.
Proof.
  intros.
  eapply list2mem_array_eq; autorewrite with core; auto.
  pred_apply.
  rewrite arrayN_except_upd; auto.
Qed.

Theorem list2mem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex ol i * i |-> v)%pred (list2mem nl)
  -> i < length ol
  -> updN ol i v = nl.
Proof.
  intros; apply eq_sym.
  eapply list2mem_array_upd; eauto.
Qed.

Theorem list2mem_array_removelast_eq : forall V (nl ol : list V),
  (arrayN_ex ol (length ol - 1))%pred (list2mem nl)
  -> length ol > 0
  -> nl = removelast ol.
Proof.
  unfold arrayN_ex; intros.
  destruct ol.
  inversion H0.

  eapply list2mem_array_eq with (l' := nl); eauto.
  pred_apply.
  rewrite firstn_removelast_eq; auto.
  rewrite skipn_oob by omega.
  unfold arrayN at 2.
  clear H; cancel.
Qed.


Theorem list2mem_array_exis : forall V l (def : V) i,
  (arrayN_ex l i * i |-> selN l i def)%pred (list2mem l)
  -> (arrayN_ex l i * i |->?)%pred (list2mem l).
Proof.
  intros; pred_apply; cancel.
Qed.


(* Ltacs *)

Ltac rewrite_list2mem_pred_bound H :=
  let Hi := fresh in
  eapply list2mem_inbound in H as Hi.

Ltac rewrite_list2mem_pred_sel H :=
  let Hx := fresh in
  eapply list2mem_sel in H as Hx;
  try autorewrite with defaults in Hx;
  unfold sel in Hx.

Ltac rewrite_list2mem_pred_upd H:=
  let Hx := fresh in
  eapply list2mem_array_upd in H as Hx;
  [ unfold upd in Hx | .. ].

Ltac rewrite_list2mem_pred :=
  match goal with
  | [ H : (?prd * ?ix |-> ?v)%pred (list2mem ?l) |- _ ] =>
    rewrite_list2mem_pred_bound H;
    first [
      is_var v; rewrite_list2mem_pred_sel H; subst v |
      match prd with
      | arrayN_ex ?ol ix =>
        is_var l; rewrite_list2mem_pred_upd H;
        [ subst l | clear H .. ]
      end ]
  end.

Ltac list2mem_ptsto_cancel :=
  match goal with
  | [ |- (_ * ?p |-> ?a)%pred (list2mem ?l) ] =>
    let Hx := fresh in
    assert (arrayN 0 l (list2mem l)) as Hx;
      [ eapply list2mem_array; eauto; try omega |
        pred_apply; erewrite arrayN_except; clear Hx;
        try autorewrite with defaults; eauto ]
  end.

Ltac destruct_listmatch :=
  match goal with
    | [  H : context [ listmatch ?prd ?a _ ],
        H2 : ?p%pred (list2mem ?a) |- _ ] =>
      match p with
        | context [ (?ix |-> _)%pred ] =>
            let Hb := fresh in
            apply list2mem_inbound in H2 as Hb;
            extract_listmatch_at ix;
            clear Hb
      end
  end.

Ltac list2mem_cancel :=
    repeat rewrite_list2mem_pred;
    repeat destruct_listmatch;
    subst; eauto;
    try list2mem_ptsto_cancel; eauto.


Ltac list2mem_bound :=
   match goal with
    | [ H : ( _ * ?p |-> ?i)%pred (list2mem ?l) |- wordToNat ?p < length ?l' ] =>
          let Ha := fresh in assert (length l = length l') by solve_length_eq;
          let Hb := fresh in apply list2mem_inbound in H as Hb;
          eauto; (omega || setoid_rewrite <- Ha; omega); clear Hb Ha
  end.
