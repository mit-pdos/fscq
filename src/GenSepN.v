Require Import Mem.
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
Require Import ListUtils.
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

Notation "[[[ NS ':::' P ]]]" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.
Notation "【 NS '‣‣' P 】" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.

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


Lemma listupd_memupd: forall A l i (v : A),
  i < length l
  -> list2nmem (updN l i v) = Mem.upd (list2nmem l) i v.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.upd.
  autorewrite with core lists.

  destruct (eq_nat_dec x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.

  erewrite selN_updN_ne; auto.
Qed.

Theorem list2nmem_updN: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2nmem l)
  -> (F * i |-> y)%pred (list2nmem (updN l i y)).
Proof.
  intros.
  rewrite listupd_memupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2nmem_inbound; eauto.
Qed.

Lemma list2nmem_updN_selN : forall A F (l : list A) a v1 def,
  (F * a |-> v1)%pred (list2nmem (updN l a v1)) ->
  (F * a |-> selN l a def)%pred (list2nmem l).
Proof.

  intros.
  destruct (lt_dec a (length l)).

  eapply list2nmem_updN with (y := selN l a def) in H.
  rewrite updN_twice in H.
  rewrite updN_selN_eq in H; auto.
  apply list2nmem_inbound in H.
  rewrite length_updN in H.
  congruence.
Qed.


Theorem listapp_memupd: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.upd (list2nmem l) (length l) a.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.upd.

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
  erewrite listapp_memupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2nmem, selN.
  rewrite selN_oob; auto.
  rewrite map_length.
  omega.
Qed.

Theorem list2nmem_arrayN_app: forall A (F : @pred _ _ A) l l',
  F (list2nmem l) -> (F * arrayN (length l) l') %pred (list2nmem (l ++ l')).
Proof.
  intros.
  generalize dependent F.
  generalize dependent l.
  induction l'; intros; simpl.
  - rewrite app_nil_r.
    apply emp_star_r.
    apply H.
  - apply sep_star_assoc.
    assert (Happ := list2nmem_app F l a H).
    assert (IHla := IHl' (l ++ a :: nil) (sep_star F (ptsto (length l) a)) Happ).
    replace (length (l ++ a :: nil)) with (S (length l)) in IHla.
    replace ((l ++ a :: nil) ++ l') with (l ++ a :: l') in IHla.
    apply IHla.
    rewrite <- app_assoc; reflexivity.
    rewrite app_length; simpl.
    symmetry; apply Nat.add_1_r.
Qed.

Theorem list2nmem_removelast_is : forall A l (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (lt_dec i (length l - 1)) then Some (selN l i def) else None.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (lt_dec x (length l - 1)); unfold list2nmem.
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
  assert (m1 = list2nmem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2nmem_removelast_list2nmem; auto.

  destruct (eq_nat_dec x (length l - 1)); subst.
  apply mem_disjoint_comm in H0. 
  eapply mem_disjoint_either; eauto.

  rewrite H1; unfold mem_union.
  destruct (m1 x); subst; simpl; auto.
  apply eq_sym; apply H5; auto.
Qed.


Theorem list2nmem_array: forall  A (l : list A),
  arrayN 0 l (list2nmem l).
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  erewrite listapp_memupd; try omega.
  eapply arrayN_app_memupd; try omega.
  eauto.
Qed.

Theorem list2nmem_arrayN_firstn_skipn: forall A (l:list A) n,
  (arrayN 0 (firstn n l) * arrayN n (skipn n l))%pred (list2nmem l).
Proof.
  intros.
  case_eq (lt_dec n (length l)); intros.
  - rewrite <- firstn_skipn with (l := l) (n := n) at 3.
    replace n with (length (firstn n l)) at 2.
    apply list2nmem_arrayN_app.
    apply list2nmem_array.
    apply firstn_length_l; omega.
  - rewrite firstn_oob by omega.
    rewrite skipn_oob by omega.
    eapply pimpl_apply.
    cancel.
    apply list2nmem_array.
Qed.

Lemma list2nmem_arrayN_xyz : forall A (def:A) data F off (l:list A),
  (F * arrayN off data)%pred (list2nmem l) ->
  (F * arrayN off data)%pred (list2nmem (
    firstn off l ++ data ++ skipn (off + length data) l)).
Proof.
  induction data; intros; simpl in *.
  rewrite Nat.add_0_r.
  rewrite firstn_skipn.
  assumption.

  assert ((F * arrayN (S off) data * off |-> a)%pred (list2nmem l)).
  pred_apply; cancel.
  assert ((F * off |-> a * arrayN (S off) data)%pred (list2nmem l)).
  pred_apply; cancel.
  assert (IHa := IHdata (F * off |-> a)%pred (S off) (updN l off a)).
  assert (Habound := H0).
  apply list2nmem_inbound in Habound.
  eapply list2nmem_sel in H0.
  assert (Hasel := H0).
  apply selN_eq_updN_eq in H0.
  rewrite H0 in IHa.
  assert (IHa' := IHa H1).
  replace (firstn (S off) l) with (firstn off l ++ a :: nil) in IHa'.
  replace (S off + length data) with (off + S (length data)) in IHa'.
  rewrite cons_nil_app in IHa'.
  (* cancel tries to do some substitution that doesn't work,
     so manually call assoc lemma *)
  pred_apply; apply sep_star_assoc.
  omega.
  replace (S off) with (off + 1) by omega.
  symmetry; eapply firstn_plusone_selN'.
  eassumption.
  assumption.

  Grab Existential Variables.
  exact def.
Qed.

Lemma list2nmem_arrayN_newlist_partial : forall A (def:A) n F off (l:list A) olddata newdata,
  length olddata = length newdata ->
  (F * arrayN off olddata)%pred (list2nmem l) ->
  (F * arrayN off (firstn n newdata) * arrayN (off+n) (skipn n olddata))%pred
    (list2nmem (firstn off l ++
      firstn n newdata ++ skipn n olddata ++
      skipn (off+length olddata) l)).
Proof.
  induction n; intros; simpl.
  rewrite Nat.add_0_r.
  assert (Hsplit := list2nmem_arrayN_xyz def olddata off H0).
  pred_apply; cancel.
  destruct newdata; destruct olddata; simpl; auto; try inversion H.
  rewrite Nat.add_0_r.
  rewrite firstn_skipn.
  pred_apply; cancel.
  replace (off + S n) with (S off + n) by omega.
  replace (off + S (length olddata)) with (S off + length olddata) by omega.
  assert (IHn' := IHn (F * off |-> a)%pred (S off) (updN l off a) _ _ H2).
  simpl in H0.
  (* there are many asserts here because I don't know of a way to use
     sep_star_assoc to rewrite separation logic propositions other than
     pred_apply; cancel, and pred_apply requires that a hypothesis regarding
     the same memory.

     What I really want is pred_rewrite H, where H is a pimpl or pimpl_iff. *)
  assert ((F * arrayN (S off) olddata * off |-> a)%pred
    (list2nmem (updN l off a))) as Hupdl.
  eapply list2nmem_updN.
  pred_apply; cancel.
  assert ((F * off |-> a * arrayN (S off) olddata)%pred
    (list2nmem (updN l off a))).
  pred_apply; cancel.
  assert (IHn'' := IHn' H1).
  replace (firstn (S off) (updN l off a)) with (firstn off l ++ a :: nil) in IHn''.
  rewrite cons_nil_app in IHn''.
  rewrite skipN_updN' in IHn'' by omega.
  pred_apply; cancel.
  replace (S off) with (off + 1) by omega.
  assert (off < length l) as Hoffbound.
  eapply list2nmem_inbound.
  pred_apply; cancel.
  erewrite firstn_plusone_selN' with (x := a).
  rewrite firstn_updN_oob.
  auto.
  auto.
  symmetry; apply selN_updN_eq.
  assumption.
  rewrite length_updN; assumption.

  Grab Existential Variables.
  exact def.
Qed.

Lemma list2nmem_arrayN_newlist : forall A (def:A) F off (l:list A) olddata newdata,
  length olddata = length newdata ->
  (F * arrayN off olddata)%pred (list2nmem l) ->
  (F * arrayN off newdata)%pred
    (list2nmem (firstn off l ++
      newdata ++
      skipn (off+length olddata) l)).
Proof.
  intros.
  assert (Hnewlist := list2nmem_arrayN_newlist_partial def (length newdata) _ _ _ H H0).
  rewrite firstn_oob in Hnewlist by omega.
  rewrite skipn_oob in Hnewlist by omega.
  simpl in Hnewlist.
  pred_apply; cancel.
Qed.


(* Alternative variants of [list2nmem] that are more induction-friendly *)
Definition list2nmem_off (A: Type) (start : nat) (l: list A) : (nat -> option A) :=
  fun a => if lt_dec a start then None
                             else selN (map (@Some A) l) (a - start) None.

Theorem list2nmem_off_eq : forall A (l : list A), list2nmem l = list2nmem_off 0 l.
Proof.
  unfold list2nmem, list2nmem_off; intros.
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

Theorem list2nmem_off_app_union : forall A (a b : list A) start,
  list2nmem_off start (a ++ b) = @mem_union _ eq_nat_dec A (list2nmem_off start a)
                                                           (list2nmem_off (start + length a) b).
Proof.
  intros.
  repeat rewrite list2nmem_fix_off_eq.
  generalize dependent b.
  generalize dependent start.
  induction a; simpl; intros; apply functional_extensionality; intros.
  - unfold mem_union. rewrite <- plus_n_O. auto.
  - unfold mem_union in *.
    destruct (eq_nat_dec x start); eauto.
    rewrite IHa.
    replace (S start + length a0) with (start + S (length a0)) by omega.
    auto.
Qed.

Theorem list2nmem_off_disjoint : forall A (a b : list A) sa sb,
  (sb >= sa + length a \/ sa >= sb + length b) ->
  @mem_disjoint _ eq_nat_dec A (list2nmem_off sa a) (list2nmem_off sb b).
Proof.
  unfold mem_disjoint, list2nmem_off, not; intros; repeat deex;
    destruct (lt_dec a0 sa); destruct (lt_dec a0 sb); try congruence;
    apply selN_map_some_range in H0;
    apply selN_map_some_range in H2;
    omega.
Qed.

Lemma list2nmem_nil_array : forall A (l : list A) start,
  arrayN start l (list2nmem nil) -> l = nil.
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2nmem; simpl; intros.
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
  unfold list2nmem, emp; intros.
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
        assert (m2 = list2nmem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H0.
        apply equal_f with x in H0.
        destruct (eq_nat_dec x start).

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


Lemma list2nmem_some_bound' : forall A (m : list A) start off a,
  list2nmem_fix start m off = Some a
  -> off + 1 <= start + length m.
Proof.
  induction m; simpl; intros.
  congruence.
  destruct (Nat.eq_dec off start).
  omega.
  replace (start + S (length m)) with (S start + length m) by omega.
  eapply IHm.
  eauto.
Qed.

Lemma list2nmem_some_bound : forall A (m : list A) off a,
  list2nmem m off = Some a
  -> off + 1 <= length m.
Proof.
  intros.
  rewrite list2nmem_fix_eq in H.
  apply list2nmem_some_bound' in H.
  omega.
Qed.

Theorem list2nmem_arrayN_bound : forall A (l m : list A) off F,
  (F * arrayN off l)%pred (list2nmem m)
  -> l = nil \/ off + length l <= length m.
Proof.
  induction l; simpl; intros.
  intuition.
  right.
  apply sep_star_assoc in H as H'.
  apply IHl in H'.
  intuition.
  subst. simpl.
  apply sep_star_comm in H.
  apply sep_star_assoc in H.
  apply ptsto_valid in H.
  apply list2nmem_some_bound in H.
  omega.
Qed.

Theorem list2nmem_ptsto_bound : forall A (l : list A) off v F,
  (F * off |-> v)%pred (list2nmem l)
  -> off < length l.
Proof.
  intros.
  assert ((F * arrayN off (v :: nil))%pred (list2nmem l)).
  pred_apply; cancel.
  apply list2nmem_arrayN_bound in H0. intuition; try congruence.
  simpl in *; omega.
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
  erewrite isolate_fwd_upd; eauto.
  simpl.
  unfold piff; split; cancel.
Qed.


Theorem arrayN_ex_updN_eq : forall A l i (v : A),
  arrayN_ex (updN l i v) i <=p=> arrayN_ex l i.
Proof.
  unfold arrayN_ex; intros; autorewrite with core lists;
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

Theorem list2nmem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> nl = updN ol i v.
Proof.
  intros.
  eapply list2nmem_array_eq; autorewrite with core lists; auto.
  pred_apply.
  rewrite isolate_fwd_upd; auto.
  cancel.
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


Lemma list2nmem_ptsto_cancel : forall V i (def : V) l, i < length l ->
  (arrayN_ex l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
  intros.
  assert (arrayN 0 l (list2nmem l)) as Hx by eapply list2nmem_array.
  pred_apply; erewrite arrayN_except; eauto.
Qed.

Lemma list2nmem_ptsto_cancel_pair : forall A B i (def : A * B) l,
  i < length l ->
  (arrayN_ex l i * i |-> (fst (selN l i def), snd (selN l i def)))%pred (list2nmem l).
Proof.
  intros.
  assert (arrayN 0 l (list2nmem l)) as Hx by eapply list2nmem_array.
  pred_apply; erewrite arrayN_except; eauto.
  rewrite <- surjective_pairing.
  cancel.
Qed.

Lemma list2nmem_sel_for_eauto : forall V A i (v v' : V) l def,
  (A * i |-> v)%pred (list2nmem l)
  -> v' = selN l i def
  -> v' = v.
Proof.
  intros.
  apply list2nmem_sel with (def:=def) in H.
  congruence.
Qed.


Lemma arrayN_split : forall A off (l : list A) start,
  off <= length l ->
  arrayN start (firstn off l) * arrayN (start + off) (skipn off l) <=p=>
  arrayN start l.
Proof.
  induction off; simpl; intros.
  - replace (start + 0) with start by omega.
    split; cancel.
  - destruct l; simpl in *; try omega.
    replace (start + S off) with (S start + off) by omega.
    rewrite sep_star_assoc.
    apply piff_star_l.
    apply IHoff.
    omega.
Qed.

Lemma arrayN_combine' : forall A (a b : list A) start,
  arrayN start a * arrayN (start + length a) b <=p=> arrayN start (a ++ b).
Proof.
  induction a; simpl; intros.
  - replace (start + 0) with start by omega.
    split; cancel.
  - rewrite sep_star_assoc.
    apply piff_star_l.
    replace (start + S (length a0)) with (S start + length a0) by omega.
    apply IHa.
Qed.

Lemma arrayN_combine : forall A (a b : list A) start off,
  off = start + length a ->
  arrayN start a * arrayN off b <=p=> arrayN start (a ++ b).
Proof.
  intros; subst.
  apply arrayN_combine'.
Qed.


Lemma skipn_selN_skipn : forall off A (l : list A) def,
  off < length l ->
  skipn off l = selN l off def :: skipn (S off) l.
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try omega; auto.
  destruct l; simpl in *; try omega.
  apply IHoff.
  omega.
Qed.

Lemma arrayN_list2nmem : forall A (def : A) (a b : list A) F off,
  (F * arrayN off a)%pred (list2nmem b) ->
  a = firstn (length a) (skipn off b).
Proof.
  induction a; simpl; intros; auto.
  rewrite skipn_selN_skipn with (def:=def).
  f_equal.
  eapply list2nmem_sel.
  pred_apply. cancel.
  eapply IHa.
  pred_apply. cancel.
  eapply list2nmem_ptsto_bound.
  pred_apply. cancel.
Qed.

Theorem list2nmem_ptsto_end_eq : forall A (F : @pred _ _ A) l a a',
  (F * (length l) |-> a)%pred (list2nmem (l ++ a' :: nil)) ->
  a = a'.
Proof.
  intros.
  apply list2nmem_sel with (def:=a) in H.
  rewrite selN_last in H; auto.
Qed.

Theorem list2nmem_arrayN_end_eq : forall A (F : @pred _ _ A) l l' l'' (def:A),
  length l' = length l'' ->
  (F * arrayN (length l) l')%pred (list2nmem (l ++ l'')) ->
  l' = l''.
Proof.
  intros.
  apply arrayN_list2nmem in H0.
  rewrite skipn_app in H0.
  rewrite firstn_oob in H0.
  auto.
  omega.
  exact def.
Qed.

Theorem list2nmem_off_arrayN: forall  A (l : list A) off,
  arrayN off l (list2nmem_off off l).
Proof.
  intros; rewrite list2nmem_fix_off_eq.
  generalize dependent off; induction l; simpl; intros.
  - firstorder.
  - apply sep_star_comm. eapply ptsto_upd_disjoint; eauto.
    apply list2nmem_fix_below.
    omega.
Qed.

Theorem list2nmem_arrayN_app_iff : forall A (F : @pred _ _ A) l l',
  (F * arrayN (length l) l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).
Proof.
  intros.
  rewrite list2nmem_off_eq in *.
  rewrite list2nmem_off_app_union in H.
  eapply septract_sep_star.
  2: unfold septract; eexists; intuition.
  4: pred_apply' H; cancel.
  apply strictly_exact_to_exact_domain.
  apply arrayN_strictly_exact.
  apply list2nmem_off_disjoint; intuition.
  apply list2nmem_off_arrayN.
Qed.


Lemma mem_except_list2nmem_oob : forall A (l : list A) a,
  a >= length l ->
  mem_except (list2nmem l) a = list2nmem l.
Proof.
  unfold mem_except, list2nmem; intros.
  apply functional_extensionality; intro.
  destruct (Nat.eq_dec x a); subst; simpl; auto.
  erewrite selN_oob; auto.
  autorewrite with lists in *; omega.
Qed.


(* Ltacs *)

Ltac rewrite_list2nmem_pred_bound H :=
  let Hi := fresh in
  eapply list2nmem_inbound in H as Hi.

Ltac rewrite_list2nmem_pred_sel H :=
  let Hx := fresh in
  eapply list2nmem_sel in H as Hx;
  try autorewrite with defaults in Hx.

Ltac rewrite_list2nmem_pred_upd H:=
  let Hx := fresh in
  eapply list2nmem_array_updN in H as Hx.

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


(* crashes *)

Require Import PredCrash AsyncDisk.
Import ListNotations.

Lemma list2nmem_crash_xform : forall vl vsl (F : rawpred),
  possible_crash_list vsl vl ->
  F (list2nmem vsl) ->
  crash_xform F (list2nmem (synced_list vl)).
Proof.
  induction vl using rev_ind; simpl; intuition.
  unfold crash_xform, possible_crash; eexists; intuition.
  setoid_rewrite length_nil in H0; auto.
  apply possible_crash_list_length in H; auto.

  unfold crash_xform, possible_crash.
  eexists; intuition. eauto.
  destruct H as [H Hx].
  destruct (lt_eq_lt_dec a (length vl)).
  destruct s.
  assert (a < length vsl).
  rewrite H; autorewrite with lists; simpl; omega.

  right.
  exists (selN vsl a ($0, nil)).
  exists (selN vl a $0); intuition.
  apply selN_map; auto.
  unfold list2nmem, synced_list.
  erewrite selN_map.
  rewrite selN_combine, selN_app1, repeat_selN; auto.
  autorewrite with lists; simpl; omega.
  autorewrite with lists; auto.
  rewrite combine_length_eq; autorewrite with lists; simpl; omega.
  specialize (Hx a H1).
  rewrite selN_app1 in Hx; auto.

  right; subst.
  eexists; exists x; intuition.
  autorewrite with lists in H; simpl in H.
  unfold list2nmem; erewrite selN_map by omega; eauto.
  unfold list2nmem; rewrite synced_list_app.
  erewrite selN_map, selN_app2.
  rewrite synced_list_length, Nat.sub_diag; auto.
  rewrite synced_list_length; auto.
  rewrite app_length, synced_list_length; simpl; omega.
  rewrite app_length in H; simpl in H.
  assert (length vl < length vsl) as Hy by omega.
  specialize (Hx (length vl) Hy).
  rewrite selN_app2, Nat.sub_diag in Hx by omega; simpl in Hx.
  unfold vsmerge; eauto.

  left; split.
  rewrite app_length in H; simpl in H.
  unfold list2nmem; erewrite selN_oob; auto.
  rewrite map_length; omega.
  unfold list2nmem; erewrite selN_oob; auto.
  rewrite map_length, synced_list_length, app_length; simpl; omega.
  Unshelve. all: eauto.
Qed.


Lemma crash_xform_list2nmem_possible_crash_list : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  exists vsl, F (list2nmem vsl) /\ possible_crash_list vsl (map fst vl).
Proof.
  unfold crash_xform.
  induction vl using rev_ind; intros; auto.
  exists nil; deex.
  replace (list2nmem nil) with m'; auto.
  apply functional_extensionality; intro.
  specialize (H1 x).
  destruct H1; destruct H.
  rewrite H; auto.
  deex; unfold list2nmem in H; simpl in *; congruence.
  unfold possible_crash_list; intuition.
  inversion H.

  deex.

  (* Figure out [m' (length vl)] *)
  case_eq (m' (length vl)); [ intro p | ]; intro Hp.
  specialize (IHvl (pred_ex F (length vl) p)).
  rewrite listapp_memupd in H1.

  pose proof (possible_crash_upd_mem_except H1) as Hx.
  rewrite mem_except_list2nmem_oob in Hx by auto.
  specialize (H1 (length vl)); destruct H1.
  contradict H; rewrite upd_eq by auto.
  intuition congruence.
  repeat deex.

  eapply pred_ex_mem_except in H0 as Hy.
  destruct IHvl as [ ? Hz ].
  eexists; eauto.
  destruct Hz as [ Hz [ Heq HP ] ].
  rewrite map_length in Heq.

  unfold pred_ex in Hz.
  rewrite <- Heq in Hz.
  rewrite <- listapp_memupd in Hz.
  eexists; split; eauto.

  split; autorewrite with lists; simpl; intros.
  repeat rewrite app_length; omega.
  destruct (lt_dec i (length x0)); repeat rewrite map_app.
  setoid_rewrite selN_app1; try rewrite map_length; try omega.
  apply HP; auto.
  setoid_rewrite selN_app2; try rewrite map_length; try omega.
  rewrite <- Heq; replace (i - length x0) with 0 by omega; simpl.
  rewrite upd_eq in H by auto.
  destruct x; inversion H; subst; simpl.
  rewrite Hp in H1; inversion H1; subst.
  eauto.
  eauto.

  specialize (H1 (length vl)); destruct H1.
  destruct H; contradict H1.
  rewrite listapp_memupd, upd_eq; auto; congruence.
  repeat deex; congruence.
Qed.


Lemma crash_xform_list2nmem_synced : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  map snd vl = repeat (@nil valu) (length vl).
Proof.
  unfold crash_xform.
  induction vl using rev_ind; intros; auto.
  deex; rewrite map_app.

  pose proof (H1 (length vl)) as Hx; destruct Hx.
  destruct H as [ H Hx ]; contradict Hx.
  rewrite listapp_memupd, upd_eq by auto; congruence.
  repeat deex; auto.
  rewrite listapp_memupd, upd_eq in H by auto; inversion H; subst.

  erewrite IHvl; simpl.
  rewrite app_length; simpl.
  rewrite <- repeat_app_tail.
  f_equal; omega.
  exists (mem_except m' (length vl)).
  intuition.

  apply pred_ex_mem_except; eauto.
  replace (list2nmem vl) with (mem_except (list2nmem (vl ++ [(v', nil)])) (length vl)).
  apply possible_crash_mem_except; eauto.
  rewrite listapp_memupd.
  rewrite <- mem_except_upd.
  rewrite mem_except_list2nmem_oob; auto.
Qed.

