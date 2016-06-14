Require Import Pred.
Require Import DirTree.
Require Import String.
Require Import Mem.
Require Import List.
Require Import SepAuto.

Import DIRTREE.
Import ListNotations.

Fixpoint dirents2mem (ents : list (string * dirtree)) : @mem _ string_dec _ :=
  match ents with
  | nil => empty_mem
  | (name, subtree) :: rest =>
    Mem.insert (dirents2mem rest) name subtree
  end.

Definition dir2mem (t : dirtree) :=
  dirents2mem (dirtree_dirents t).


Lemma dirents2mem_cons: forall l ent_name ent_tree,
  dirents2mem ((ent_name, ent_tree) :: l) = Mem.insert (dirents2mem l) ent_name ent_tree.
Proof.
  intros.
  unfold dirents2mem.
  reflexivity.
Qed.


Theorem dirents2mem_not_in_none : forall name l,
  (~ In name (map fst l)) ->
  dirents2mem l name = None.
Proof.
  induction l; simpl; intros.
  - firstorder.
  - destruct a.
    rewrite insert_ne; eauto.
Qed.


(* xxx unused *)
Lemma insert_dirents2mem_found: forall l a v,
  (In a (map fst l)) ->
  insert (dirents2mem l) a v = dirents2mem l.
Proof.
  intros.
  induction l.
  - unfold insert, dirents2mem; simpl.
    simpl in H.
    exfalso; auto.
  - destruct a0.
    rewrite dirents2mem_cons.
    destruct (string_dec s a).
    + subst. rewrite insert_repeat; eauto.
    + rewrite insert_comm; eauto.
      rewrite IHl; eauto.
      erewrite map_cons in H.
      eapply in_inv in H.
      destruct H; eauto; simpl in H. congruence.
Qed.

Lemma ptsto_insert_disjoint_ne: forall AT AEQ V (F : @pred AT AEQ V) a v a' v' m,
  a <> a' ->
  m a' = None ->
  (exists F', (F' * a |-> v)%pred m /\ (F' * a' |->v' = F)%pred) ->
  (F * a |-> v)%pred (insert m a' v').
Proof.
  intros.
  destruct H1.
  intuition.
  rewrite <- H3.
  eapply pimpl_apply.
  eapply sep_star_comm.
  eapply pimpl_apply.
  eapply sep_star_assoc_1.
  apply ptsto_insert_disjoint; eauto.
  eapply pimpl_apply.
  eapply sep_star_comm.
  eassumption.
Qed.

Require Import FunctionalExtensionality.

Lemma ptsto_insert_bwd_ne: forall AT AEQ V (F : @pred AT AEQ V) a v a' v' m,
  a <> a' ->
  m a' = None ->
  (F * a |-> v)%pred (insert m a' v') ->
  (pred_except F a' v' * a |-> v)%pred m.
Proof.
  unfold_sep_star; unfold pimpl, pred_except, insert; intros.
  repeat deex.
  exists (mem_except m a').
  exists m2.
  intuition.
  apply functional_extensionality; intros.
  - apply equal_f with (x0 := x) in H2.
    destruct (AEQ x a'); subst.
    rewrite H0 in *.

Lemma mem_union_sel_none : forall AT AEQ V (m1 m2 : @mem AT AEQ V) a,
  m1 a = None ->
  m2 a = None ->
  mem_union m1 m2 a = None.
Proof.
Admitted.

    rewrite mem_union_sel_none; auto.
    apply mem_except_is_none.
    admit.
    rewrite H2.
    Search mem_union mem_except.
  
  
  replace (fun a => if AEQ a a' then Some v' else mem_except m0 a' a) with m0.
  Search mem_except Some.
  exists (fun a => if AEQ a a' then v'
  do 2 eexists.
  
  setoid_rewrite pred_except_ptsto with (p := F) (a := a') (v := v') in H1.
  pred_apply.
  cancel.

  instantiate (v' := v').
  pred_apply.
  cancel.
Admitted.

     (* F = (F' * a' |-> v')%pred -> *)

Theorem dirents2mem_update_subtree :
  forall root F name oldtree newtree,
  tree_names_distinct root ->
  (F * name |-> oldtree)%pred (dir2mem root) ->
  (F * name |-> newtree)%pred (dir2mem (update_subtree [name] newtree root)).
Proof.
  unfold dir2mem.
  destruct root; simpl.
  - intros.
    exfalso.
    apply pred_empty_mem in H0.
    apply emp_pimpl_sep_star in H0.
    intuition.
    eapply emp_not_ptsto; eauto.
  - intros.
    generalize dependent F.
    induction l; simpl; intros.
    + apply pred_empty_mem in H0.
      apply emp_pimpl_sep_star in H0.
      intuition.
      exfalso; eapply emp_not_ptsto; eauto.
    + destruct a; simpl in *.
      destruct (string_dec s name); subst; simpl in *.
      * erewrite update_subtree_notfound.
        apply ptsto_insert_disjoint.
        apply sep_star_comm in H0.
        eapply ptsto_insert_bwd; eauto.
        eapply dirents2mem_not_in_none; eauto.
        inversion H. inversion H4.
        inversion H4; eauto.
        eapply dirents2mem_not_in_none; eauto.
        inversion H.
        inversion H4; eauto.
        inversion H.
        inversion H4; eauto.
      * eapply ptsto_insert_bwd_ne in H0.
        destruct H0.
        destruct H0.
        eapply ptsto_insert_disjoint_ne; auto.
        erewrite dirents2mem_not_in_none; eauto.
        inversion H.
        inversion H5; eauto.
        admit.
        eexists x.
        split.
        eapply IHl; eauto.
        eassumption.
        congruence.
Qed.