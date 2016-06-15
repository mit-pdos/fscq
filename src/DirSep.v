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


Lemma fst_update_subtree: forall l name newtree,
  map fst (map (update_subtree_helper (fun _: dirtree => newtree) name) l) = map fst l.
Proof.
  intros.
  induction l.
  - simpl; auto.
  - erewrite map_cons.
    unfold update_subtree_helper at 1.
    destruct a.
    destruct (string_dec s name).
    erewrite map_cons; erewrite IHl; simpl; auto.
    erewrite map_cons; erewrite IHl; simpl; auto.
Qed.


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
        eapply ptsto_insert_disjoint_ne; auto.
        erewrite dirents2mem_not_in_none; eauto.
        inversion H.
        inversion H4; eauto. subst.
        subst; contradict H7.
         erewrite fst_update_subtree in H7; eauto.
        eapply IHl; eauto.
        eauto.
        inversion H; inversion H4; subst.
        apply dirents2mem_not_in_none; auto.
Qed.

