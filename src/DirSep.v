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
    Mem.upd (dirents2mem rest) name subtree
  end.

Definition dir2mem (t : dirtree) :=
  dirents2mem (dirtree_dirents t).

Theorem dirents2mem_not_in_none : forall name l,
  (~ In name (map fst l)) ->
  dirents2mem l name = None.
Proof.
  induction l; simpl; intros.
  - firstorder.
  - destruct a.
    rewrite upd_ne; eauto.
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
      * inversion H. inversion H4.
        erewrite update_subtree_notfound by auto.
        apply sep_star_comm in H0.
        apply ptsto_upd_bwd_or in H0.
        intuition.
        -- eapply ptsto_upd_disjoint; eauto.
           eapply dirents2mem_not_in_none; eauto.
        -- deex.
           apply sep_star_comm.
           eapply ptsto_upd. eauto.
      * admit.
Admitted.
