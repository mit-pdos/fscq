Require Import Pred.
Require Import DirTree.
Require Import String.
Require Import Mem.
Require Import List.
Require Import SepAuto.
Require Import BFile.
Require Import AsyncDisk.

Import DIRTREE.
Import ListNotations.

Set Implicit Arguments.

Fixpoint dirents2mem (ents : list (string * dirtree)) : @mem _ string_dec _ :=
  match ents with
  | nil => empty_mem
  | (name, subtree) :: rest =>
    Mem.insert (dirents2mem rest) name subtree
  end.

Definition dir2mem (t : dirtree) :=
  dirents2mem (dirtree_dirents t).


Section FLAT.

  Variable AT : Type.
  Variable AEQ : forall (a b : AT), {a=b} + {a<>b}.
  Variable V : Type.
  Variable mk_mem : string -> dirtree -> @mem AT AEQ V.
  Fixpoint dirlist_mem (dirlist : list (string * dirtree)) :=
    match dirlist with
    | nil => empty_mem
    | (name, e) :: dirlist' => mem_union (mk_mem name e) (dirlist_mem dirlist')
    end.

End FLAT.


Fixpoint dir2flatmem (prefix : list string) (d : dirtree) : @mem _ (list_eq_dec string_dec) _ :=
  match d with
  | TreeFile inum f => Mem.insert empty_mem prefix (inum, f)
  | TreeDir _ ents => dirlist_mem (fun name subtree => dir2flatmem (prefix ++ [name]) subtree) ents
  end.


Lemma dir2flatmem_find_subtree : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem [] tree fnlist = Some (inum, f) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
Admitted.

(** This should be useful for satisfying preconditions of most AsyncFS functions
 ** that take as an argument an inode number of an existing file in a tree.
 *)
Lemma dir2flatmem_find_subtree_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> (inum, f))%pred (dir2flatmem [] tree) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem_find_subtree; eauto.
Qed.

Lemma dir2flatmem_find_name : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem [] tree fnlist = Some (inum, f) ->
  find_name fnlist tree = Some (inum, false).
Proof.
  unfold find_name; intros.
  erewrite dir2flatmem_find_subtree; eauto.
Qed.

(** This should be useful for satisfying the precondition of [lookup_ok].
 *)
Lemma dir2flatmem_find_name_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> (inum, f))%pred (dir2flatmem [] tree) ->
  find_name fnlist tree = Some (inum, false).
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem_find_name; eauto.
Qed.

Lemma dir2flatmem_update_subtree_upd : forall fnlist tree inum f f',
  tree_names_distinct tree ->
  find_subtree fnlist tree = Some (TreeFile inum f) ->
  dir2flatmem [] (update_subtree fnlist (TreeFile inum f') tree) =
  upd (dir2flatmem [] tree) fnlist (inum, f').
Proof.
Admitted.

(** This should be useful in carrying forward separation-logic facts
 ** across [update_subtree] which shows up in postconditions of AsyncFS
 ** mutation functions (and, indirectly through various lemmas, in the
 ** postcondition of [update_fblock_d_ok] as well).
 *)
Lemma dir2flatmem_update_subtree : forall fnlist tree inum f f' F,
  tree_names_distinct tree ->
  (F * fnlist |-> (inum, f))%pred  (dir2flatmem [] tree) ->
  (F * fnlist |-> (inum, f'))%pred (dir2flatmem [] (update_subtree fnlist (TreeFile inum f') tree)).
Proof.
  intros.
  erewrite dir2flatmem_update_subtree_upd; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem_find_subtree_ptsto; eauto.
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
        erewrite update_dirtree_preserve_name in H7; eauto.
        eapply IHl; eauto.
        eauto.
        inversion H; inversion H4; subst.
        apply dirents2mem_not_in_none; auto.
Qed.

Lemma dir2flatmem_graft_upd : forall tree inum inum' f f' basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree (base++[name]) tree = Some (TreeFile inum f) ->
  dir2flatmem [] (tree_graft basenum basedents base name (TreeFile inum' f') tree) =
  upd (dir2flatmem [] tree) (base++[name]) (inum', f').
Proof.
Admitted.

(* if name exists then the graft is the same as an update but with new inum too *)
Theorem dirents2mem_graft_file' : forall (F: @pred (list string) (@list_eq_dec string string_dec) (addr * BFILE.bfile))
      tree name inum f inum' f' basenum basedents base,
  tree_names_distinct tree ->
  (F * (base ++ [name]) |-> (inum', f'))%pred (dir2flatmem [] tree) -> 
  (F * (base ++ [name]) |-> (inum, f))%pred (dir2flatmem [] (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
  intros.
  erewrite dir2flatmem_graft_upd; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem_find_subtree_ptsto; eauto.
Qed.

(* unproven version for when dst doesn't exist *)
Theorem dirents2mem_graft_file : forall (F: @pred (list string) (@list_eq_dec string string_dec) (addr * BFILE.bfile))
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  F (dir2flatmem [] tree) -> 
  (F * (base ++ [name]) |-> (inum, f))%pred (dir2flatmem [] (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
Admitted.

Lemma dir2flatmem_prune_delete : forall tree inum f basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree (base++[name]) tree = Some (TreeFile inum f) ->
  dir2flatmem [] (tree_prune basenum basedents base name tree) =
  mem_except (dir2flatmem [] tree) (base++[name]).
Proof.
Admitted.

Theorem dirents2mem_prune_file : forall (F: @pred (list string) (@list_eq_dec string string_dec) (addr * BFILE.bfile))
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  (F * (base ++ [name]) |-> (inum, f))%pred (dir2flatmem [] tree) ->
  F (dir2flatmem [] (tree_prune basenum basedents base name tree)).
Proof.
  intros.
  erewrite dir2flatmem_prune_delete; eauto.
  eapply ptsto_mem_except; eauto.
  pred_apply.
  cancel.
  eapply dir2flatmem_find_subtree_ptsto; eauto.
Qed.


Global Opaque dir2flatmem.