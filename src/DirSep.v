Require Import Pred.
Require Import DirTree.
Require Import String.
Require Import Mem.
Require Import List.
Require Import SepAuto.
Require Import BFile.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.

Import DIRTREE.
Import ListNotations.

Set Implicit Arguments.

Definition dir2flatmem2 (d : dirtree) : @mem _ (list_eq_dec string_dec) _ :=
  fun pn => match DIRTREE.find_subtree pn d with
  | Some (TreeFile inum f) => Some (Some (inum, f))
  | Some (TreeDir _ _) => Some None
  | None => Some None
  end.

Lemma dir2flatmem2_find_subtree : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (Some (inum, f)) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree).
  destruct d.
  inversion H0; subst; auto.
  inversion H0.
  inversion H0.
Qed.

(** This should be useful for satisfying preconditions of most AsyncFS functions
 ** that take as an argument an inode number of an existing file in a tree.
 *)
Lemma dir2flatmem2_find_subtree_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> Some (inum, f))%pred (dir2flatmem2 tree) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree; eauto.
Qed.

Lemma dir2flatmem2_find_name : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (Some (inum, f)) ->
  find_name fnlist tree = Some (inum, false).
Proof.
  unfold find_name; intros.
  erewrite dir2flatmem2_find_subtree; eauto.
Qed.

(** This should be useful for satisfying the precondition of [lookup_ok].
 *)
Lemma dir2flatmem2_find_name_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> Some (inum, f))%pred (dir2flatmem2 tree) ->
  find_name fnlist tree = Some (inum, false).
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_name; eauto.
Qed.

Lemma dir2flatmem2_update_subtree_upd : forall fnlist tree inum f f',
  tree_names_distinct tree ->
  find_subtree fnlist tree = Some (TreeFile inum f) ->
  dir2flatmem2 (update_subtree fnlist (TreeFile inum f') tree) =
  upd (dir2flatmem2 tree) fnlist (Some (inum, f')).
Proof.
  unfold dir2flatmem2; intros.
  apply functional_extensionality; intros.
  destruct (list_eq_dec string_dec x fnlist); subst.
  erewrite find_update_subtree; eauto.
  rewrite upd_eq; auto.
  (* XXX this next step uses a false theorem... *)
  rewrite find_subtree_update_subtree_ne_path; eauto.
  rewrite upd_ne; auto.
Qed.

(** This should be useful in carrying forward separation-logic facts
 ** across [update_subtree] which shows up in postconditions of AsyncFS
 ** mutation functions (and, indirectly through various lemmas, in the
 ** postcondition of [update_fblock_d_ok] as well).
 *)
Lemma dir2flatmem2_update_subtree : forall fnlist tree inum f f' F,
  tree_names_distinct tree ->
  (F * fnlist |-> Some (inum, f))%pred  (dir2flatmem2 tree) ->
  (F * fnlist |-> Some (inum, f'))%pred (dir2flatmem2 (update_subtree fnlist (TreeFile inum f') tree)).
Proof.
  intros.
  erewrite dir2flatmem2_update_subtree_upd; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.


Lemma dir2flatmem2_graft_upd : forall tree inum inum' f f' basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree (base++[name]) tree = Some (TreeFile inum f) ->
  dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum' f') tree) =
  upd (dir2flatmem2 tree) (base++[name]) (Some (inum', f')).
Proof.
Admitted.

(* if name exists then the graft is the same as an update but with new inum too *)
Theorem dirents2mem2_graft_file' : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f inum' f' basenum basedents base,
  tree_names_distinct tree ->
  (F * (base ++ [name]) |-> Some (inum', f'))%pred (dir2flatmem2 tree) -> 
  (F * (base ++ [name]) |-> Some (inum, f))%pred (dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
  intros.
  erewrite dir2flatmem2_graft_upd; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.

Lemma dir2flatmem2_prune_delete : forall tree inum f basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree (base++[name]) tree = Some (TreeFile inum f) ->
  dir2flatmem2 (tree_prune basenum basedents base name tree) =
  upd (dir2flatmem2 tree) (base++[name]) None.
Proof.
Admitted.

Theorem dirents2mem2_prune_file : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  (F * (base ++ [name]) |-> Some (inum, f))%pred (dir2flatmem2 tree) ->
  (F * (base ++ [name]) |-> None)%pred (dir2flatmem2 (tree_prune basenum basedents base name tree)).
Proof.
  intros.
  erewrite dir2flatmem2_prune_delete; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.

(* XXX require that [name] refer to a TreeFile, as opposed to a TreeDir *)
Lemma dir2flatmem2_update_delete : forall tree basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  dir2flatmem2 (update_subtree base (TreeDir basenum (delete_from_list name basedents)) tree) =
  upd (dir2flatmem2 tree) (base++[name]) None.
Proof.
Admitted.

Lemma dir2flatmem2_delete_file: forall (F: @pred _ (@list_eq_dec string string_dec) _)
     tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  DIRTREE.find_subtree base tree = Some (DIRTREE.TreeDir basenum basedents) ->
  (F * (base++[name])%list |-> Some (inum, f))%pred (dir2flatmem2 tree) ->
  (F * (base++[name])%list |-> None)%pred (dir2flatmem2 (update_subtree base (TreeDir basenum (delete_from_list name basedents)) tree)).
Proof.
  intros.
  erewrite dir2flatmem2_update_delete; eauto.
  eapply ptsto_upd'; eauto.
Qed.


Global Opaque dir2flatmem2.
