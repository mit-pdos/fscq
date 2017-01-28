Require Import Pred.
Require Import DirTreeDef.
Require Import DirTree.
Require Import String.
Require Import Mem.
Require Import List.
Require Import SepAuto.
Require Import BFile.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.
Require Import DirTreeNames.
Require Import DirTreeInodes.

Import DIRTREE.
Import ListNotations.

Set Implicit Arguments.

Inductive flatmem_entry :=
| Nothing
| Dir
| File : forall (inum : addr) (f : BFILE.bfile), flatmem_entry.

Definition dir2flatmem2 (d : dirtree) : @mem _ (list_eq_dec string_dec) _ :=
  fun pn => match find_subtree pn d with
  | Some (TreeFile inum f) => Some (File inum f)
  | Some (TreeDir _ _) => Some Dir
  | None => Some Nothing
  end.

Lemma dir2flatmem2_find_subtree : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (File inum f) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree).
  destruct d.
  inversion H0; subst; auto.
  inversion H0.
  inversion H0.
Qed.

Lemma dir2flatmem2_find_subtree_none : forall fnlist tree,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some Nothing ->
  find_subtree fnlist tree = None.
Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree); eauto.
  destruct d; inversion H0; subst; auto; congruence.
Qed.

Lemma dir2flatmem2_find_subtree_dir : forall fnlist tree,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some Dir ->
  exists inum d, find_subtree fnlist tree = Some (TreeDir inum d).
Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree); [ destruct d | ]; try congruence.
  eauto.
Qed.

(** This should be useful for satisfying preconditions of most AsyncFS functions
 ** that take as an argument an inode number of an existing file in a tree.
 *)
Lemma dir2flatmem2_find_subtree_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> File inum f)%pred (dir2flatmem2 tree) ->
  find_subtree fnlist tree = Some (TreeFile inum f).
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree; eauto.
Qed.

Lemma dir2flatmem2_find_subtree_ptsto_none : forall fnlist tree F,
  tree_names_distinct tree ->
  (F * fnlist |-> Nothing)%pred (dir2flatmem2 tree) ->
  find_subtree fnlist tree = None.
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree_none in H0; eauto.
Qed.

Lemma dir2flatmem2_find_subtree_ptsto_dir : forall fnlist tree F,
  tree_names_distinct tree ->
  (F * fnlist |-> Dir)%pred (dir2flatmem2 tree) ->
  exists inum d, find_subtree fnlist tree = Some (TreeDir inum d).
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree_dir in H0; eauto.
Qed.

Lemma dir2flatmem2_find_name : forall fnlist tree inum f,
  tree_names_distinct tree ->
  dir2flatmem2 tree fnlist = Some (File inum f) ->
  find_name fnlist tree = Some (inum, false).
Proof.
  unfold find_name; intros.
  erewrite dir2flatmem2_find_subtree; eauto.
Qed.

(** This should be useful for satisfying the precondition of [lookup_ok].
 *)
Lemma dir2flatmem2_find_name_ptsto : forall fnlist tree inum f F,
  tree_names_distinct tree ->
  (F * fnlist |-> File inum f)%pred (dir2flatmem2 tree) ->
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
  upd (dir2flatmem2 tree) fnlist (File inum f').
Proof.
  unfold dir2flatmem2; intros.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix fnlist x); repeat deex; subst.
  {
    destruct suffix.
    - rewrite app_nil_r in *.
      erewrite find_update_subtree; eauto.
      rewrite upd_eq; auto.
    - rewrite upd_ne.
      repeat erewrite find_subtree_app.
      2: eauto.
      2: erewrite find_update_subtree; eauto.
      simpl; eauto.
      rewrite <- app_nil_r with (l := fnlist) at 2.
      intro H'. apply app_inv_head in H'. congruence.
  }
  destruct (pathname_decide_prefix x fnlist); repeat deex; subst.
  {
    destruct suffix.
    - rewrite app_nil_r in *.
      erewrite find_update_subtree; eauto.
      rewrite upd_eq; auto.
    - rewrite upd_ne.
      case_eq (find_subtree x tree); intros.
      destruct d.
      + erewrite find_subtree_app in * by eauto; simpl in *; congruence.
      + erewrite update_subtree_app by eauto. erewrite find_update_subtree by eauto.
        simpl; auto.
      + rewrite find_subtree_app_none in * by eauto; congruence.
      + rewrite <- app_nil_r with (l := x) at 1.
        intro H'. apply app_inv_head in H'. congruence.
  }
  rewrite find_subtree_update_subtree_ne_path; eauto.
  rewrite upd_ne; auto.
  contradict H1; subst; eauto. exists nil. rewrite app_nil_r. auto.
Qed.

(** This should be useful in carrying forward separation-logic facts
 ** across [update_subtree] which shows up in postconditions of AsyncFS
 ** mutation functions (and, indirectly through various lemmas, in the
 ** postcondition of [update_fblock_d_ok] as well).
 *)
Lemma dir2flatmem2_update_subtree : forall fnlist tree inum f f' F,
  tree_names_distinct tree ->
  (F * fnlist |-> File inum f)%pred  (dir2flatmem2 tree) ->
  (F * fnlist |-> File inum f')%pred (dir2flatmem2 (update_subtree fnlist (TreeFile inum f') tree)).
Proof.
  intros.
  erewrite dir2flatmem2_update_subtree_upd; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.

Lemma dir2flatmem2_graft_upd : forall tree inum inum' f f' basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (find_subtree (base++[name]) tree = Some (TreeFile inum f) \/
   find_subtree (base++[name]) tree = None) ->
  dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum' f') tree) =
  upd (dir2flatmem2 tree) (base++[name]) (File inum' f').
Proof.
  intros.
  unfold dir2flatmem2.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix base x).
  - destruct H2 as [suffix H2]; subst.
    destruct (pathname_decide_prefix [name] suffix).
    + destruct H2 as [suffix0 H2]; subst.
      rewrite app_assoc.
      erewrite find_subtree_app.
      2: erewrite find_subtree_tree_graft; eauto.
      destruct suffix0; simpl in *.
      * rewrite app_nil_r. rewrite upd_eq; eauto.
      * rewrite upd_ne; eauto.
        2: intro H'; rewrite <- app_nil_r in H'; apply app_inv_head in H'; congruence.
        intuition.
        -- erewrite find_subtree_app; eauto. simpl. eauto.
        -- erewrite find_subtree_app_none; eauto.
    + destruct suffix; simpl in *.
      * rewrite app_nil_r in *.
        rewrite upd_ne; eauto.
        rewrite H0.
        unfold tree_graft.
        erewrite find_update_subtree; eauto.
        rewrite <- app_nil_r with (l := base) at 1.
        intro H'.
        apply app_inv_head in H'. congruence.
      * assert (s <> name) by ( intro; subst; eauto ).
        unfold tree_graft.
        erewrite find_subtree_app.
        2: erewrite find_update_subtree; eauto.
        rewrite upd_ne; eauto.
        2: intro H'; apply app_inv_head in H'; congruence.
        erewrite find_subtree_app; [ | eauto ].

        clear H0.
        simpl.
        induction basedents; simpl in *.
        -- destruct (string_dec name s); congruence.
        -- destruct a.
           destruct (string_dec s0 name); subst; simpl in *.
          ++ destruct (string_dec name s); try congruence.
          ++ destruct (string_dec s0 s); try congruence.

  - clear H1.
    rewrite upd_ne.
    unfold tree_graft.
    2: intro; apply H2; eauto.
    case_eq (find_subtree x tree); intros.
    destruct d.
    + erewrite find_subtree_update_subtree_oob; eauto.
    + edestruct find_subtree_dir_after_update_subtree; eauto.
      rewrite H3; eauto.
    + erewrite find_subtree_none_after_update_subtree; eauto.
Qed.

Theorem dirents2mem2_graft_file_replace : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f inum' f' basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base ++ [name]) |-> File inum' f')%pred (dir2flatmem2 tree) -> 
  (F * (base ++ [name]) |-> File inum f)%pred (dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
  intros.
  erewrite dir2flatmem2_graft_upd; eauto.
  eapply ptsto_upd'; eauto.
  left.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.

Theorem dirents2mem2_graft_file_none : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base ++ [name]) |-> Nothing)%pred (dir2flatmem2 tree) -> 
  (F * (base ++ [name]) |-> File inum f)%pred (dir2flatmem2 (tree_graft basenum basedents base name (TreeFile inum f) tree)).
Proof.
  intros.
  erewrite dir2flatmem2_graft_upd; eauto.
  eapply ptsto_upd'; eauto.
  right.
  eapply dir2flatmem2_find_subtree_ptsto_none; eauto.
Grab Existential Variables.
  all: eauto.
Qed.

Lemma dir2flatmem2_prune_delete : forall tree inum f basenum basedents base name,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (find_subtree (base++[name]) tree = Some (TreeFile inum f) \/
   find_subtree (base++[name]) tree = None) ->
  dir2flatmem2 (tree_prune basenum basedents base name tree) =
  upd (dir2flatmem2 tree) (base++[name]) Nothing.
Proof.
  intros.
  unfold dir2flatmem2.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix base x).
  - destruct H2 as [suffix H2]; subst.
    destruct (pathname_decide_prefix [name] suffix).
    + destruct H2 as [suffix0 H2]; subst.
      rewrite app_assoc.
      erewrite find_subtree_app_none.
      2: eapply find_subtree_pruned_none; eauto.

      destruct suffix0; simpl in *.
      * rewrite app_nil_r. rewrite upd_eq; eauto.
      * rewrite upd_ne; eauto.
        2: intro H'; rewrite <- app_nil_r in H'; apply app_inv_head in H'; congruence.
        intuition.
        -- erewrite find_subtree_app; eauto. simpl. eauto.
        -- erewrite find_subtree_app_none; eauto.

    + destruct suffix; simpl in *.
      * rewrite app_nil_r in *.
        rewrite upd_ne; eauto.
        rewrite H0.
        unfold tree_prune.
        erewrite find_update_subtree; eauto.
        rewrite <- app_nil_r with (l := base) at 1.
        intro H'.
        apply app_inv_head in H'. congruence.
      * assert (s <> name) by ( intro; subst; eauto ).
        unfold tree_prune.
        erewrite find_subtree_app.
        2: erewrite find_update_subtree; eauto.
        rewrite upd_ne; eauto.
        2: intro H'; apply app_inv_head in H'; congruence.
        erewrite find_subtree_app; [ | eauto ].

        clear H0.
        simpl.
        induction basedents; simpl in *.
        -- destruct (string_dec name s); congruence.
        -- destruct a.
           destruct (string_dec s0 name); subst; simpl in *.
          ++ destruct (string_dec name s); try congruence.
          ++ destruct (string_dec s0 s); try congruence.

  - clear H1.
    rewrite upd_ne.
    unfold tree_prune.
    2: intro; apply H2; eauto.
    case_eq (find_subtree x tree); intros.
    destruct d.
    + erewrite find_subtree_update_subtree_oob; eauto.
    + edestruct find_subtree_dir_after_update_subtree; eauto.
      rewrite H3; eauto.
    + erewrite find_subtree_none_after_update_subtree; eauto.
Qed.

Theorem dirents2mem2_prune_file : forall (F: @pred _ (@list_eq_dec string string_dec) _)
      tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base ++ [name]) |-> File inum f)%pred (dir2flatmem2 tree) ->
  (F * (base ++ [name]) |-> Nothing)%pred (dir2flatmem2 (tree_prune basenum basedents base name tree)).
Proof.
  intros.
  erewrite dir2flatmem2_prune_delete; eauto.
  eapply ptsto_upd'; eauto.
  left.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.

Theorem dirents2mem_update_subtree_upd : forall base subtree pn v subtree0 t,
  tree_names_distinct t ->
  find_subtree base t = Some subtree0 ->
  dir2flatmem2 subtree = upd (dir2flatmem2 subtree0) pn v ->
  dir2flatmem2 (update_subtree base subtree t) = upd (dir2flatmem2 t) (base ++ pn) v.
Proof.
  intros.
  unfold dir2flatmem2 in *.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix base x).
  - deex.
    erewrite find_subtree_app.
    2: eapply find_update_subtree; eauto.
    eapply equal_f in H1.
    rewrite H1.
    destruct (list_eq_dec string_dec pn suffix); subst.
    + repeat rewrite upd_eq; eauto.
    + repeat rewrite upd_ne; eauto.
      erewrite find_subtree_app; eauto.
      intro. apply n. apply app_inv_head in H2; eauto.
  - rewrite upd_ne.
    2: intro; apply H2; eauto.
    case_eq (find_subtree x t); [ destruct d | ]; intros.
    + erewrite find_subtree_update_subtree_oob; eauto.
    + edestruct find_subtree_dir_after_update_subtree.
      3: eauto.
      2: eauto.
      eauto.
      rewrite H4; eauto.
    + rewrite find_subtree_none_after_update_subtree; eauto.
Qed.

Theorem dirents2mem2_update_subtree_one_name : forall t base pn subtree_old subtree_new F v0 v',
  (F * (base ++ pn) |-> v0)%pred (dir2flatmem2 t) ->
  dir2flatmem2 subtree_new = upd (dir2flatmem2 subtree_old) pn v' ->
  tree_names_distinct t ->
  find_subtree base t = Some subtree_old ->
  (F * (base ++ pn) |-> v')%pred (dir2flatmem2 (update_subtree base subtree_new t)).
Proof.
  intros.
  erewrite dirents2mem_update_subtree_upd; eauto.
  eapply ptsto_upd'; eauto.
Qed.


Lemma dirents2mem2_not_prefix : forall t F pn1 i1 f1 pn2 i2 f2,
  tree_names_distinct t ->
  (F * pn1 |-> File i1 f1 * pn2 |-> File i2 f2)%pred (dir2flatmem2 t) ->
  ~ pathname_prefix pn1 pn2.
Proof.
  intros.
  eapply pimpl_trans in H0 as H'1; [ | | reflexivity ].
  eapply pimpl_trans in H0 as H'2; [ | | reflexivity ].
  eapply dir2flatmem2_find_subtree_ptsto with (fnlist := pn1) in H'1; eauto.
  eapply dir2flatmem2_find_subtree_ptsto with (fnlist := pn2) in H'2; eauto.
  2: cancel.
  2: cancel.

  intro.
  destruct H1; subst.
  erewrite find_subtree_app in H'2 by eauto.

  destruct x.

  - rewrite app_nil_r in *.
    eapply ptsto_conflict_F with (a := pn1).
    eapply pimpl_trans; [ reflexivity | | eauto ].
    cancel.
  - simpl in *; congruence.
Qed.

Lemma dir2flatmem2_delete_file: forall (F: @pred _ (@list_eq_dec string string_dec) _)
     tree name inum f basenum basedents base,
  tree_names_distinct tree ->
  find_subtree base tree = Some (TreeDir basenum basedents) ->
  (F * (base++[name])%list |-> File inum f)%pred (dir2flatmem2 tree) ->
  (F * (base++[name])%list |-> Nothing)%pred (dir2flatmem2 (update_subtree base (TreeDir basenum (delete_from_list name basedents)) tree)).
Proof.
  intros.
  eapply dir2flatmem2_prune_delete in H0.
  unfold tree_prune in H0.
  unfold delete_from_dir in H0.
  rewrite H0.
  eapply ptsto_upd'; eauto.
  eauto.
  left.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.

Lemma dir2flatmem2_rename: forall Ftree cwd srcbase srcname dstbase dstname
      dstnum0 dstents subtree srcnum0 srcents srcnum srcfile dstnum dstfile 
      dnum tree_elem tree,
  tree_names_distinct tree ->
  tree_inodes_distinct tree ->
  ((Ftree ✶ (cwd ++ srcbase ++ [srcname]) |-> File srcnum srcfile)
    ✶ (cwd ++ dstbase ++ [dstname]) |-> File dstnum dstfile)%pred 
      (dir2flatmem2 tree) ->
  find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
  find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum0 srcents) ->
  find_dirlist srcname srcents = Some subtree ->
  find_subtree dstbase
          (tree_prune srcnum0 srcents srcbase srcname (TreeDir dnum tree_elem)) =
        Some (TreeDir dstnum0 dstents) ->
  ((Ftree ✶ (cwd ++ srcbase ++ [srcname]) |-> Nothing)
   ✶ (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred
    (dir2flatmem2
      (update_subtree cwd
        (tree_graft dstnum0 dstents dstbase dstname subtree
         (tree_prune srcnum0 srcents srcbase srcname
            (TreeDir dnum tree_elem))) tree)).
Proof.
  intros.
  erewrite <- update_update_subtree_same.
  eapply dirents2mem2_update_subtree_one_name.
  eapply pimpl_trans; [ reflexivity | | ].
  2: eapply dirents2mem2_update_subtree_one_name.
  5: eauto.
  3: eapply dir2flatmem2_prune_delete with (name := srcname) (base := srcbase).
  cancel.
  pred_apply; cancel.
  3: left.
  3: erewrite <- find_subtree_app by eauto.
  3: eapply dir2flatmem2_find_subtree_ptsto.

  eapply tree_names_distinct_subtree; eauto.

  eauto.
  eauto.
  pred_apply; cancel.
  eauto.

  3: erewrite find_update_subtree; eauto.

  erewrite <- find_subtree_dirlist in H4.
  erewrite <- find_subtree_app in H4 by eauto.
  erewrite <- find_subtree_app in H4 by eauto.
  erewrite dir2flatmem2_find_subtree_ptsto in H4.
  3: pred_apply; cancel.
  inversion H4; subst.

  erewrite dir2flatmem2_graft_upd; eauto.

  eapply tree_names_distinct_prune_subtree'; eauto.
  eapply tree_names_distinct_subtree; eauto.

  left.
  eapply find_subtree_prune_subtree_oob; eauto.

  intro. eapply pathname_prefix_trim in H6.
  eapply dirents2mem2_not_prefix; eauto.
  erewrite <- find_subtree_app by eauto.
  erewrite dir2flatmem2_find_subtree_ptsto.
  reflexivity. eauto.
  pred_apply; cancel.
  eauto.

  eapply tree_names_distinct_update_subtree; eauto.
  eapply tree_names_distinct_prune_subtree'; eauto.
  eapply tree_names_distinct_subtree; eauto.
Qed.



Global Opaque dir2flatmem2.
