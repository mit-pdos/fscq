Require Import Prog.
Require Import AsyncFS.
Require Import List.
Require Import String.
Require Import Word.
Require Import Hoare.
Require Import Log.
Require Import FSLayout.
Require Import Pred.
Require Import Inode.
Require Import DirTree.
Require Import SepAuto.
Require Import Bool.
Require Import BasicProg.
Require Import Omega.
Require Import GenSepN.
Require Import AsyncDisk.
Require Import NEList.
Require Import SuperBlock.
Require Import BFile.

Import ListNotations.

Set Implicit Arguments.


(* Lemmas that should be moved to DirTree or TreeUtil. XXX some are unproven.
 * Maybe after we cleaned up DirTree? 
 *)

Lemma cons_app: forall (A: Type)  (l: list A) (a: A),
                            a::l = [a] ++ l.
Proof.
  intros.
  auto.
Qed.


(* dirent lemmas *)

Definition dirent_names (ents : list (string * DIRTREE.dirtree)) := map fst ents.

Lemma dirent_add_app_ne: forall dents s d name elem',
  s <> name
  ->  DIRTREE.add_to_list name elem' ((s,d) :: dents) = [(s,d)] ++ DIRTREE.add_to_list name elem' dents.
Proof.
  intros.
  unfold DIRTREE.add_to_list at 1.
  destruct (string_dec s name).
  congruence.
  unfold DIRTREE.add_to_list at 1.
  reflexivity.
Qed.

Lemma dirent_add_app_eq: forall dents s d name elem',
  s = name
  ->  DIRTREE.add_to_list name elem' ((s,d) :: dents) = [(s,elem')] ++ dents.
Proof.
  intros.
  unfold DIRTREE.add_to_list.
  destruct (string_dec s name).
  rewrite <- e.
  reflexivity.
  fold DIRTREE.add_to_list. 
  intuition.
Qed.

Lemma dirent_head_eq: forall (dents: list (string*DIRTREE.dirtree)) name s d,
  In name (dirent_names ((s, d) :: dents)) /\ s = name -> ~In name (dirent_names dents).
Proof.
  induction dents.
  - subst; simpl.
    intros. intuition.
  - intros.
Admitted.

Lemma dirtree_name_in_dents: forall name tree_elem elem,
  fold_right
    (DIRTREE.find_subtree_helper
       (fun tree : DIRTREE.dirtree => Some tree) name) None tree_elem = Some elem
  -> In name (dirent_names tree_elem).
Proof.
  intros.
  induction tree_elem.
  - intros. simpl in H. congruence.
  - destruct a.
    destruct (string_dec s name).
    unfold dirent_names.
    rewrite cons_app.
    rewrite map_app.
    apply in_app_iff.
    simpl.
    left.
    auto.
    unfold dirent_names.
    rewrite cons_app.
    rewrite map_app.
    apply in_or_app.
    right.
    apply IHtree_elem.
    rewrite cons_app in H.
    rewrite fold_right_app in H.
    simpl in H.
    destruct (string_dec s name).
    congruence.
    assumption.
Qed.

Lemma dent_add_to_twice: forall fn elem0 elem1 ents,
  DIRTREE.add_to_list fn elem1 (DIRTREE.add_to_list fn elem0 ents) = DIRTREE.add_to_list fn elem1 ents.
Proof.
  intros.
  induction ents.
  - simpl.
    destruct (string_dec fn fn).
    reflexivity.
    congruence.
  - destruct a.
    destruct (string_dec fn s).
    erewrite dirent_add_app_eq; eauto.
    erewrite dirent_add_app_eq; auto.
    rewrite <- cons_app.
    erewrite dirent_add_app_eq; auto.
    erewrite dirent_add_app_ne; auto.
    erewrite dirent_add_app_ne; auto.
    rewrite <- cons_app.
    erewrite dirent_add_app_ne; auto.
    erewrite IHents.
    reflexivity.
Qed.

Lemma dent_in_add_to: forall fn elem tree,
  In fn (dirent_names (DIRTREE.dirtree_dirents tree)) ->  
  In fn (dirent_names (DIRTREE.add_to_list fn elem (DIRTREE.dirtree_dirents tree))).
Proof.
  intros.
  induction (DIRTREE.dirtree_dirents tree).
  - simpl.
    left; eauto.
  - unfold dirent_names.
    destruct a.
    destruct (string_dec fn s).
    erewrite dirent_add_app_eq; eauto.
    erewrite dirent_add_app_ne; eauto.
    rewrite cons_app.
    rewrite map_app.
    subst; simpl.
    right.
    eapply IHl.
    rewrite cons_app in H.
    unfold dirent_names in *.
    rewrite map_app in H.
    simpl in H.
    destruct H.
    congruence.
    assumption.
Qed.

Lemma tree_name_distinct_map: forall (tree_elem: list (string*DIRTREE.dirtree)) inum s d,
   DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum ((s, d) :: tree_elem)) <-> 
    ~In s (dirent_names tree_elem)
      /\ DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum tree_elem).
Proof.
  split.
  - induction tree_elem.
    * simpl.
      intuition.
      admit.
    * intros.
      split.
      eapply DIRTREE.tree_names_distinct_head_name.
      instantiate (2 := inum).
      instantiate (1 := d).
      assumption.
      eapply DIRTREE.tree_name_distinct_rest.
      instantiate (1 := (s, d)). auto.
  - intros.
    destruct H.
    constructor.
Admitted.

Lemma dent_in_add_to_distinct: forall fn elem inum ents,
  DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum ents) ->
  DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum (DIRTREE.add_to_list fn elem ents)).
Proof.
  intros.
  induction ents.
  - simpl.
    admit.
  - destruct a.
    destruct (string_dec fn s).
    erewrite dirent_add_app_eq; eauto.  (* s must not be in ents; how to prove? *)
Admitted.


(* dirtree lemmas *)

Lemma  update_subtree_root: forall root_new root_old,
  DIRTREE.update_subtree [] root_new root_old = root_new.
Proof.
  intros.
  unfold DIRTREE.update_subtree; eauto.
Qed.

Lemma dirtree_inum_update_subtree : forall t fn rest sub,
  DIRTREE.dirtree_inum (DIRTREE.update_subtree (fn::rest) sub t) = DIRTREE.dirtree_inum t.
Proof.
  destruct t; simpl; auto.
Qed.

Lemma dirtree_inum_update_subtree' : forall t fn rest sub inum,
  DIRTREE.dirtree_inum t = inum ->
  DIRTREE.dirtree_inum (DIRTREE.update_subtree (fn::rest) sub t) = inum.
Proof.
  intros; rewrite dirtree_inum_update_subtree; auto.
Qed.

Hint Resolve dirtree_inum_update_subtree'.

Lemma dirtree_isdir_update_subtree : forall t fn rest sub,
  DIRTREE.dirtree_isdir (DIRTREE.update_subtree (fn::rest) sub t) = DIRTREE.dirtree_isdir t.
Proof.
  destruct t; simpl; auto.
Qed.

Lemma dirtree_isdir_update_subtree' : forall t fn rest sub r,
  DIRTREE.dirtree_isdir t = r ->
  DIRTREE.dirtree_isdir (DIRTREE.update_subtree (fn::rest) sub t) = r.
Proof.
  intros; rewrite dirtree_isdir_update_subtree; auto.
Qed.

Hint Resolve dirtree_isdir_update_subtree'.

Lemma dirtree_isdir_true_find_subtree : forall t fn rest sub,
  DIRTREE.find_subtree (fn::rest) t = Some sub ->
  DIRTREE.dirtree_isdir t = true.
Proof.
  destruct t; simpl; intros; congruence.
Qed.

Hint Resolve dirtree_isdir_true_find_subtree.

Lemma dirtree_find_subtree_isdir_true: forall t fn rest sub,
  DIRTREE.find_subtree (fn::rest) t = Some sub ->
  DIRTREE.dirtree_isdir t = true.
Proof.
  destruct t; simpl; intros; congruence.
Qed.

Lemma tree_names_distinct_nodup: forall inum tree_elem,
  DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum tree_elem) -> NoDup (map fst tree_elem).
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma find_subtree_impl_adirent: forall fn tree sub,
  DIRTREE.find_subtree [fn] tree = Some sub ->
  In fn (dirent_names (DIRTREE.dirtree_dirents tree)).
Proof.
  intros.
  unfold dirent_names.
  unfold DIRTREE.find_subtree in H.
  destruct tree.
  intuition.
  congruence.
  eapply dirtree_name_in_dents in H.
  intuition.
Qed.

Lemma update_subtree_is_update_dents: forall fn sub inum ents,
  In fn (dirent_names ents) ->
  DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum ents) ->
  DIRTREE.update_subtree [fn] sub (DIRTREE.TreeDir inum ents) =
  DIRTREE.TreeDir inum (DIRTREE.add_to_list fn sub ents).
Proof.
  intros.
  unfold DIRTREE.update_subtree.
  f_equal.
  induction ents; subst; simpl.
  - admit.
  - destruct a.
    simpl.
    destruct (string_dec s fn).
    rewrite DIRTREE.map_update_subtree_helper_notfound.
    subst; reflexivity.
    eapply dirent_head_eq.
    intuition.
    subst; eauto.
    f_equal.
    rewrite IHents.
    reflexivity.
    unfold dirent_names in *.
    rewrite map_cons in H.
    simpl in H.
    destruct H.
    congruence.
    eauto.
    eapply DIRTREE.tree_name_distinct_rest; eauto.
Admitted.

Lemma update_update_subtree_eq: forall fn elem0 elem1 tree sub,
  DIRTREE.tree_names_distinct tree ->
  DIRTREE.find_subtree [fn] tree = Some sub ->
  DIRTREE.update_subtree [fn] elem1 (DIRTREE.update_subtree [fn] elem0 tree) =
  DIRTREE.update_subtree [fn] elem1 tree.
Proof.
  intros.
  apply dirtree_find_subtree_isdir_true in H0 as Hdir.
  eapply find_subtree_impl_adirent in H0 as Hent.
  eapply DIRTREE.dirtree_dir_parts in Hdir.
  rewrite Hdir.
  rewrite Hdir in H.
  rewrite update_subtree_is_update_dents; eauto.
  rewrite update_subtree_is_update_dents; eauto.
  rewrite update_subtree_is_update_dents; eauto.
  f_equal.
  rewrite dent_add_to_twice; auto.
  apply dent_in_add_to; eauto.
  eapply dent_in_add_to_distinct; eauto.
Qed.

Lemma find_subtree_update_subtree_ne: forall fn1 fn2 tree elem,
  fn1 <> fn2 ->
  DIRTREE.find_subtree [fn1] (DIRTREE.update_subtree [fn2] elem tree) = 
    DIRTREE.find_subtree [fn1] tree.
Proof.
Admitted.


Global Opaque DIRTREE.tree_graft.
Global Opaque DIRTREE.update_subtree.
Global Opaque DIRTREE.find_subtree.
Global Opaque DIRTREE.find_name.
Global Opaque DIRTREE.add_to_dir.
Global Opaque DIRTREE.delete_from_dir.
