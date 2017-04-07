Require Import DirTree.
Require Export String.
Require Import RelationClasses.
Require Import CCLProg.
Require Import Automation.

Export DirTreeDef.

Local Open Scope list.

Definition thread_homes := TID -> list string.

Implicit Type (homes: thread_homes).

Definition homedir_rely tid homes (tree tree':dirtree) :=
  find_subtree (homes tid) tree' = find_subtree (homes tid) tree.

Definition homedir_guarantee tid homes (tree tree':dirtree) :=
  forall tid', tid <> tid' ->
          homedir_rely tid' homes tree tree'.

Instance homedir_guar_preorder tid homes : PreOrder (homedir_guarantee tid homes).
Proof.
  unfold homedir_guarantee, homedir_rely.
  constructor; hnf; intros.
  auto.

  specialize (H tid').
  specialize (H0 tid').
  intuition congruence.
Defined.

Instance homedir_rely_preorder tid homes : PreOrder (homedir_rely tid homes).
Proof.
  unfold homedir_rely.
  constructor; hnf; intros; congruence.
Defined.

Lemma homedir_rely_preserves_homedir : forall homes homedir tid tree tree',
    find_subtree (homes tid) tree = Some homedir ->
    homedir_rely tid homes tree tree' ->
    find_subtree (homes tid) tree' = Some homedir.
Proof.
  unfold homedir_rely; intros.
  congruence.
Qed.

Lemma homedir_rely_preserves_homedir_missing : forall (homes : thread_homes) (tid : TID)
                                                 (tree tree' : dirtree),
    find_subtree (homes tid) tree = None ->
    homedir_rely tid homes tree tree' ->
    find_subtree (homes tid) tree' = None.
Proof.
  unfold homedir_rely; intros.
  congruence.
Qed.

Lemma homedir_rely_preserves_subtrees : forall homes tid path tree tree' f,
    find_subtree (homes tid ++ path) tree = Some f ->
    homedir_rely tid homes tree tree' ->
    find_subtree (homes tid ++ path) tree' = Some f.
Proof.
  intros.
  eapply find_subtree_app' in H; repeat deex.
  erewrite find_subtree_app; eauto using homedir_rely_preserves_homedir.
Qed.

Definition directories_disjoint (path1 path2: list string) :=
  exists prefix name1 name2 rest1 rest2,
    path1 = prefix ++ name1 :: rest1 /\
    path2 = prefix ++ name2 :: rest2 /\
    name1 <> name2.

Definition homedir_disjoint homes tid :=
  forall tid', tid <> tid' ->
          directories_disjoint (homes tid) (homes tid').

Lemma find_other_name_alter : forall name1 name2 rest1 rest2 up tree,
    name1 <> name2 ->
    find_subtree (name2 :: rest2) (alter_subtree (name1 :: rest1) up tree) =
    find_subtree (name2 :: rest2) tree.
Proof.
  intros.
  destruct tree; simpl; auto.
  induction l; simpl; auto.
  destruct a; simpl.
  destruct (string_dec s name1) eqn:?, (string_dec s name2) eqn:? ;
    subst; simpl in *;
      repeat simpl_match;
      congruence.
Qed.

Theorem alter_homedir_guarantee : forall homes tid path tree up,
    homedir_disjoint homes tid ->
    DirTreeNames.tree_names_distinct tree ->
    homedir_guarantee tid homes tree (alter_subtree (homes tid ++ path) up tree).
Proof.
  intros.
  case_eq (find_subtree (homes tid ++ path) tree); intros.
  - unfold homedir_guarantee, homedir_rely; intros.
    specialize (H _ ltac:(eassumption)).
    unfold directories_disjoint in H; repeat deex.
    replace (homes tid) in *.
    replace (homes tid') in *.
    replace ((prefix ++ name1 :: rest1) ++ path) with (prefix ++ (name1 :: rest1 ++ path)) in *;
      swap 1 2.
    rewrite <- List.app_assoc; auto.

    eapply find_subtree_app' in H1; repeat deex.
    erewrite find_subtree_app with (tree:=tree) by eauto.
    erewrite find_subtree_app;
      [ | solve [ erewrite DirTreeNames.find_prefix_alter; eauto ] ].
    apply find_other_name_alter; auto.
  - erewrite DirTreeNames.alter_subtree_path_notfound; eauto.
    reflexivity.
Qed.
