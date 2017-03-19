Require Import DirTree.
Require Export String.
Require Import RelationClasses.
Require Import CCLProg.

Export DirTreeDef.

Definition thread_homes := TID -> list string.

Definition homedir_rely tid (homes: thread_homes) (tree tree':dirtree) :=
  find_subtree (homes tid) tree' = find_subtree (homes tid) tree.

Definition homedir_guarantee tid (homes: thread_homes) (tree tree':dirtree) :=
  forall tid', tid' <> tid ->
          homedir_rely tid homes tree tree'.

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
