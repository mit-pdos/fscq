Require Import DirName.
Require Import Balloc.
Require Import Prog.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile.
Require Import String.
Require Import FSLayout.
Require Import Pred.
Require Import Arith.
Require Import GenSepN.

Set Implicit Arguments.

(**
 * This should eventually replace DirAlloc.v.
 *)

Module DIRTREE.

  Inductive dir_item :=
  | DirFile : BFILE.bfile -> dir_item
  | DirSubdir : @mem string string_dec (addr * dir_item) -> dir_item.

  Definition dirtree := @mem string string_dec (addr * dir_item).

  Definition tree_dir_pred (tree : dirtree) : @pred _ eq_nat_dec BFILE.bfile.
    admit.
  Defined.

  Definition tree_file_pred (tree : dirtree) : @pred _ eq_nat_dec BFILE.bfile.
    admit.
  Defined.

  Definition rep fsxp tree :=
    (exists bflist freeinodes freeinode_pred_unused freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
     BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred *
     [[ (tree_dir_pred tree * tree_file_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

End DIRTREE.
