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
Require Import List.

Set Implicit Arguments.

(**
 * This should eventually replace DirAlloc.v.
 *)

Module DIRTREE.

  Inductive dir_item :=
  | DirFile : BFILE.bfile -> dir_item
  | DirSubdir : list (string * addr * dir_item) -> dir_item.

  Definition dirtree := list (string * addr * dir_item).

  Fixpoint tree_dir_names_pred' (dirlist : dirtree) : @pred _ string_dec (addr * addr) :=
    match dirlist with
    | nil => emp
    | (name, inum, DirFile f) :: dirlist' => name |-> (inum, $0) * tree_dir_names_pred' dirlist'
    | (name, inum, DirSubdir s) :: dirlist' => name |-> (inum, $1) * tree_dir_names_pred' dirlist'
    end.

  Definition tree_dir_names_pred (dir_inum : addr) (dirlist : dirtree) : @pred _ eq_nat_dec _ := (
    exists f dsmap,
    #dir_inum |-> f *
    [[ SDIR.rep f dsmap ]] *
    [[ tree_dir_names_pred' dirlist dsmap ]])%pred.

  (**
   * XXX how can we get Coq to accept this as terminating?
   *)
  (*
  Fixpoint tree_pred (dirlist : dirtree) {struct dirlist} : @pred _ eq_nat_dec _ := (
    match dirlist with
    | nil => emp
    | (name, inum, DirFile f) :: dirlist' => #inum |-> f * tree_pred dirlist'
    | (name, inum, DirSubdir s) :: dirlist' =>
      tree_dir_names_pred inum s * tree_pred s * tree_pred dirlist'
    end)%pred.
  *)
  Parameter tree_pred : dirtree -> @pred nat eq_nat_dec BFILE.bfile.

  Definition rep fsxp tree :=
    (exists bflist freeinodes freeinode_pred_unused freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
     BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred *
     [[ (tree_dir_names_pred fsxp.(FSXPRootInum) tree * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

End DIRTREE.
