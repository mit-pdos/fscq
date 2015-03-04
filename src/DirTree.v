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

  (**
   * XXX slightly awkward: we have to specify a tree depth ahead of time,
   * since otherwise Coq will not let us construct a tree of possibly-infinite
   * depth..
   *)
  Fixpoint dirtree depth : Type :=
    match depth with
    | O => unit
    | S depth' => @mem string string_dec (addr * (BFILE.bfile + dirtree depth'))%type
    end.

  Definition tree_dir_pred {depth} (tree : dirtree depth) : @pred _ eq_nat_dec BFILE.bfile.
    admit.
  Defined.

  Definition tree_file_pred {depth} (tree : dirtree depth) : @pred _ eq_nat_dec BFILE.bfile.
    admit.
  Defined.

  Definition rep fsxp {depth} (tree : dirtree depth) :=
    (exists bflist freeinodes freeinode_pred_unused freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
     BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred *
     [[ (tree_dir_pred tree * tree_file_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

End DIRTREE.
