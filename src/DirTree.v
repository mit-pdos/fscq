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

  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let3 (mscs, inum, isdir) <- ForEach fn fnlist
      Loopvar mscs_inum_isdir <- (mscs, dnum, $1)
      Continuation lrx
      Invariant
        any
      OnCrash
        any
      Begin
        If (weq mscs_inum_isdir.(snd) $0) {
          rx (mscs, None)
        } else {
          let2 (mscs, r) <- SDIR.dslookup (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                          mscs_inum_isdir.(fst).(snd) fn mscs_inum_isdir.(fst).(fst);
          match r with
          | None => rx (mscs, None)
          | Some (inum, isdir) => lrx (mscs, inum, isdir)
          end
        }
    Rof;
    rx (mscs, Some (inum, isdir)).

  Definition mknod T fsxp dnum name isdir mscs rx : prog T :=
    let2 (mscs, oi) <- BALLOC.alloc_gen fsxp.(FSXPMemLog) fsxp.(FSXPInodeAlloc) mscs;
    match oi with
    | None => rx (mscs, None)
    | Some inum =>
      let2 (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                     dnum name inum isdir mscs;
      If (bool_dec ok true) {
        rx (mscs, Some inum)
      } else {
        rx (mscs, None)
      }
    end.

  Definition mkfile T fsxp dnum name mscs rx : prog T :=
    let2 (mscs, r) <- mknod fsxp dnum name $0 mscs;
    rx (mscs, r).

  Definition mkdir T fsxp dnum name mscs rx : prog T :=
    let2 (mscs, r) <- mknod fsxp dnum name $1 mscs;
    rx (mscs, r).

  Definition delete T fsxp dnum name mscs rx : prog T :=
    let2 (mscs, oi) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                     dnum name mscs;
    match oi with
    | None => rx (mscs, false)
    | Some (inum, isdir) =>
      mscs <- IfRx irx (weq isdir $0) {
        irx mscs
      } else {
        let2 (mscs, l) <- SDIR.dslist fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                      inum mscs;
        match l with
        | nil => irx mscs
        | a::b => rx (mscs, false)
        end
      };
      let2 (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       dnum name mscs;
      If (bool_dec ok true) {
        mscs <- BALLOC.free_gen fsxp.(FSXPMemLog) fsxp.(FSXPInodeAlloc) inum mscs;
        rx (mscs, true)
      } else {
        rx (mscs, false)
      }
    end.

End DIRTREE.
