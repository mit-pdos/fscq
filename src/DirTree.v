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
Require Import Hoare.
Require Import MemLog.
Require Import GenSep.
Require Import SepAuto.

Set Implicit Arguments.

Module DIRTREE.

  Inductive dir_item :=
  | DirFile : BFILE.bfile -> dir_item
  | DirSubdir : list (string * addr * dir_item) -> dir_item.

  Definition dirtree := list (string * addr * dir_item).

  Fixpoint find_name (tree : dirtree) (fnlist : list string) (inum : addr) (isdir : addr) :=
    match fnlist with
    | nil => Some (inum, isdir)
    | name :: rest =>
      if weq isdir $0 then None else
      fold_left (fun accum (arg : string * addr * dir_item) =>
                 let '(name', inum', item') := arg in
                                  if string_dec name' name then
                                  match item' with
                                  | DirFile _ => find_name nil rest inum' $0
                                  | DirSubdir tree' => find_name tree' rest inum' $1
                                  end
                                  else accum) tree None
    end.

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

  Section DIRITEM.

  Variable F : addr -> dir_item -> @pred nat eq_nat_dec BFILE.bfile.

  Fixpoint tree_pred' (dirlist : dirtree) : @pred _ eq_nat_dec _ := (
    match dirlist with
    | nil => emp
    | (_, inum, dir_item) :: dirlist' => F inum dir_item * tree_pred' dirlist'
    end)%pred.

  End DIRITEM.

  Fixpoint diritem_pred inum diritem := (
    match diritem with
    | DirFile f => #inum |-> f
    | DirSubdir s => tree_dir_names_pred inum s * tree_pred' diritem_pred s
    end)%pred.

  Definition tree_pred (dirlist : dirtree) :=
    tree_pred' diritem_pred dirlist.

  Definition rep fsxp tree :=
    (exists bflist freeinodes freeinode_pred_unused freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
     BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred *
     [[ (tree_dir_names_pred fsxp.(FSXPRootInum) tree * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

  Lemma tree_dir_extract : forall d F dmap name inum,
    (F * name |-> (inum, $1))%pred dmap
    -> tree_dir_names_pred' d dmap
    -> tree_pred d =p=> exists F s, F * tree_dir_names_pred inum s * tree_pred s.
  Proof.
    induction d; intros.
    - simpl in *. eapply emp_complete in H0; [| apply emp_empty_mem ]; subst.
      apply sep_star_empty_mem in H; intuition.
      exfalso. eapply ptsto_empty_mem. eauto.
    - destruct a. destruct p. destruct d0; simpl in *.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHd. cancel. cancel.
        2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto. discriminate.
        apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0. inversion H0. subst.
          cancel. unfold tree_pred. instantiate (a0:=l). cancel.
        * apply ptsto_mem_except in H0.
          rewrite IHd. cancel. cancel.
          2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
          pred_apply; cancel.
  Qed.

  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let3 (mscs, inum, isdir) <- ForEach fn fnlist
      Ghost mbase m F treetop bflist
      Loopvar mscs_inum_isdir <- (mscs, dnum, $1)
      Continuation lrx
      Invariant
        MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs_inum_isdir.(fst).(fst) *
        exists tree,
        [[ (F * rep fsxp treetop)%pred (list2mem m) ]] *
        [[ (exists F', tree_dir_names_pred mscs_inum_isdir.(fst).(snd) tree *
            tree_pred tree * F')%pred (list2nmem bflist) ]] *
        [[ find_name treetop fnlist dnum $1 = find_name tree fn mscs_inum_isdir.(fst).(snd) mscs_inum_isdir.(snd) ]]
      OnCrash
        MEMLOG.log_intact fsxp.(FSXPMemLog) mbase
      Begin
        If (weq mscs_inum_isdir.(snd) $0) {
          rx (mscs_inum_isdir.(fst).(fst), None)
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

  Theorem namei_ok : forall fsxp dnum fnlist mscs,
    {< F mbase m tree,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp tree)%pred (list2mem m) ]]
    POST:(mscs,r)
           [[ r = find_name tree fnlist dnum $1 ]] *
           MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs
    CRASH  MEMLOG.log_intact fsxp.(FSXPMemLog) mbase
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei, rep.
    step.

    instantiate (a4 := l).
    pred_apply. cancel.
    (*
     * interesting problem: [namei] starts from a caller-supplied directory, but
     * we don't have a precondition proving that this directory [dnum] is a valid
     * part of the tree..
     *)
    admit.

    step.
    step.
    destruct (weq b $0); congruence.

    (* destruct some [exists] terms before creating evars.. *)
    unfold tree_dir_names_pred in H11; destruct_lift H11.

    step.
    unfold SDIR.rep_macro. do 2 eexists. intuition.
    (* Be careful which [list2mem d0] we pick! *)
    eapply pimpl_apply; [ | exact H3 ]. cancel.
    pred_apply. cancel.
    eauto.

    destruct b3.

    destruct p6.
    eapply pimpl_ok2; eauto.
    intros; norm'l; split_or_l; unfold stars; simpl;
      norm'l; unfold stars; simpl; inv_option_eq.

    (* we probably have an overly strong loop invariant..  we need to know that
     * for the next loop iteration, [isdir] is $1, since otherwise we don't
     * have a [tree_dir_names_pred].
     *)
    assert (a2 = $1) by admit.
    subst.
    rewrite tree_dir_extract in H0 by eauto; destruct_lift H0.
    cancel.
    instantiate (a0 := d3). cancel.
    destruct (weq b $0); try congruence.
    rewrite H10.

    (* extract the element out of the [fold_left].. *)
    admit.

    step.
    destruct (weq b $0); try congruence.
    rewrite H10.

    (* extract a non-existent element [elem] out of the [fold_left] to produce [None].. *)
    admit.

    step.

    Grab Existential Variables.
    exact emp.
  Qed.

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

  (**
   * XXX later we should probably implement some checks in [rename] to maintain
   * the directory structure as a tree (without loops).
   *)
  Definition rename T fsxp dsrc srcname ddst dstname mscs rx : prog T :=
    let2 (mscs, osrc) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       dsrc srcname mscs;
    match osrc with
    | None => rx (mscs, false)
    | Some (inum, isdir) =>
      let2 (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       dsrc srcname mscs;
      let2 (mscs, odst) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                         ddst dstname mscs;
      match odst with
      | None =>
        let2 (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       ddst dstname inum isdir mscs;
        rx (mscs, ok)
      | Some (inum', isdir') =>
        let2 (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                         ddst dstname mscs;
        let2 (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       ddst dstname inum isdir mscs;
        If (weq isdir' $0) {
          rx (mscs, ok)
        } else {
          let2 (mscs, l) <- SDIR.dslist fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                        inum' mscs;
          match l with
          | nil => rx (mscs, ok)
          | a::b => rx (mscs, false)
          end
        }
      end
    end.

End DIRTREE.
