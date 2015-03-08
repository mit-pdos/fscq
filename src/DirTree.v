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

  Definition find_name_helper (rec : dirtree -> addr -> addr -> option (addr * addr)) name
                              (arg : string * addr * dir_item) (accum : option (addr * addr)) :=
    let '(name', inum', item') := arg in
    if string_dec name' name then
    match item' with
    | DirFile _ => rec nil inum' $0
    | DirSubdir tree' => rec tree' inum' $1
    end
    else accum.

  Fixpoint find_name (fnlist : list string) (tree : dirtree) (inum : addr) (isdir : addr) :=
    match fnlist with
    | nil => Some (inum, isdir)
    | name :: rest =>
      if weq isdir $0 then None else
      fold_right (find_name_helper (find_name rest) name) None tree
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

  (**
   * [F] represents the other parts of the file system above [rootinum],
   * in cases where [rootinum] is a subdirectory somewhere in the tree.
   *)
  Definition rep fsxp F rootinum tree :=
    (exists bflist freeinodes freeinode_pred_unused freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
     BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred *
     [[ (F * tree_dir_names_pred rootinum tree * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

  Lemma tree_dir_extract : forall d F dmap name inum isdir,
    (F * name |-> (inum, isdir))%pred dmap
    -> isdir <> $0
    -> tree_dir_names_pred' d dmap
    -> tree_pred d =p=> exists F s, F * tree_dir_names_pred inum s * tree_pred s.
  Proof.
    induction d; intros.
    - simpl in *. eapply emp_complete in H1; [| apply emp_empty_mem ]; subst.
      apply sep_star_empty_mem in H; intuition.
      exfalso. eapply ptsto_empty_mem. eauto.
    - destruct a. destruct p. destruct d0; simpl in *.
      + apply ptsto_mem_except in H1 as H1'.
        rewrite IHd. cancel. cancel.
        2: eauto. 2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H1 H).
        destruct (string_dec name s). exfalso. apply H2; eauto.
        destruct (weq isdir $0); try congruence.
        apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H1. apply ptsto_valid' in H.
          rewrite H in H1. inversion H1. subst.
          cancel. unfold tree_pred. instantiate (a0:=l). cancel.
        * apply ptsto_mem_except in H1.
          rewrite IHd. cancel. cancel.
          2: eauto. 2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
          pred_apply; cancel.
  Qed.

  Lemma find_name_file : forall tree rec name inum F dmap,
    (F * name |-> (inum, $0))%pred dmap
    -> tree_dir_names_pred' tree dmap
    -> fold_right (find_name_helper rec name) None tree = rec nil inum $0.
  Proof.
    induction tree; simpl; intros.
    - eapply emp_complete in H0; [| apply emp_empty_mem ]; subst.
      apply sep_star_empty_mem in H; intuition.
      exfalso. eapply ptsto_empty_mem; eauto.
    - destruct a. destruct p. unfold find_name_helper; fold (find_name_helper rec name).
      destruct (string_dec s name); subst.
      + apply ptsto_valid' in H. destruct d.
        * apply ptsto_valid in H0. rewrite H in H0. inversion H0; eauto.
        * apply ptsto_valid in H0. rewrite H in H0. discriminate.
      + eapply IHtree.
        apply sep_star_comm. eapply ptsto_mem_except_exF. apply sep_star_comm; eauto.
        instantiate (1:=s); eauto.
        destruct d; apply ptsto_mem_except in H0; eauto.
  Qed.

  Lemma find_name_subdir_helper : forall reclst inum a b bfmem,
       (exists F, F * tree_dir_names_pred inum a)%pred bfmem
    -> (exists F, F * tree_dir_names_pred inum b)%pred bfmem
    -> find_name reclst a inum $1 = find_name reclst b inum $1.
  Proof.
    unfold tree_dir_names_pred; intros.
    destruct_lift H. destruct_lift H0.
    apply ptsto_valid' in H. apply ptsto_valid' in H0.
    rewrite H in H0; inversion H0; subst. clear H H0 bfmem.
    admit.
  Qed.

  Lemma find_name_subdir : forall tree reclst name inum subtree isdir F dmap bfmem,
    (F * name |-> (inum, isdir))%pred dmap
    -> tree_dir_names_pred' tree dmap
    -> isdir <> $0
    -> (exists F, F * tree_dir_names_pred inum subtree)%pred bfmem
    -> (exists F, F * tree_pred tree)%pred bfmem
    -> fold_right (find_name_helper (find_name reclst) name) None tree =
       find_name reclst subtree inum isdir.
  Proof.
    induction tree; simpl; intros.
    - eapply emp_complete in H0; [| apply emp_empty_mem ]; subst.
      apply sep_star_empty_mem in H; intuition.
      exfalso. eapply ptsto_empty_mem; eauto.
    - destruct a. destruct p. unfold find_name_helper; fold (find_name_helper (find_name reclst) name).
      destruct (string_dec s name); subst.
      + apply ptsto_valid' in H. destruct d.
        * apply ptsto_valid in H0. rewrite H in H0. inversion H0; subst. congruence.
        * apply ptsto_valid in H0. rewrite H in H0. inversion H0; subst.
          simpl in *.
          eapply find_name_subdir_helper.
          pred_apply' H3. cancel.
          pred_apply' H2. cancel.
      + eapply IHtree.
        apply sep_star_comm. eapply ptsto_mem_except_exF. apply sep_star_comm; eauto.
        instantiate (1:=s); eauto.
        destruct d; apply ptsto_mem_except in H0; eauto.
        eauto.
        eauto.
        pred_apply' H3. cancel.
  Qed.

  Lemma find_name_none : forall tree rec name dmap,
    notindomain name dmap
    -> tree_dir_names_pred' tree dmap
    -> fold_right (find_name_helper rec name) None tree = None.
  Proof.
    induction tree; simpl; intros; try reflexivity.
    destruct a. destruct p.
    unfold find_name_helper; fold (find_name_helper rec name).
    destruct (string_dec s name); subst.
    - exfalso. eapply notindomain_not_indomain; eauto.
      destruct d; apply ptsto_valid in H0; firstorder.
    - eapply notindomain_mem_except' in H.
      destruct d; apply ptsto_mem_except in H0;
        eapply IHtree; eauto.
  Qed.

  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let3 (mscs, inum, isdir) <- ForEach fn fnlist
      Ghost mbase m F Ftop treetop bflist
      Loopvar mscs_inum_isdir <- (mscs, dnum, $1)
      Continuation lrx
      Invariant
        MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs_inum_isdir.(fst).(fst) *
        exists tree,
        [[ (F * rep fsxp Ftop dnum treetop)%pred (list2mem m) ]] *
        [[ mscs_inum_isdir.(snd) <> $0 ->
           (exists F', tree_dir_names_pred mscs_inum_isdir.(fst).(snd) tree *
            tree_pred tree * F')%pred (list2nmem bflist) ]] *
        [[ find_name fnlist treetop dnum $1 = find_name fn tree mscs_inum_isdir.(fst).(snd) mscs_inum_isdir.(snd) ]]
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
    {< F mbase m Ftop tree,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp Ftop dnum tree)%pred (list2mem m) ]]
    POST:(mscs,r)
           [[ r = find_name fnlist tree dnum $1 ]] *
           MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs
    CRASH  MEMLOG.log_intact fsxp.(FSXPMemLog) mbase
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei, rep.
    step.

    match goal with
    | [ H: _ (list2nmem _) |- _ ] => pred_apply' H
    end.
    cancel.

    step.
    step.
    destruct (weq b $0); congruence.

    (* destruct some [exists] terms before creating evars.. *)
    eapply pimpl_ok2; [ eauto with prog |].
    intros; norm'l; unfold stars; simpl.
    apply H11 in H14 as H14'.
    unfold tree_dir_names_pred in H14'; destruct_lift H14'.

    cancel.
    unfold SDIR.rep_macro. do 2 eexists. intuition.
    (* Be careful which [list2mem] we pick! *)
    pred_apply' H3. cancel.
    pred_apply' H0. cancel.
    eauto.

    repeat destruct_branch.
    eapply pimpl_ok2; eauto.
    intros; norm'l; split_or_l; unfold stars; simpl;
      norm'l; unfold stars; simpl; inv_option_eq.

    rewrite H10; clear H10. destruct (weq b $0); try congruence.
    (* check whether, for the next loop iteration, [isdir] is $0 or $1 *)
    destruct (weq a2 $0).
    cancel.

    eapply find_name_file; eauto.

    rewrite tree_dir_extract in H0 by eauto. destruct_lift H0.
    cancel.
    instantiate (a := d3). cancel.

    eapply find_name_subdir; eauto.
    pred_apply' H0. cancel.
    pred_apply' H4. cancel.

    step.
    rewrite H10; clear H10. destruct (weq b $0); try congruence.
    erewrite find_name_none; eauto.

    step.
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
