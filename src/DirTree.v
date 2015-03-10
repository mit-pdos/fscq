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

  Inductive dirtree :=
  | TreeFile : addr -> BFILE.bfile -> dirtree
  | TreeDir  : addr -> list (string * dirtree) -> dirtree.

  Definition dirtree_inum (dt : dirtree) :=
    match dt with
    | TreeFile inum _ => inum
    | TreeDir  inum _ => inum
    end.

  Definition find_name_helper {T} (rec : dirtree -> option T) name
                              (dirent : string * dirtree)
                              (accum : option T) :=
    let (ent_name, ent_item) := dirent in
    if string_dec ent_name name then rec ent_item else accum.

  Fixpoint find_name (fnlist : list string) (tree : dirtree) :=
    match fnlist with
    | nil =>
      match tree with
      | TreeFile inum _ => Some (inum, false)
      | TreeDir inum _ => Some (inum, true)
      end
    | name :: rest =>
      match tree with
      | TreeFile _ _ => None
      | TreeDir _ dirents =>
        fold_right (find_name_helper (find_name rest) name) None dirents
      end
    end.

  Fixpoint find_file (fnlist : list string) (tree : dirtree) :=
    match fnlist with
    | nil =>
      match tree with
      | TreeFile inum f => Some (inum, f)
      | TreeDir _ _ => None
      end
    | name :: rest =>
      match tree with
      | TreeFile _ _ => None
      | TreeDir _ dirents =>
        fold_right (find_name_helper (find_file rest) name) None dirents
      end
    end.

  Fixpoint tree_dir_names_pred' (dirents : list (string * dirtree)) : @pred _ string_dec (addr * bool) :=
    match dirents with
    | nil => emp
    | (name, TreeFile inum f) :: dirlist' => name |-> (inum, false) * tree_dir_names_pred' dirlist'
    | (name, TreeDir  inum s) :: dirlist' => name |-> (inum, true)  * tree_dir_names_pred' dirlist'
    end.

  Definition tree_dir_names_pred (dir_inum : addr) (dirents : list (string * dirtree)) : @pred _ eq_nat_dec _ := (
    exists f dsmap,
    #dir_inum |-> f *
    [[ SDIR.rep f dsmap ]] *
    [[ tree_dir_names_pred' dirents dsmap ]])%pred.

  Section DIRITEM.

  Variable F : dirtree -> @pred nat eq_nat_dec BFILE.bfile.

  Fixpoint dirlist_pred' (dirlist : list (string * dirtree)) : @pred _ eq_nat_dec _ := (
    match dirlist with
    | nil => emp
    | (_, e) :: dirlist' => F e * dirlist_pred' dirlist'
    end)%pred.

  End DIRITEM.

  Fixpoint tree_pred e := (
    match e with
    | TreeFile inum f => #inum |-> f
    | TreeDir inum s => tree_dir_names_pred inum s * dirlist_pred' tree_pred s
    end)%pred.

  (**
   * [F] represents the other parts of the file system above [tree],
   * in cases where [tree] is a subdirectory somewhere in the tree.
   *)
  Definition rep fsxp F tree :=
    (exists bflist freeinodes freeinode_pred_unused freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
     BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred *
     [[ (F * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

(*
  Lemma tree_dir_extract : forall d F dmap name inum,
    (F * name |-> (inum, true))%pred dmap
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
*)

  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let^ (mscs, inum, isdir) <- ForEach fn fnrest fnlist
      Ghost [ mbase m F Ftop treetop bflist freeinodes freeinode_pred_unused freeinode_pred ]
      Loopvar [ mscs inum isdir ]
      Continuation lrx
      Invariant
        MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
        exists tree,
        [[ (F * BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
            BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred)%pred
           (list2mem m) ]] *
        [[ (Ftop * tree_pred treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ isdir = true ->
           (exists Fsub, Fsub * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ inum = dirtree_inum tree ]] *
        [[ find_name fnlist treetop = find_name fnrest tree ]]
      OnCrash
        MEMLOG.would_recover_old fsxp.(FSXPMemLog) mbase
      Begin
        If (bool_dec isdir false) {
          rx ^(mscs, None)
        } else {
          let^ (mscs, r) <- SDIR.dslookup (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                          inum fn mscs;
          match r with
          | None => rx ^(mscs, None)
          | Some (inum, isdir) => lrx ^(mscs, inum, isdir)
          end
        }
    Rof ^(mscs, dnum, true);
    rx ^(mscs, Some (inum, isdir)).

  Theorem namei_ok : forall fsxp dnum fnlist mscs,
    {< F mbase m Ftop tree,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = dirtree_inum tree ]]
    POST RET:^(mscs,r)
           [[ r = find_name fnlist tree ]] *
           [[ exists Fsub subtree,
              r = Some (dirtree_inum subtree, true) ->
              (F * rep fsxp Fsub subtree)%pred (list2mem m) ]] *
           MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) mbase
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei, rep.
    step.
    step.
    step.

    destruct (weq a1 $0); congruence.
    exists $0. exists emp. exists nil. intros; discriminate.

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

    rewrite H10; clear H10. destruct (weq a1 $0); try congruence.
    (* check whether, for the next loop iteration, [isdir] is $0 or $1 *)
    destruct (weq a6 $0).
    cancel.

    eapply find_name_file; eauto.

    rewrite tree_dir_extract in H0 by eauto. destruct_lift H0.
    cancel.
    instantiate (a := d3). cancel.

    eapply find_name_subdir; eauto.
    pred_apply' H0. cancel.
    pred_apply' H4. cancel.

    step.
    rewrite H10; clear H10. destruct (weq a1 $0); try congruence.
    erewrite find_name_none; eauto.

    exists $0. exists emp. exists nil. intros; discriminate.

    step.

    destruct (weq a1 $0) as [Ha1|Ha1].
    exists $0; exists emp; exists nil; subst. inversion 1.
    apply H10 in Ha1. destruct_lift Ha1.

    exists a0; do 2 eexists; intro Heq; inversion Heq; subst.
    pred_apply' H3. clear H5. cancel.
    instantiate (subtree := d2). cancel.
  Qed.

  Definition mkfile T fsxp dnum name mscs rx : prog T :=
    let^ (mscs, oi) <- BALLOC.alloc_gen fsxp.(FSXPMemLog) fsxp.(FSXPInodeAlloc) mscs;
    match oi with
    | None => rx ^(mscs, None)
    | Some inum =>
      let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                     dnum name inum false mscs;
      If (bool_dec ok true) {
        mscs <- BFILE.bftrunc fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                              inum mscs;
        rx ^(mscs, Some (inum : addr))
      } else {
        rx ^(mscs, None)
      }
    end.

  Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase m Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           (* We always modify the memory, because we might allocate the file,
            * but then fail to link it into the directory..  When we return
            * None, the overall transaction should be aborted.
            *)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (F * rep fsxp Ftop (TreeDir dnum ((name, TreeFile inum BFILE.bfile0) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) mbase
    >} mkfile fsxp dnum name mscs.
  Proof.
    unfold mkfile, rep.
    step.
    unfold tree_dir_names_pred in H5. destruct_lift H5.
    step.
    unfold SDIR.rep_macro. do 2 eexists. intuition.
    pred_apply. cancel.
    pred_apply. cancel.
    eauto.
    unfold SDIR.rep_macro.
    step.
    step.
    step.

    repeat deex.
    rewrite H12 in H0. destruct_lift H0.
    step.
    step.

    apply pimpl_or_r; right. cancel.
    unfold tree_dir_names_pred; cancel; eauto.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    step.
    Grab Existential Variables.
    exact BFILE.bfile0.
    exact emp.
    exact nil.
    exact emp.
    exact empty_mem.
    exact emp.
    exact emp.
  Qed.

  Definition mkdir T fsxp dnum name mscs rx : prog T :=
    let^ (mscs, oi) <- BALLOC.alloc_gen fsxp.(FSXPMemLog) fsxp.(FSXPInodeAlloc) mscs;
    match oi with
    | None => rx ^(mscs, None)
    | Some inum =>
      let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                     dnum name inum true mscs;
      If (bool_dec ok true) {
        mscs <- BFILE.bftrunc fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                              inum mscs;
        rx ^(mscs, Some (inum : addr))
      } else {
        rx ^(mscs, None)
      }
    end.

  Theorem mkdir_ok : forall fsxp dnum name mscs,
    {< F mbase m Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (F * rep fsxp Ftop (TreeDir dnum ((name, TreeDir inum nil) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) mbase
    >} mkdir fsxp dnum name mscs.
  Proof.
    unfold mkdir, rep.
    step.
    unfold tree_dir_names_pred in H5. destruct_lift H5.
    step.
    unfold SDIR.rep_macro. do 2 eexists. intuition.
    pred_apply. cancel.
    pred_apply. cancel.
    eauto.
    unfold SDIR.rep_macro.
    step.
    step.
    step.

    repeat deex.
    rewrite H12 in H0. destruct_lift H0.
    step.
    step.
    apply pimpl_or_r; right. cancel.

    unfold tree_dir_names_pred at 1. cancel; eauto.
    unfold tree_dir_names_pred; cancel.
    apply SDIR.bfile0_empty.
    apply emp_empty_mem.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    step.
    Grab Existential Variables.
    exact BFILE.bfile0.
    exact emp.
    exact nil.
    exact emp.
    exact empty_mem.
    exact emp.
    exact emp.
  Qed.

  Definition dir_updater := dirtree -> dirtree.

  Definition update_tree_helper (rec : dirtree -> dirtree)
                                name
                                (dirent : string * dirtree) :=
    let (ent_name, ent_tree) := dirent in
    if string_dec ent_name name then (ent_name, rec ent_tree) else dirent.

  Fixpoint update_tree (fnlist : list string) (updater : dir_updater) (tree : dirtree) :=
    match fnlist with
    | nil => updater tree
    | name :: rest =>
      match tree with
      | TreeFile _ _ => tree
      | TreeDir inum ents =>
        TreeDir inum (map (update_tree_helper (update_tree rest updater) name) ents)
      end
    end.

  Definition add_to_dir (name : string) (newitem : dirtree) tree :=
    match tree with
    | TreeFile _ _ => tree
    | TreeDir inum ents => TreeDir inum ((name, newitem) :: ents)
    end.

  Fixpoint delete_from_list (name : string) (ents : list (string * dirtree)) :=
    match ents with
    | nil => nil
    | hd :: rest =>
      let (ent_name, ent_item) := hd in
      if string_dec ent_name name then
        rest
      else
        hd :: rest
    end.

  Definition delete_from_dir (name : string) tree :=
    match tree with
    | TreeFile _ _ => tree
    | TreeDir inum ents => TreeDir inum (delete_from_list name ents)
    end.

(*
  Theorem update_subtree : forall fsxp fnlist treetop m F Ftop itop
                                  Fsub isub treesub
                                  m' updater,
    (F * rep fsxp Ftop itop treetop)%pred (list2mem m) ->
    find_name fnlist treetop itop $1 = Some (isub, $1) ->
    (F * rep fsxp Fsub isub treesub)%pred (list2mem m) ->
    (F * rep fsxp Fsub isub (updater treesub))%pred (list2mem m') ->
    (F * rep fsxp Ftop itop (update_tree fnlist updater treetop))%pred (list2mem m').
  Proof.
    induction fnlist; simpl.
    intros.
    inversion H0; subst. pred_apply. unfold rep. cancel. admit.
    induction treetop; simpl; intros.
    discriminate.
    pred_apply. cancel.
    admit.
  Qed.
*)

  Definition delete T fsxp dnum name mscs rx : prog T :=
    let^ (mscs, oi) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                     dnum name mscs;
    match oi with
    | None => rx ^(mscs, false)
    | Some (inum, isdir) =>
      mscs <- IfRx irx (bool_dec isdir false) {
        irx mscs
      } else {
        let^ (mscs, l) <- SDIR.dslist fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                      inum mscs;
        match l with
        | nil => irx mscs
        | a::b => rx ^(mscs, false)
        end
      };
      let^ (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       dnum name mscs;
      If (bool_dec ok true) {
        mscs <- BALLOC.free_gen fsxp.(FSXPMemLog) fsxp.(FSXPInodeAlloc) inum mscs;
        rx ^(mscs, true)
      } else {
        rx ^(mscs, false)
      }
    end.

  (**
   * XXX later we should probably implement some checks in [rename] to maintain
   * the directory structure as a tree (without loops).
   *)
  Definition rename T fsxp dsrc srcname ddst dstname mscs rx : prog T :=
    let^ (mscs, osrc) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       dsrc srcname mscs;
    match osrc with
    | None => rx ^(mscs, false)
    | Some (inum, isdir) =>
      let^ (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       dsrc srcname mscs;
      let^ (mscs, odst) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                         ddst dstname mscs;
      match odst with
      | None =>
        let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       ddst dstname inum isdir mscs;
        rx ^(mscs, ok)
      | Some (inum', isdir') =>
        let^ (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                         ddst dstname mscs;
        let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                       ddst dstname inum isdir mscs;
        If (bool_dec isdir' false) {
          rx ^(mscs, ok)
        } else {
          let^ (mscs, l) <- SDIR.dslist fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                        inum' mscs;
          match l with
          | nil => rx ^(mscs, ok)
          | a::b => rx ^(mscs, false)
          end
        }
      end
    end.

  Definition read T fsxp inum off mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread (FSXPMemLog fsxp) (FSXPInode fsxp) inum off mscs;
    rx ^(mscs, v).

  Definition write T fsxp inum off v mscs rx : prog T :=
    mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) inum off v mscs;
    rx mscs.

  Theorem read_ok : forall fsxp inum off mscs,
    {< F mbase m rootdnum pathname Ftop tree f B v,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ rootdnum = dirtree_inum tree ]] *
           [[ find_file pathname tree = Some (inum, f) ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET:^(mscs,r)
           MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ r = v ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) mbase
    >} read fsxp inum off mscs.
  Proof.
    admit.
  Qed.

  Definition set_file (f : dirtree) (oldtree : dirtree) := f.

  Theorem write_ok : forall fsxp inum off v mscs,
    {< F mbase m rootdnum pathname Ftop tree f B v0,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m) mscs *
           [[ (F * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ rootdnum = dirtree_inum tree ]] *
           [[ find_file pathname tree = Some (inum, f) ]] *
           [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET:mscs
           exists m' tree' f',
           MEMLOG.rep fsxp.(FSXPMemLog) (ActiveTxn mbase m') mscs *
           [[ (F * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_tree pathname (set_file (TreeFile inum f')) tree ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]] *
           [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) mbase
    >} write fsxp inum off v mscs.
  Proof.
    admit.
  Qed.

End DIRTREE.
