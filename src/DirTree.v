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
Require Import Array.

Set Implicit Arguments.

Module DIRTREE.

  Inductive dirtree :=
  | TreeFile : addr -> BFILE.bfile -> dirtree
  | TreeDir  : addr -> list (string * dirtree) -> dirtree.

  (**
   * Helpers for looking up names in a tree, and for updating trees.
   *)
  Definition dirtree_inum (dt : dirtree) :=
    match dt with
    | TreeFile inum _ => inum
    | TreeDir  inum _ => inum
    end.

  Definition dirtree_isdir (dt : dirtree) :=
    match dt with
    | TreeFile _ _ => false
    | TreeDir  _ _ => true
    end.

  Definition find_subtree_helper {T} (rec : dirtree -> option T) name
                                 (dirent : string * dirtree)
                                 (accum : option T) :=
    let (ent_name, ent_item) := dirent in
    if string_dec ent_name name then rec ent_item else accum.

  Fixpoint find_subtree (fnlist : list string) (tree : dirtree) :=
    match fnlist with
    | nil => Some tree
    | name :: suffix =>
      match tree with
      | TreeFile _ _ => None
      | TreeDir _ dirents =>
        fold_right (find_subtree_helper (find_subtree suffix) name) None dirents
      end
    end.

  Definition find_name (fnlist : list string) (tree : dirtree) :=
    match find_subtree fnlist tree with
    | None => None
    | Some subtree =>
      match subtree with
      | TreeFile inum _ => Some (inum, false)
      | TreeDir inum _ => Some (inum, true)
      end
    end.

  Definition update_subtree_helper (rec : dirtree -> dirtree)
                                   name
                                   (dirent : string * dirtree) :=
    let (ent_name, ent_tree) := dirent in
    if string_dec ent_name name then (ent_name, rec ent_tree) else dirent.

  Fixpoint update_subtree (fnlist : list string) (subtree : dirtree) (tree : dirtree) :=
    match fnlist with
    | nil => subtree
    | name :: rest =>
      match tree with
      | TreeFile _ _ => tree
      | TreeDir inum ents =>
        TreeDir inum (map (update_subtree_helper (update_subtree rest subtree) name) ents)
      end
    end.

  (**
   * Predicates capturing the representation invariant of a directory tree.
   *)
  Fixpoint tree_dir_names_pred' (dirents : list (string * dirtree)) : @pred _ string_dec (addr * bool) :=
    match dirents with
    | nil => emp
    | (name, subtree) :: dirlist' => name |-> (dirtree_inum subtree, dirtree_isdir subtree) * tree_dir_names_pred' dirlist'
    end.

  Definition tree_dir_names_pred (dir_inum : addr) (dirents : list (string * dirtree)) : @pred _ eq_nat_dec _ := (
    exists f dsmap,
    #dir_inum |-> f *
    [[ SDIR.rep f dsmap ]] *
    [[ tree_dir_names_pred' dirents dsmap ]])%pred.

  Section DIRITEM.

    Variable F : dirtree -> @pred nat eq_nat_dec BFILE.bfile.
    Variable Fexcept : dirtree -> @pred nat eq_nat_dec BFILE.bfile.

    Fixpoint dirlist_pred (dirlist : list (string * dirtree)) : @pred _ eq_nat_dec _ := (
      match dirlist with
      | nil => emp
      | (_, e) :: dirlist' => F e * dirlist_pred dirlist'
      end)%pred.

    Fixpoint dirlist_pred_except (name : string) (dirlist : list (string * dirtree)) : @pred _ eq_nat_dec _ := (
      match dirlist with
      | nil => emp
      | (ename, e) :: dirlist' =>
        (if string_dec ename name then Fexcept e else F e) * dirlist_pred_except name dirlist'
      end)%pred.

  End DIRITEM.

  Fixpoint tree_pred e := (
    match e with
    | TreeFile inum f => #inum |-> f
    | TreeDir inum s => tree_dir_names_pred inum s * dirlist_pred tree_pred s
    end)%pred.

  Fixpoint tree_pred_except (fnlist : list string) e {struct fnlist} :=  (
    match fnlist with
    | nil => emp
    | fn :: suffix =>
      match e with
      | TreeFile inum f => #inum |-> f
      | TreeDir inum s => tree_dir_names_pred inum s *
                          dirlist_pred_except (tree_pred) (tree_pred_except suffix) fn s
      end
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

  (**
   * Theorems about extracting and folding back subtrees from a tree.
   *)
  Lemma dirlist_pred_except_notfound : forall l fnlist name,
    ~ In name (map fst l) ->
    dirlist_pred tree_pred l =p=> dirlist_pred_except tree_pred (tree_pred_except fnlist) name l.
  Proof.
    induction l; simpl; intros.
    cancel.
    destruct a. destruct (string_dec s name); subst.
    - edestruct H. eauto.
    - cancel. eauto.
  Qed.

  Lemma tree_dir_names_pred'_app : forall l1 l2,
    tree_dir_names_pred' (l1 ++ l2) =p=> tree_dir_names_pred' l1 * tree_dir_names_pred' l2.
  Proof.
    induction l1; simpl; intros.
    cancel.
    destruct a; destruct d; cancel; eauto.
  Qed.

  Lemma dir_names_distinct' : forall l m F,
    (F * tree_dir_names_pred' l)%pred m ->
    NoDup (map fst l).
  Proof.
    induction l; simpl; intros.
    constructor.
    destruct a; simpl in *.
    destruct d.
    - constructor; [| eapply IHl; pred_apply' H; cancel ].
      intro Hin.
      apply in_map_iff in Hin. repeat deex. destruct x.
      apply in_split in H2. repeat deex.
      eapply ptsto_conflict_F with (a := s). pred_apply' H.
      rewrite tree_dir_names_pred'_app. simpl.
      destruct d; cancel.
    - constructor; [| eapply IHl; pred_apply' H; cancel ].
      intro Hin.
      apply in_map_iff in Hin. repeat deex. destruct x.
      apply in_split in H2. repeat deex.
      eapply ptsto_conflict_F with (a := s). pred_apply' H.
      rewrite tree_dir_names_pred'_app. simpl.
      destruct d; cancel.
  Qed.

  Lemma dir_names_distinct : forall l w,
    tree_dir_names_pred w l =p=> tree_dir_names_pred w l * [[ NoDup (map fst l) ]].
  Proof.
    unfold tree_dir_names_pred; intros.
    cancel; eauto.
    eapply dir_names_distinct'.
    pred_apply' H1. cancel.
  Qed.

  Theorem subtree_extract : forall fnlist tree subtree,
    find_subtree fnlist tree = Some subtree ->
    tree_pred tree =p=> tree_pred_except fnlist tree * tree_pred subtree.
  Proof.
    induction fnlist; simpl; intros.
    - inversion H; subst. cancel.
    - destruct tree; try discriminate; simpl.
      rewrite dir_names_distinct at 1; cancel.
      induction l; simpl in *; try discriminate.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite IHfnlist; eauto.
        cancel.
        apply dirlist_pred_except_notfound.
        inversion H3; eauto.
      + cancel.
        inversion H3; eauto.
  Qed.

  Theorem tree_dir_names_pred_update' : forall fnlist subtree subtree' d,
    find_subtree fnlist d = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    (dirtree_inum d, dirtree_isdir d) =
    (dirtree_inum (update_subtree fnlist subtree' d),
     dirtree_isdir (update_subtree fnlist subtree' d)).
  Proof.
    destruct fnlist; simpl; intros.
    congruence.
    destruct d; auto.
  Qed.

  Lemma tree_dir_names_pred'_distinct : forall l,
    tree_dir_names_pred' l =p=> tree_dir_names_pred' l * [[ NoDup (map fst l) ]].
  Proof.
    unfold pimpl; intros.
    assert ((emp * tree_dir_names_pred' l)%pred m) by (pred_apply; cancel).
    apply dir_names_distinct' in H0 as Hnodup.
    clear H0. pred_apply; cancel.
  Qed.

  Theorem tree_dir_names_pred_notfound : forall l fnlist subtree' name,
    ~ In name (map fst l) ->
    tree_dir_names_pred' l =p=>
    tree_dir_names_pred' (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    induction l; simpl; intros.
    cancel.
    destruct a; simpl.
    destruct (string_dec s name); subst; try intuition.
    cancel.
    eauto.
  Qed.

  Theorem tree_dir_names_pred'_update : forall l fnlist subtree subtree' name,
    fold_right (find_subtree_helper (find_subtree fnlist) name) None l = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    tree_dir_names_pred' l =p=>
    tree_dir_names_pred' (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    intros; rewrite tree_dir_names_pred'_distinct; cancel.
    induction l; simpl; intros.
    cancel.

    destruct a.
    case_eq (update_subtree_helper (update_subtree fnlist subtree') name (s, d)); intros.
    unfold update_subtree_helper in H2.
    simpl in *.
    destruct (string_dec s name); subst.
    - inversion H2; clear H2; subst; simpl in *.
      erewrite <- tree_dir_names_pred_update'; eauto. cancel.
      apply tree_dir_names_pred_notfound. inversion H4; eauto.
    - inversion H2; clear H2; subst; simpl in *.
      cancel. apply H2. inversion H4; eauto.
  Qed.

  Theorem tree_dir_names_pred_update : forall w l fnlist subtree subtree' name,
    fold_right (find_subtree_helper (find_subtree fnlist) name) None l = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    tree_dir_names_pred w l =p=>
    tree_dir_names_pred w (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    unfold tree_dir_names_pred; intros; cancel; eauto.
    pred_apply.
    eapply tree_dir_names_pred'_update; eauto.
  Qed.

  Lemma dirlist_pred_except_notfound' : forall l fnlist name subtree',
    ~ In name (map fst l) ->
    dirlist_pred_except tree_pred (tree_pred_except fnlist) name l =p=>
    dirlist_pred tree_pred (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    induction l; simpl; intros.
    cancel.
    destruct a; simpl. destruct (string_dec s name); subst.
    - edestruct H. eauto.
    - cancel. eauto.
  Qed.

  Theorem subtree_absorb : forall fnlist tree subtree subtree',
    find_subtree fnlist tree = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    tree_pred_except fnlist tree * tree_pred subtree' =p=>
    tree_pred (update_subtree fnlist subtree' tree).
  Proof.
    induction fnlist; simpl; intros.
    - inversion H; subst. cancel.
    - destruct tree; try discriminate; simpl.
      rewrite dir_names_distinct at 1; cancel.
      rewrite tree_dir_names_pred_update; eauto.
      cancel.

      induction l; simpl in *; intros; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite <- IHfnlist; eauto. cancel.
        inversion H6.
        apply dirlist_pred_except_notfound'; eauto.
      + cancel.
        inversion H6.
        rewrite <- H2; eauto.
        cancel.
  Qed.

  (**
   * Helpers for higher levels that need to reason about updated trees.
   *)

  Theorem find_update_subtree : forall fnlist tree subtree subtree0,
    find_subtree fnlist tree = Some subtree0 ->
    dirtree_inum subtree0 = dirtree_inum subtree ->
    find_subtree fnlist (update_subtree fnlist subtree tree) = Some subtree.
  Proof.
    induction fnlist; simpl; try congruence; intros.
    destruct tree; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl.
    - destruct (string_dec a a); try congruence; eauto.
    - destruct (string_dec s a); try congruence; eauto.
  Qed.

  Hint Resolve find_update_subtree.

  (**
   * XXX
   * Might be useful to have another theorem about how pathname-to-inode mappings
   * are preserved across [update_subtree] for other paths.  In particular, if we
   * do an [update_subtree] for some path [p] to a new subtree [subtree], then
   * paths that do not start with [p] should not be affected.  Furthermore, paths
   * [p' = p ++ suffix] should also be unaffected if:
   *
   *   find_subtree suffix subtree = find_subtree p' tree
   *
   * However, it's not clear yet who needs this kind of theorem.  This might be
   * necessary for applications above FS.v, because they will have to prove that
   * their file descriptors / inode numbers remain valid after they performed
   * some operation on the tree.
   *)

  Lemma tree_dir_extract_subdir : forall dlist F dmap name inum,
    (F * name |-> (inum, true))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> dirlist_pred tree_pred dlist =p=>
       exists F s, F * tree_dir_names_pred inum s * tree_pred (TreeDir inum s).
  Proof.
    admit.
(*
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
*)
  Qed.

  Lemma tree_dir_extract_file : forall dlist F dmap name inum,
    (F * name |-> (inum, false))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> dirlist_pred tree_pred dlist =p=>
       exists F bfile, F * tree_pred (TreeFile inum bfile).
  Proof.
    admit.
  Qed.

  Lemma find_name_file : forall name inum F dmap bfmem reclst isub dlist bfsub,
    (F * name |-> (isub, false))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (exists F, F * tree_pred (TreeFile isub bfsub))%pred bfmem
    -> (exists F, F * tree_pred (TreeDir inum dlist))%pred bfmem
    -> find_name (name :: reclst) (TreeDir inum dlist) = find_name reclst (TreeFile isub bfsub).
  Proof.
    admit.
(*
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
*)
  Qed.

(*
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
*)

  Lemma find_name_subdir : forall reclst name inum dlist dlsub isub F dmap bfmem,
    (F * name |-> (isub, true))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (exists F, F * tree_dir_names_pred isub dlsub)%pred bfmem
    -> (exists F, F * tree_pred (TreeDir inum dlist))%pred bfmem
    -> find_name (name :: reclst) (TreeDir inum dlist) = find_name reclst (TreeDir isub dlsub).
  Proof.
    admit.
(*
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
*)
  Qed.

  Lemma find_name_none : forall dlist dmap name fnlist dnum,
    notindomain name dmap
    -> tree_dir_names_pred' dlist dmap
    -> find_name (name :: fnlist) (TreeDir dnum dlist) = None.
  Proof.
    admit.
(*
    induction tree; simpl; intros; try reflexivity.
    destruct a. destruct p.
    unfold find_name_helper; fold (find_name_helper rec name).
    destruct (string_dec s name); subst.
    - exfalso. eapply notindomain_not_indomain; eauto.
      destruct d; apply ptsto_valid in H0; firstorder.
    - eapply notindomain_mem_except' in H.
      destruct d; apply ptsto_mem_except in H0;
        eapply IHtree; eauto.
*)
  Qed.

  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let^ (mscs, inum, isdir) <- ForEach fn fnrest fnlist
      Ghost [ mbase m F Fm Ftop treetop bflist freeinodes freeinode_pred_unused freeinode_pred ]
      Loopvar [ mscs inum isdir ]
      Continuation lrx
      Invariant
        MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
        exists tree,
        [[ (Fm * BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist *
            BALLOC.rep_gen fsxp.(FSXPInodeAlloc) freeinodes freeinode_pred_unused freeinode_pred)%pred
           (list2mem m) ]] *
        [[ (Ftop * tree_pred treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ isdir = true ->
           (exists Fsub, Fsub * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ inum = dirtree_inum tree ]] *
        [[ isdir = dirtree_isdir tree ]] *
        [[ find_name fnlist treetop = find_name fnrest tree ]]
      OnCrash
        MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
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
    {< F mbase m Fm Ftop tree,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = dirtree_inum tree ]] * [[ dirtree_isdir tree = true ]]
    POST RET:^(mscs,r)
           [[ r = find_name fnlist tree ]] *
           [[ exists Fsub subtree,
              r = Some (dirtree_inum subtree, true) ->
              (Fm * rep fsxp Fsub subtree)%pred (list2mem m) ]] *
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei, rep.
    step.
    step.
    step.

    destruct d2; simpl in *.
    unfold find_name in *; simpl in *; auto.
    congruence.

    exists emp. exists (TreeFile $0 BFILE.bfile0). intros; discriminate.

    (* destruct some [exists] terms before creating evars.. *)
    eapply pimpl_ok2; [ eauto with prog |].
    intros; norm'l; unfold stars; simpl.
    destruct a1; intuition.

    destruct d2; simpl in *; try congruence; subst.
    destruct_lift H0.
    unfold tree_dir_names_pred in H0; destruct_lift H0.

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


    destruct a4.
    assert (Hx := H0).
    rewrite tree_dir_extract_subdir in H0 by eauto. destruct_lift H0.
    cancel.
    instantiate (a := (TreeDir a3 l2)).
    cancel.
    auto.
    auto.

    erewrite <- find_name_subdir; eauto.
    pred_apply' H0; cancel. simpl. 
    unfold tree_dir_names_pred.
    pred_apply' Hx; cancel. eauto. eauto.

    assert (Hx := H0).
    rewrite tree_dir_extract_file in H0. destruct_lift H0.
    cancel.
    instantiate (a := (TreeFile a3 b0)).
    auto. auto.

    erewrite <- find_name_file; eauto.
    pred_apply' H0; cancel.
    simpl. unfold tree_dir_names_pred.
    pred_apply' Hx; cancel. eauto. eauto. eauto. eauto.

    step.

    erewrite <- find_name_none. eauto. eauto. eauto.
    exists emp. exists (TreeFile $0 BFILE.bfile0).
    discriminate.

    step.
    destruct d2; unfold find_name in *; simpl in *; subst; eauto.
    destruct a1. intuition. destruct_lift H.
    clear H7 H9. repeat eexists.
    intro Heq; inversion Heq; subst.
    pred_apply.
    instantiate (subtree := d2). cancel.

    exists emp. exists (TreeFile $0 BFILE.bfile0).
    intros; discriminate.
  Qed.

  Hint Extern 1 ({{_}} progseq (namei _ _ _ _) _) => apply namei_ok : prog.

  Definition mkfile T fsxp dnum name mscs rx : prog T :=
    let^ (mscs, oi) <- BALLOC.alloc_gen fsxp.(FSXPMemLog) fsxp.(FSXPInodeAlloc) mscs;
    match oi with
    | None => rx ^(mscs, None)
    | Some inum =>
      let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                     dnum name inum false mscs;
      If (bool_dec ok true) {
        mscs <- BFILE.bfreset fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                              inum mscs;
        rx ^(mscs, Some (inum : addr))
      } else {
        rx ^(mscs, None)
      }
    end.

  Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           (* We always modify the memory, because we might allocate the file,
            * but then fail to link it into the directory..  When we return
            * None, the overall transaction should be aborted.
            *)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (TreeDir dnum ((name, TreeFile inum BFILE.bfile0) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
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
        mscs <- BFILE.bfreset fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                              inum mscs;
        rx ^(mscs, Some (inum : addr))
      } else {
        rx ^(mscs, None)
      }
    end.

  Theorem mkdir_ok : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (TreeDir dnum ((name, TreeDir inum nil) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
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

  Hint Extern 1 ({{_}} progseq (mkfile _ _ _ _) _) => apply mkfile_ok : prog.
  Hint Extern 1 ({{_}} progseq (mkdir _ _ _ _) _) => apply mkdir_ok : prog.

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

  Definition rename_correct T fsxp dnum srcpath srcname dstpath dstname mscs rx : prog T :=
    let^ (mscs, osrcdir) <- namei fsxp dnum srcpath mscs;
    match osrcdir with
    | None => rx ^(mscs, false)
    | Some (dsrc, isdir) => if (isdir : bool) then rx ^(mscs, false) else
      let^ (mscs, osrc) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                         dsrc srcname mscs;
      match osrc with
      | None => rx ^(mscs, false)
      | Some (inum, inum_isdir) =>
        let^ (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                         dsrc srcname mscs;
        let^ (mscs, odstdir) <- namei fsxp dnum dstpath mscs;
        match odstdir with
        | None => rx ^(mscs, false)
        | Some (ddst, isdir) => if (isdir : bool) then rx ^(mscs, false) else
          let^ (mscs, odst) <- SDIR.dslookup fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                             ddst dstname mscs;
          match odst with
          | None =>
            let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                           ddst dstname inum inum_isdir mscs;
            rx ^(mscs, ok)
          | Some (dst_inum, dst_isdir) =>
            mscs <- IfRx irx (bool_dec dst_isdir true) {
              let^ (mscs, l) <- SDIR.dslist fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                            dst_inum mscs;
              match l with
              | nil => irx mscs
              | a::b => rx ^(mscs, false)
              end
            } else {
              irx mscs
            };
            let^ (mscs, ok) <- SDIR.dsunlink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                             ddst dstname mscs;
            let^ (mscs, ok) <- SDIR.dslink fsxp.(FSXPMemLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode)
                                           ddst dstname inum inum_isdir mscs;
            rx ^(mscs, ok)
          end
        end
      end
    end.

  Definition read T fsxp inum off mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread (FSXPMemLog fsxp) (FSXPInode fsxp) inum off mscs;
    rx ^(mscs, v).

  Definition write T fsxp inum off v mscs rx : prog T :=
    mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) inum off v mscs;
    rx mscs.

  Definition truncate T fsxp inum nblocks mscs rx : prog T :=
    let^ (mscs, ok) <- BFILE.bftrunc (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                     inum nblocks mscs;
    rx ^(mscs, ok).

  Definition getlen T fsxp inum mscs rx : prog T :=
    let^ (mscs, len) <- BFILE.bflen (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, len).

  Definition getattr T fsxp inum mscs rx : prog T :=
    let^ (mscs, attr) <- BFILE.bfgetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, attr).

  Definition setattr T fsxp inum attr mscs rx : prog T :=
    mscs <- BFILE.bfsetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum attr mscs;
    rx mscs.

  Theorem read_ok : forall fsxp inum off mscs,
    {< F mbase m pathname Fm Ftop tree f B v,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET:^(mscs,r)
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ r = v ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} read fsxp inum off mscs.
  Proof.
    unfold read, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem write_ok : forall fsxp inum off v mscs,
    {< F mbase m pathname Fm Ftop tree f B v0,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET:mscs
           exists m' tree' f',
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]] *
           [[ f' = BFILE.Build_bfile (Array.upd (BFILE.BFData f) off v) (BFILE.BFAttr f) ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} write fsxp inum off v mscs.
  Proof.
    unfold write, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto.
  Qed.

  Theorem truncate_ok : forall fsxp inum nblocks mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:^(mscs, ok)
           exists m',
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
          ([[ ok = false ]] \/
           [[ ok = true ]] *
           exists tree' f',
           [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.Build_bfile (setlen (BFILE.BFData f) #nblocks $0) (BFILE.BFAttr f) ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} truncate fsxp inum nblocks mscs.
  Proof.
    unfold truncate, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto. cancel.
  Qed.

  Theorem getlen_ok : forall fsxp inum mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:^(mscs,r)
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ r = $ (length (BFILE.BFData f)) ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} getlen fsxp inum mscs.
  Proof.
    unfold getlen, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem getattr_ok : forall fsxp inum mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:^(mscs,r)
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ r = BFILE.BFAttr f ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} getattr fsxp inum mscs.
  Proof.
    unfold getattr, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem setattr_ok : forall fsxp inum attr mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:mscs
           exists m' tree' f',
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.Build_bfile (BFILE.BFData f) attr ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} setattr fsxp inum attr mscs.
  Proof.
    unfold setattr, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (truncate _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} progseq (getlen _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} progseq (getattr _ _ _) _) => apply getattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (setattr _ _ _ _) _) => apply setattr_ok : prog.

End DIRTREE.
