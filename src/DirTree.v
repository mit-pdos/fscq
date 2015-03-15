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

  Lemma tree_dir_extract_subdir : forall l F dmap name inum,
    (F * name |-> (inum, true))%pred dmap
    -> tree_dir_names_pred' l dmap
    -> dirlist_pred tree_pred l =p=>
       exists F s, F * tree_pred (TreeDir inum s).
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d. simpl in *.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl. cancel. cancel. 2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto.
        congruence.
        apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0. inversion H0. subst.
          cancel. instantiate (a0 := l0). cancel.
        * apply ptsto_mem_except in H0. simpl.
          rewrite IHl. cancel. cancel. 2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
          pred_apply; cancel.
  Qed.

  Lemma tree_dir_extract_file : forall l F dmap name inum,
    (F * name |-> (inum, false))%pred dmap
    -> tree_dir_names_pred' l dmap
    -> dirlist_pred tree_pred l =p=>
       exists F bfile, F * tree_pred (TreeFile inum bfile).
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d; simpl in *.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0; inversion H0. subst. cancel.
        * apply ptsto_mem_except in H0.
          rewrite IHl. cancel. 2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF.
          pred_apply; cancel. auto.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl. cancel. 2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto.
        congruence.
        apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
  Qed.

  Lemma find_subtree_file : forall dlist name inum F A B dmap reclst isub bfmem bfsub,
    (F * name |-> (isub, false))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred tree_pred dlist)%pred bfmem
    -> (A * tree_pred (TreeFile isub bfsub))%pred bfmem
    -> find_subtree (name :: reclst) (TreeDir inum dlist) 
                   = find_subtree reclst (TreeFile isub bfsub).
  Proof.
    induction dlist; simpl; intros.
    apply ptsto_valid' in H. congruence.
    destruct a. unfold find_subtree_helper at 1.
    destruct (string_dec s name); subst.
    - apply ptsto_valid' in H. apply ptsto_valid in H0.
      rewrite H in H0; inversion H0.
      destruct d. simpl in *; subst; f_equal.
      apply sep_star_comm in H1; apply sep_star_assoc_1 in H1.
      apply ptsto_valid in H1. apply ptsto_valid' in H2.
      rewrite H1 in H2. inversion H2. subst; auto.
      simpl in H0; congruence.
    - simpl in *.
      eapply IHdlist. exact inum.
      apply sep_star_comm. eapply ptsto_mem_except_exF.
      apply sep_star_comm; eauto. eauto.
      apply ptsto_mem_except in H0; eauto. 2: eauto.
      pred_apply' H1; cancel.
  Qed.

  Lemma find_name_file : forall dlist name inum F A B dmap reclst isub bfmem bfsub,
    (F * name |-> (isub, false))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred tree_pred dlist)%pred bfmem
    -> (A * tree_pred (TreeFile isub bfsub))%pred bfmem
    -> find_name (name :: reclst) (TreeDir inum dlist) = find_name reclst (TreeFile isub bfsub).
  Proof.
    intros; unfold find_name.
    erewrite find_subtree_file; eauto.
  Qed.

  Lemma find_subtree_helper_dec : forall l name rec F F' m dmap,
    (F * dirlist_pred tree_pred l * F')%pred m
    -> tree_dir_names_pred' l dmap
    -> (fold_right (@find_subtree_helper dirtree rec name) None l = None /\
        dmap name = None) \/
       (exists inum f,
        dmap name = Some (inum, false) /\
        fold_right (find_subtree_helper rec name) None l = rec (TreeFile inum f)) \/
       (exists inum sublist F',
        dmap name = Some (inum, true) /\
        fold_right (find_subtree_helper rec name) None l = rec (TreeDir inum sublist) /\
        (F' * dirlist_pred tree_pred sublist * tree_dir_names_pred inum sublist)%pred m).
  Proof.
    induction l; simpl; intros.
    - left. intuition.
    - destruct a; simpl in *.
      destruct (string_dec s name); subst.
      + right.
        apply ptsto_valid in H0.
        destruct d; simpl in *.
        * left. do 2 eexists. intuition eauto.
        * right. do 3 eexists. intuition eauto.
          pred_apply. cancel.
      + apply ptsto_mem_except in H0.
        edestruct IHl with (m:=m) (rec:=rec) (name:=name); eauto.
        pred_apply. cancel.
        * left. intuition. unfold mem_except in *. destruct (string_dec name s); congruence.
        * right. unfold mem_except in *. destruct (string_dec name s); congruence.
  Qed.

  Lemma find_name_subdir'' : forall fnlist inum l0 l1 A B m,
    (A * dirlist_pred tree_pred l0 * tree_dir_names_pred inum l0)%pred m
    -> (B * dirlist_pred tree_pred l1 * tree_dir_names_pred inum l1)%pred m
    -> find_name fnlist (TreeDir inum l0) = find_name fnlist (TreeDir inum l1).
  Proof.
    unfold find_name.
    induction fnlist; simpl; intros; auto.
    assert (H' := H); assert (H0' := H0).
    unfold tree_dir_names_pred in H, H0.
    destruct_lift H; destruct_lift H0.
    apply ptsto_valid' in H. apply ptsto_valid' in H0.
    rewrite H in H0; inversion H0; subst.
    pose proof (SDIR.rep_mem_eq H6 H8); subst.
    edestruct (find_subtree_helper_dec _ a) with (F:=A) (rec:=find_subtree fnlist) as [HA|HA'];
      edestruct (find_subtree_helper_dec _ a) with (F:=B) (rec:=find_subtree fnlist) as [HB|HB']; eauto;
      try destruct HA'; try destruct HB'; repeat deex; intuition; try congruence.
    - rewrite H1; rewrite H3. auto.
    - rewrite H4; rewrite H9.
      rewrite H3 in H2. inversion H2; subst.
      destruct fnlist; simpl; eauto.
    - rewrite H2; rewrite H1.
      rewrite H3 in H4. inversion H4; subst.
      eauto.
  Qed.

  Lemma find_name_subdir' : forall inum dlist name A B dmap reclst isub bfmem dlsub,
    dmap name = Some (isub, true)
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred tree_pred dlist)%pred bfmem
    -> (A * tree_pred (TreeDir isub dlsub))%pred bfmem
    -> find_name (name :: reclst) (TreeDir inum dlist) 
                   = find_name reclst (TreeDir isub dlsub).
  Proof.
    unfold find_name.
    unfold find_subtree; fold find_subtree.
    induction dlist; simpl; intros.
    congruence.
    destruct a. unfold find_subtree_helper at 1.
    destruct (string_dec s name); subst.
    - destruct d; simpl in *.
      apply ptsto_valid in H0; rewrite H0 in *; congruence.
      apply ptsto_valid in H0. rewrite H0 in H; inversion H; subst.
      eapply find_name_subdir''.
      pred_apply' H1. cancel.
      pred_apply' H2. cancel.
    - apply ptsto_mem_except in H0.
      eapply IHdlist.
      2: eauto.
      unfold mem_except; destruct (string_dec name s); congruence.
      pred_apply' H1. cancel.
      pred_apply' H2. cancel.
  Qed.

  Lemma find_name_subdir : forall dlist name inum F A B dmap reclst isub bfmem dlsub,
    (F * name |-> (isub, true))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred tree_pred dlist)%pred bfmem
    -> (A * tree_pred (TreeDir isub dlsub))%pred bfmem
    -> find_name (name :: reclst) (TreeDir inum dlist) 
                   = find_name reclst (TreeDir isub dlsub).
  Proof.
    intros. apply ptsto_valid' in H.
    eapply find_name_subdir'; eauto.
  Qed.

  Lemma find_subtree_none : forall dlist dmap name fnlist dnum,
    notindomain name dmap
    -> tree_dir_names_pred' dlist dmap
    -> find_subtree (name :: fnlist) (TreeDir dnum dlist) = None.
  Proof.
    induction dlist; simpl; intros; auto.
    destruct a. unfold find_subtree_helper at 1.
    destruct (string_dec s name); subst.
    apply ptsto_valid in H0. congruence.
    eapply notindomain_mem_except' in H.
    apply ptsto_mem_except in H0.
    simpl in *. eapply IHdlist; eauto.
  Qed.

  Lemma find_name_none : forall dlist dmap fnlist dnum name,
    notindomain name dmap
    -> tree_dir_names_pred' dlist dmap
    -> find_name (name :: fnlist) (TreeDir dnum dlist) = None.
  Proof.
    unfold find_name; intros.
    erewrite find_subtree_none; eauto.
  Qed.


  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPMemLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, inum, isdir) <- ForEach fn fnrest fnlist
      Ghost [ mbase m F Fm Ftop treetop bflist freeinodes unused freeinode_pred ]
      Loopvar [ mscs inum isdir ]
      Continuation lrx
      Invariant
        MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
        exists tree,
        [[ (Fm * BFILE.rep bxp ixp bflist *
            BALLOC.rep_gen ibxp freeinodes unused freeinode_pred)%pred
           (list2mem m) ]] *
        [[ (Ftop * tree_pred treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ inum = dirtree_inum tree ]] *
        [[ isdir = dirtree_isdir tree ]] *
        [[ find_name fnlist treetop = find_name fnrest tree ]] *
        [[ isdir = true -> (exists Fsub, 
                   Fsub * tree_pred tree * freeinode_pred)%pred (list2nmem bflist) ]]
      OnCrash
        MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
      Begin
        If (bool_dec isdir true) {
          let^ (mscs, r) <- SDIR.dslookup lxp bxp ixp inum fn mscs;
          match r with
          | Some (inum, isdir) => lrx ^(mscs, inum, isdir)
          | None => rx ^(mscs, None)
          end
        } else {
          rx ^(mscs, None)
        }
    Rof ^(mscs, dnum, true);
    rx ^(mscs, Some (inum, isdir)).

   Local Hint Unfold SDIR.rep_macro rep : hoare_unfold.

  Theorem namei_ok : forall fsxp dnum fnlist mscs,
    {< F mbase m Fm Ftop tree,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = dirtree_inum tree ]] *
           [[ dirtree_isdir tree = true ]]
    POST RET:^(mscs,r)
           MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ r = find_name fnlist tree ]]
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei.
    step.
    step.

    (* isdir = true *)
    destruct d2; simpl in *; subst; intuition.
    step.
    hypmatch (tree_dir_names_pred) as Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.
    do 2 eexists; intuition; eauto.
    pred_apply; cancel.
    pred_apply' H0; cancel.
    destruct a0.

    (* dslookup = Some _: extract subtree before [cancel] *)
    hypmatch (dirlist_pred) as Hx; assert (Horig := Hx).
    destruct_branch; eapply pimpl_ok2; eauto with prog; intros.
    norm'l; split_or_l; unfold stars; simpl;
    norm'l; unfold stars; inv_option_eq; simpl.
    destruct a3.

    (* subtree is a directory *)
    rewrite tree_dir_extract_subdir in Hx by eauto; destruct_lift Hx.
    cancel; try instantiate (1 := (TreeDir a0 l2)); eauto; try cancel.
    erewrite <- find_name_subdir; eauto.
    pred_apply' Horig; cancel.
    hypmatch l2 as Hx; pred_apply' Hx; cancel.

    (* subtree is a file *)
    rewrite tree_dir_extract_file in Hx by eauto; destruct_lift Hx.
    cancel; try instantiate (1 := (TreeFile a0 b0)); eauto; try cancel.
    erewrite <- find_name_file; eauto.
    pred_apply' Horig; cancel.
    hypmatch b0 as Hx; pred_apply' Hx; cancel.

    (* dslookup = None *)
    step.
    erewrite <- find_name_none; eauto.

    (* rx : isdir = false *)
    step.
    hypmatch (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct d2; simpl in *; auto; congruence.

    (* rx : isdir = true *)
    step.
    hypmatch (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct d2; simpl in *; subst; auto.

    Grab Existential Variables.
    all: try exact emp; try exact empty_mem.
  Qed.

  Hint Extern 1 ({{_}} progseq (namei _ _ _ _) _) => apply namei_ok : prog.

  Definition mkfile T fsxp dnum name mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPMemLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, oi) <- BALLOC.alloc_gen lxp ibxp mscs;
    match oi with
    | None => rx ^(mscs, None)
    | Some inum =>
      let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp dnum name inum false mscs;
      If (bool_dec ok true) {
        mscs <- BFILE.bfreset lxp bxp ixp inum mscs;
        rx ^(mscs, Some (inum : addr))
      } else {
        rx ^(mscs, None)
      }
    end.

  Theorem mkfile_ok' : forall fsxp dnum name mscs,
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
            [[ (Fm * rep fsxp Ftop (TreeDir dnum 
                     ((name, TreeFile inum BFILE.bfile0) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} mkfile fsxp dnum name mscs.
  Proof.
    unfold mkfile, rep.
    step.
    subst; simpl in *.
    hypmatch tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.
    unfold SDIR.rep_macro. do 2 eexists. intuition.
    pred_apply. cancel.
    pred_apply. cancel.
    eauto.
    step.
    step.
    step.

    repeat deex.
    hypmatch dirlist_pred as Hx; hypmatch (pimpl p0) as Hy;
    rewrite Hy in Hx; destruct_lift Hx.
    step.
    step.

    apply pimpl_or_r; right. cancel.
    unfold tree_dir_names_pred; cancel; eauto.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    step.
    Grab Existential Variables.
    all: try exact emp.
    all: try exact BFILE.bfile0.
    all: try exact nil.
    all: try exact empty_mem.
  Qed.

  Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
           (* We always modify the memory, because we might allocate the file,
            * but then fail to link it into the directory..  When we return
            * None, the overall transaction should be aborted.
            *)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum 
                       ((name, TreeFile inum BFILE.bfile0) :: tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} mkfile fsxp dnum name mscs.
  Proof.
    intros; eapply pimpl_ok2. apply mkfile_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (a5:=l2). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
  Qed.

  Definition mkdir T fsxp dnum name mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPMemLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, oi) <- BALLOC.alloc_gen lxp ibxp mscs;
    match oi with
    | None => rx ^(mscs, None)
    | Some inum =>
      let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp dnum name inum true mscs;
      If (bool_dec ok true) {
        mscs <- BFILE.bfreset lxp bxp ixp inum mscs;
        rx ^(mscs, Some (inum : addr))
      } else {
        rx ^(mscs, None)
      }
    end.

  Theorem mkdir_ok' : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (TreeDir dnum 
                     ((name, TreeDir inum nil) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} mkdir fsxp dnum name mscs.
  Proof.
    unfold mkdir, rep.
    step.
    subst; simpl in *.
    hypmatch tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.
    do 2 eexists. intuition.
    pred_apply. cancel.
    pred_apply. cancel.
    eauto.
    step.
    step.
    step.

    repeat deex.
    hypmatch dirlist_pred as Hx; hypmatch (pimpl p0) as Hy;
    rewrite Hy in Hx; destruct_lift Hx.
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
    all: try exact emp; try exact nil; try exact empty_mem; try exact BFILE.bfile0.
  Qed.


  Theorem mkdir_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE    MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
           exists m', MEMLOG.rep fsxp.(FSXPMemLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                      ((name, TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH  MEMLOG.would_recover_old fsxp.(FSXPMemLog) F mbase
    >} mkdir fsxp dnum name mscs.
  Proof.
    intros; eapply pimpl_ok2. apply mkdir_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (a5:=l2). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
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

  Definition delete T fsxp dnum name mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPMemLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, oi) <- SDIR.dslookup lxp bxp ixp dnum name mscs;
    match oi with
    | None => rx ^(mscs, false)
    | Some (inum, isdir) =>
      mscs <- IfRx irx (bool_dec isdir false) {
        irx mscs
      } else {
        let^ (mscs, l) <- SDIR.dslist lxp bxp ixp inum mscs;
        match l with
        | nil => irx mscs
        | a::b => rx ^(mscs, false)
        end
      };
      let^ (mscs, ok) <- SDIR.dsunlink lxp bxp ixp dnum name mscs;
      If (bool_dec ok true) {
        mscs <- BALLOC.free_gen lxp ibxp inum mscs;
        rx ^(mscs, true)
      } else {
        rx ^(mscs, false)
      }
    end.

  Definition rename T fsxp dsrc srcname ddst dstname mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPMemLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, osrc) <- SDIR.dslookup lxp bxp ixp dsrc srcname mscs;
    match osrc with
    | None => rx ^(mscs, false)
    | Some (inum, isdir) =>
      let^ (mscs, ok) <- SDIR.dsunlink lxp bxp ixp dsrc srcname mscs;
      let^ (mscs, odst) <- SDIR.dslookup lxp bxp ixp ddst dstname mscs;
      match odst with
      | None =>
        let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp ddst dstname inum isdir mscs;
        rx ^(mscs, ok)
      | Some (inum', isdir') =>
        let^ (mscs, ok) <- SDIR.dsunlink lxp bxp ixp ddst dstname mscs;
        let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp ddst dstname inum isdir mscs;
        If (bool_dec isdir' false) {
          rx ^(mscs, ok)
        } else {
          let^ (mscs, l) <- SDIR.dslist lxp bxp ixp inum' mscs;
          match l with
          | nil => rx ^(mscs, ok)
          | a::b => rx ^(mscs, false)
          end
        }
      end
    end.

  Definition rename_correct T fsxp dnum srcpath srcname dstpath dstname mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPMemLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, osrcdir) <- namei fsxp dnum srcpath mscs;
    match osrcdir with
    | None => rx ^(mscs, false)
    | Some (dsrc, isdir) => if (isdir : bool) then rx ^(mscs, false) else
      let^ (mscs, osrc) <- SDIR.dslookup lxp bxp ixp dsrc srcname mscs;
      match osrc with
      | None => rx ^(mscs, false)
      | Some (inum, inum_isdir) =>
        let^ (mscs, ok) <- SDIR.dsunlink lxp bxp ixp dsrc srcname mscs;
        let^ (mscs, odstdir) <- namei fsxp dnum dstpath mscs;
        match odstdir with
        | None => rx ^(mscs, false)
        | Some (ddst, isdir) => if (isdir : bool) then rx ^(mscs, false) else
          let^ (mscs, odst) <- SDIR.dslookup lxp bxp ixp ddst dstname mscs;
          match odst with
          | None =>
            let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp ddst dstname inum inum_isdir mscs;
            rx ^(mscs, ok)
          | Some (dst_inum, dst_isdir) =>
            mscs <- IfRx irx (bool_dec dst_isdir true) {
              let^ (mscs, l) <- SDIR.dslist lxp bxp ixp dst_inum mscs;
              match l with
              | nil => irx mscs
              | a::b => rx ^(mscs, false)
              end
            } else {
              irx mscs
            };
            let^ (mscs, ok) <- SDIR.dsunlink lxp bxp ixp ddst dstname mscs;
            let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp ddst dstname inum inum_isdir mscs;
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
