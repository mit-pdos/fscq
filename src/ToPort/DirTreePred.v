Require Import Bool.
Require Import Word.
Require Import Balloc.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DirCache.
Require Import DirTreeDef.
Require Import FSLayout.
Require Import GenSepN.
Require Import SepAuto.

Import ListNotations.

Module SDIR := CacheOneDir.

Set Implicit Arguments.

  (**
   * Predicates capturing the representation invariant of a directory tree.
   *)

  Fixpoint tree_dir_names_pred' (dirents : list (string * dirtree)) : @pred _ string_dec (addr * bool) :=
    match dirents with
    | nil => emp
    | (name, subtree) :: dirlist' => name |-> (dirtree_inum subtree, dirtree_isdir subtree) * tree_dir_names_pred' dirlist'
    end.

  Definition tree_dir_names_pred ibxp (dir_inum : addr) (dirents : list (string * dirtree)) 
                                 : @pred _ eq_nat_dec _ := (
    exists f dsmap,
    dir_inum |-> f *
    [[ IAlloc.ino_valid ibxp dir_inum ]] *
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


    Variable UpdateF : dirtree -> dirtree.

    Fixpoint dirlist_update (dirlist : list (string * dirtree)) : list (string * dirtree) :=
      match dirlist with
      | nil => nil
      | (name, subtree) :: dirlist' => (name, UpdateF subtree) :: (dirlist_update dirlist')
      end.


    Variable T : Type.
    Variable CombineF : dirtree -> list T.

    Fixpoint dirlist_combine (dirlist : list (string * dirtree)) : list T :=
      match dirlist with
      | nil => nil
      | (name, subtree) :: dirlist' => (CombineF subtree) ++ (dirlist_combine dirlist')
      end.

  End DIRITEM.

  Lemma dirlist_combine_app: forall l (f : dirtree -> list addr) a,
    dirlist_combine f (a::l) = dirlist_combine f [a] ++ (dirlist_combine f l).
  Proof.
    intros. 
    rewrite cons_app.
    unfold dirlist_combine; subst; simpl.
    destruct a.
    rewrite app_nil_r; eauto.
  Qed.


  Fixpoint tree_pred ibxp e := (
    match e with
    | TreeFile inum f =>
      exists cache,
      inum |-> (BFILE.mk_bfile (DFData f) (DFAttr f) cache) * [[ IAlloc.ino_valid ibxp inum ]]
    | TreeDir inum s => tree_dir_names_pred ibxp inum s * dirlist_pred (tree_pred ibxp) s
    end)%pred.

  Fixpoint tree_pred_except ibxp (fnlist : list string) e {struct fnlist} :=  (
    match fnlist with
    | nil => emp
    | fn :: suffix =>
      match e with
      | TreeFile inum f =>
        exists cache,
        inum |-> (BFILE.mk_bfile (DFData f) (DFAttr f) cache) * [[ IAlloc.ino_valid ibxp inum ]]
      | TreeDir inum s => tree_dir_names_pred ibxp inum s *
                          dirlist_pred_except (tree_pred ibxp) (tree_pred_except ibxp suffix) fn s
      end
    end)%pred.


  Fixpoint dirtree_update_inode t inum off v :=
    match t with
    | TreeFile inum' f => if (addr_eq_dec inum inum') then
          let f' := mk_dirfile (updN (DFData f) off v) (DFAttr f) in (TreeFile inum f')
          else (TreeFile inum' f)
    | TreeDir inum' ents =>
      TreeDir inum' (dirlist_update (fun t' => dirtree_update_inode t' inum off v) ents)
    end.

  (**
   * Theorems about extracting and folding back subtrees from a tree.
   *)
  Lemma dirlist_pred_except_notfound : forall xp l fnlist name,
    ~ In name (map fst l) ->
    dirlist_pred (tree_pred xp) l <=p=>
      dirlist_pred_except (tree_pred xp) (tree_pred_except xp fnlist) name l.
  Proof.
    induction l; simpl; intros; auto.
    split; destruct a.
    destruct (string_dec s name); subst.
    edestruct H. eauto.
    cancel. apply IHl; auto.

    destruct (string_dec s name); subst.
    edestruct H. eauto.
    cancel. apply IHl; auto.
  Qed.

  Lemma tree_dir_names_pred'_app : forall l1 l2,
    tree_dir_names_pred' (l1 ++ l2) <=p=> tree_dir_names_pred' l1 * tree_dir_names_pred' l2.
  Proof.
    split; induction l1; simpl; intros.
    cancel.
    destruct a; destruct d; cancel; eauto.
    cancel.
    destruct a; destruct d; cancel; rewrite sep_star_comm; eauto.
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
      cancel.
  Qed.

  Lemma dir_names_distinct : forall xp l w,
    tree_dir_names_pred xp w l =p=> tree_dir_names_pred xp w l * [[ NoDup (map fst l) ]].
  Proof.
    unfold tree_dir_names_pred; intros.
    cancel; eauto.
    eapply dir_names_distinct'.
    pred_apply' H1. cancel.
  Qed.

  Section DIRTREE_IND2.

    Variable P : dirtree -> Prop.
    Variable dirtree_ind2' : forall (t : dirtree), P t.
    Variable dirtree_ind2_Hdir : forall inum tree_ents,
                                 Forall P (map snd tree_ents) -> P (TreeDir inum tree_ents).

    Fixpoint dirtree_ind2_list (tree_ents : list (string * dirtree)) (inum : addr) :
                               P (TreeDir inum tree_ents).
      apply dirtree_ind2_Hdir.
      induction tree_ents; simpl.
      constructor.
      constructor.
      apply dirtree_ind2'.
      apply IHtree_ents.
    Defined.

  End DIRTREE_IND2.

  Fixpoint dirtree_ind2 (P : dirtree -> Prop)
                        (Hfile : forall inum bf, P (TreeFile inum bf))
                        (Hdir : forall inum tree_ents,
                         Forall P (map snd tree_ents) -> P (TreeDir inum tree_ents))
                        (d : dirtree) {struct d} : P d.
    refine
      match d with
      | TreeFile inum bf => _
      | TreeDir inum tree_ents => _
      end.
    apply Hfile.
    specialize (dirtree_ind2 P Hfile Hdir).
    apply dirtree_ind2_list.
    apply dirtree_ind2.
    apply Hdir.
  Defined.

  Lemma dirlist_pred_split : forall a b f,
    (dirlist_pred f (a ++ b) <=p=> dirlist_pred f a * dirlist_pred f b)%pred.
  Proof.
    induction a; simpl; intros.
    - split. cancel. cancel.
    - destruct a. split.
      cancel. apply IHa.
      cancel. rewrite IHa. cancel.
  Qed.

  Theorem subtree_fold : forall xp fnlist tree subtree,
    find_subtree fnlist tree = Some subtree ->
    tree_pred_except xp fnlist tree * tree_pred xp subtree =p=> tree_pred xp tree.
  Proof.
    induction fnlist; simpl; intros.
    - inversion H; subst. cancel.
    - destruct tree; try discriminate; simpl.
      rewrite dir_names_distinct at 1.
      cancel.
      induction l; simpl in *; try discriminate.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite sep_star_assoc_2.
        rewrite sep_star_comm with (p1 := tree_pred xp subtree).
        rewrite IHfnlist; eauto.
        cancel.
        apply dirlist_pred_except_notfound; eauto.
        inversion H4; eauto.
      + cancel.
        rewrite sep_star_comm.
        eapply H0.
        inversion H4; eauto.
  Qed.

  Theorem subtree_extract : forall xp fnlist tree subtree,
    find_subtree fnlist tree = Some subtree ->
    tree_pred xp tree =p=> tree_pred_except xp fnlist tree * tree_pred xp subtree.
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

  Lemma tree_dir_extract_subdir : forall xp l F dmap name inum,
    (F * name |-> (inum, true))%pred dmap
    -> tree_dir_names_pred' l dmap
    -> dirlist_pred (tree_pred xp) l =p=>
       exists F s, F * tree_pred xp (TreeDir inum s) *
       [[ forall dnum, find_subtree [name] (TreeDir dnum l) = Some (TreeDir inum s) ]].
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d. simpl in *.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl. cancel.
        eassign s0; eassign inum; cancel.

        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec s name). exfalso. apply H2; eauto. congruence. eauto.

        2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto.
        congruence.
        apply sep_star_comm.
        eapply ptsto_mem_except_exF; eauto.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0. inversion H0. subst.
          cancel. instantiate (s0 := l0). cancel.
          destruct (string_dec s s); congruence.
        * apply ptsto_mem_except in H0. simpl.
          rewrite IHl. cancel.
          eassign s0; eassign inum; cancel.
          destruct (string_dec s name); try congruence; eauto.
          2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
          pred_apply; cancel.
  Qed.

  Lemma tree_dir_extract_file : forall xp l F dmap name inum,
    (F * name |-> (inum, false))%pred dmap
    -> tree_dir_names_pred' l dmap
    -> dirlist_pred (tree_pred xp) l =p=>
       exists F bfile, F * tree_pred xp (TreeFile inum bfile) *
       [[ forall dnum, find_subtree [name] (TreeDir dnum l) = Some (TreeFile inum bfile) ]].
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d; simpl in *.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0; inversion H0. subst. cancel.
          destruct (string_dec s s); congruence.
        * apply ptsto_mem_except in H0.
          rewrite IHl with (inum:=inum). cancel.
          destruct (string_dec s name); try congruence; eauto.
          2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF.
          pred_apply; cancel. congruence.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl with (inum:=inum). cancel.

        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec s name). exfalso. apply H2; eauto. congruence. eauto.

        2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto.
        congruence.
        apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
  Qed.

  Lemma find_subtree_file : forall xp dlist name inum F A B dmap reclst isub bfmem bfsub,
    (F * name |-> (isub, false))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred (tree_pred xp) dlist)%pred bfmem
    -> (A * tree_pred xp (TreeFile isub bfsub))%pred bfmem
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
      destruct_lift H1; destruct_lift H2.
      apply sep_star_assoc_1 in H1.
      setoid_rewrite sep_star_comm in H1.
      apply sep_star_assoc_2 in H1.
      apply ptsto_valid' in H1. apply ptsto_valid' in H2.
      rewrite H1 in H2. inversion H2. subst; auto.
      destruct d; destruct bfsub; simpl in *; congruence.
      simpl in H0; congruence.
    - simpl in *.
      eapply IHdlist. exact inum.
      apply sep_star_comm. eapply ptsto_mem_except_exF.
      apply sep_star_comm; eauto. eauto.
      apply ptsto_mem_except in H0; eauto. 2: eauto.
      pred_apply' H1; cancel.
  Qed.

  Lemma find_name_file : forall xp dlist name inum F A B dmap reclst isub bfmem bfsub,
    (F * name |-> (isub, false))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred (tree_pred xp) dlist)%pred bfmem
    -> (A * tree_pred xp (TreeFile isub bfsub))%pred bfmem
    -> find_name (name :: reclst) (TreeDir inum dlist) = find_name reclst (TreeFile isub bfsub).
  Proof.
    intros; unfold find_name.
    erewrite find_subtree_file; eauto.
  Qed.

  Lemma find_subtree_helper_dec : forall xp l name rec F F' m dmap,
    (F * dirlist_pred (tree_pred xp) l * F')%pred m
    -> tree_dir_names_pred' l dmap
    -> (fold_right (@find_subtree_helper dirtree rec name) None l = None /\
        dmap name = None) \/
       (exists inum f,
        dmap name = Some (inum, false) /\
        fold_right (find_subtree_helper rec name) None l = rec (TreeFile inum f)) \/
       (exists inum sublist F',
        dmap name = Some (inum, true) /\
        fold_right (find_subtree_helper rec name) None l = rec (TreeDir inum sublist) /\
        (F' * dirlist_pred (tree_pred xp) sublist * tree_dir_names_pred xp inum sublist)%pred m).
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
        eassign F'. cancel.
        * left. intuition. unfold mem_except in *. destruct (string_dec name s); congruence.
        * right. unfold mem_except in *. destruct (string_dec name s); congruence.
  Qed.

  Lemma find_name_subdir'' : forall xp fnlist inum l0 l1 A B m,
    (A * dirlist_pred (tree_pred xp) l0 * tree_dir_names_pred xp inum l0)%pred m
    -> (B * dirlist_pred (tree_pred xp) l1 * tree_dir_names_pred xp inum l1)%pred m
    -> find_name fnlist (TreeDir inum l0) = find_name fnlist (TreeDir inum l1).
  Proof.
    unfold find_name.
    induction fnlist; simpl; intros; auto.
    assert (H' := H); assert (H0' := H0).
    unfold tree_dir_names_pred in H, H0.
    destruct_lift H; destruct_lift H0.
    apply ptsto_valid' in H. apply ptsto_valid' in H0.
    rewrite H in H0; inversion H0; subst.
    pose proof (SDIR.rep_mem_eq H6 H9); subst.
    edestruct (find_subtree_helper_dec xp l0 a) with (F:=A) (rec:=find_subtree fnlist) as [HA|HA'];
      edestruct (find_subtree_helper_dec xp l1 a) with (F:=B) (rec:=find_subtree fnlist) as [HB|HB']; eauto;
      try destruct HA'; try destruct HB'; repeat deex; intuition; try congruence.
    - rewrite H1; rewrite H3. auto.
    - rewrite H4; rewrite H11.
      rewrite H3 in H2. inversion H2; subst.
      destruct fnlist; simpl; eauto.
    - rewrite H2; rewrite H1.
      rewrite H3 in H4. inversion H4; subst.
      eauto.
  Qed.

  Lemma find_name_subdir' : forall xp inum dlist name A B dmap reclst isub bfmem dlsub,
    dmap name = Some (isub, true)
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred (tree_pred xp) dlist)%pred bfmem
    -> (A * tree_pred xp (TreeDir isub dlsub))%pred bfmem
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
      eapply find_name_subdir'' with (xp := xp).
      pred_apply' H1. cancel.
      pred_apply' H2. cancel.
    - apply ptsto_mem_except in H0.
      eapply IHdlist.
      2: eauto.
      unfold mem_except; destruct (string_dec name s); congruence.
      pred_apply' H1. cancel.
      pred_apply' H2. cancel.
  Qed.

  Lemma find_name_subdir : forall xp dlist name inum F A B dmap reclst isub bfmem dlsub,
    (F * name |-> (isub, true))%pred dmap
    -> tree_dir_names_pred' dlist dmap
    -> (B * dirlist_pred (tree_pred xp) dlist)%pred bfmem
    -> (A * tree_pred xp (TreeDir isub dlsub))%pred bfmem
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

  Lemma dirname_not_in' : forall ents F name m,
    (tree_dir_names_pred' ents * F)%pred m ->
    notindomain name m ->
    ~ In name (map fst ents).
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; simpl in *; intuition; subst.
    apply sep_star_assoc in H.
    apply ptsto_valid in H; congruence.
    eapply IHents; eauto.
    pred_apply' H; cancel.
  Qed.

  Lemma dirname_not_in : forall ents name m,
    tree_dir_names_pred' ents m ->
    notindomain name m ->
    ~ In name (map fst ents).
  Proof.
    intros.
    eapply dirname_not_in'; eauto.
    pred_apply' H; cancel.
  Qed.


  Lemma dir_names_pred_delete' : forall l name m,
    tree_dir_names_pred' l m
    -> tree_dir_names_pred' (delete_from_list name l) (mem_except m name).
  Proof.
    induction l; simpl; intros; auto.
    apply emp_mem_except; auto.
    destruct a.
    destruct (string_dec s name); subst.
    apply ptsto_mem_except in H; auto.
    simpl.
    eapply ptsto_mem_except_F; eauto.
  Qed.

  Lemma dir_names_delete : forall xp dlist name dnum dfile dmap,
    tree_dir_names_pred' dlist dmap
    -> SDIR.rep dfile (mem_except dmap name)
    -> IAlloc.ino_valid xp dnum
    -> (dnum |-> dfile) =p=> tree_dir_names_pred xp dnum (delete_from_list name dlist).
  Proof.
    destruct dlist; simpl; intros; auto.
    unfold tree_dir_names_pred.
    cancel; eauto.
    apply emp_mem_except; eauto.

    destruct p.
    destruct (string_dec s name); subst.
    apply ptsto_mem_except in H.
    unfold tree_dir_names_pred.
    cancel; eauto.

    unfold tree_dir_names_pred; simpl.
    cancel; eauto.
    eapply ptsto_mem_except_F; eauto; intros.
    apply dir_names_pred_delete'; auto.
  Qed.

  Lemma dirlist_delete_file : forall xp dlist name inum dmap,
    tree_dir_names_pred' dlist dmap
    -> (name |-> (inum, false) * exists F, F)%pred dmap
    -> dirlist_pred (tree_pred xp) dlist =p=>
        (inum |->?) * dirlist_pred (tree_pred xp) (delete_from_list name dlist).
  Proof.
    induction dlist; simpl; intros; auto.
    destruct_lift H0.
    apply ptsto_valid in H0; congruence.

    destruct a.
    destruct (string_dec s name); subst.
    destruct_lift H0.
    apply ptsto_valid in H.
    apply ptsto_valid in H0.
    rewrite H in H0; inversion H0.
    destruct d; simpl in *; try congruence.
    cancel.

    simpl.
    apply ptsto_mem_except in H.
    rewrite <- sep_star_assoc.
    rewrite IHdlist with (inum:=inum); eauto.
    cancel.
    eapply ptsto_mem_except_exF; eauto.
  Qed.


  Lemma dlist_is_nil : forall d l m,
    SDIR.rep d m -> emp m
    -> tree_dir_names_pred' l m
    -> l = nil.
  Proof.
    intros; destruct l; simpl in *; auto.
    destruct p.
    apply ptsto_valid in H1; congruence.
  Qed.

  Lemma dirlist_pred_except_delete_eq' : forall xp l name,
    NoDup (map fst l) ->
    dirlist_pred_except (tree_pred xp) (tree_pred_except xp nil) name l
    <=p=> dirlist_pred (tree_pred xp) (delete_from_list name l).
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst.
    destruct (string_dec s name); subst.
    rewrite dirlist_pred_except_notfound with (fnlist := nil); eauto.
    split; cancel.
    split; cancel; apply IHl; auto.
  Qed.

  Lemma dirlist_pred_except_delete : forall xp l m name,
    tree_dir_names_pred' l m ->
    dirlist_pred_except (tree_pred xp) (tree_pred_except xp nil) name l
      <=p=> dirlist_pred (tree_pred xp) (delete_from_list name l).
  Proof.
    intros.
    apply pimpl_star_emp in H.
    apply dir_names_distinct' in H.
    split; apply dirlist_pred_except_delete_eq'; eauto.
  Qed.

 Lemma find_dirlist_exists' : forall l name m inum isdir,
    tree_dir_names_pred' l m
    -> (name |-> (inum, isdir) * exists F, F)%pred m
    -> exists sub, find_dirlist name l = Some sub
            /\ inum = dirtree_inum sub /\ isdir = dirtree_isdir sub.
  Proof.
    induction l; simpl; intros; auto.
    destruct_lift H0.
    apply ptsto_valid in H0; congruence.

    destruct a.
    destruct (string_dec s name); subst; eauto.
    apply ptsto_valid in H; apply ptsto_valid in H0.
    rewrite H in H0; inversion H0; subst; eauto.

    apply ptsto_mem_except in H.
    eapply IHl; eauto.
    eapply ptsto_mem_except_exF; eauto.
  Qed.

  Lemma find_dirlist_exists : forall l name m F inum isdir,
    tree_dir_names_pred' l m
    -> (F * name |-> (inum, isdir))%pred m
    -> exists sub, find_dirlist name l = Some sub
         /\ inum = dirtree_inum sub /\ isdir = dirtree_isdir sub.
  Proof.
    intros; destruct_lift H.
    eapply find_dirlist_exists'; eauto.
    pred_apply; cancel.
  Qed.

  Lemma dirlist_extract' : forall xp l name sub,
    find_dirlist name l = Some sub
    -> NoDup (map fst l)
    -> dirlist_pred (tree_pred xp) l =p=> tree_pred xp sub *
                  dirlist_pred_except (tree_pred xp) (tree_pred_except xp nil) name l.
  Proof.
    induction l; simpl; intros; try congruence.
    destruct a. destruct (string_dec s name).

    inversion H; inversion H0; subst.
    erewrite dirlist_pred_except_notfound with (name := name); eauto.
    instantiate (1 := nil); cancel.

    inversion H0; subst; clear H0.
    rewrite <- sep_star_assoc.
    setoid_rewrite <- sep_star_comm at 3.
    rewrite sep_star_assoc.
    rewrite <- IHl; eauto.
  Qed.

  Lemma dirlist_extract : forall xp F m l inum isdir name,
    tree_dir_names_pred' l m
    -> (F * name |-> (inum, isdir))%pred m
    -> dirlist_pred (tree_pred xp) l =p=> (exists sub, tree_pred xp sub *
         [[ inum = dirtree_inum sub  /\ isdir = dirtree_isdir sub ]]) *
         dirlist_pred_except (tree_pred xp) (tree_pred_except xp nil) name l.
  Proof.
    intros.
    apply pimpl_star_emp in H as Hx.
    apply dir_names_distinct' in Hx.
    pose proof (find_dirlist_exists l H H0); deex.
    cancel.
    apply dirlist_extract'; auto.
  Qed.

  Lemma dirlist_extract_subdir : forall xp F m l inum name,
    tree_dir_names_pred' l m
    -> (F * name |-> (inum, true))%pred m
    -> dirlist_pred (tree_pred xp) l =p=> 
           (exists s, tree_dir_names_pred xp inum s * dirlist_pred (tree_pred xp) s ) *
            dirlist_pred_except (tree_pred xp) (tree_pred_except xp nil) name l.
  Proof.
    intros.
    unfold pimpl; intros.
    pose proof (dirlist_extract xp l H H0 m0 H1).
    destruct_lift H2.
    destruct dummy; simpl in *; subst; try congruence.
    pred_apply; cancel.
    eassign l0; cancel.
  Qed.


  Lemma ptsto_subtree_exists' : forall name ents dmap inum isdir,
    tree_dir_names_pred' ents dmap
    -> (name |-> (inum, isdir) * exists F, F)%pred dmap
    -> exists subtree, find_dirlist name ents = Some subtree
         /\ inum = dirtree_inum subtree /\ isdir = dirtree_isdir subtree.
  Proof.
    induction ents; simpl; intros; auto.
    apply ptsto_valid in H0; congruence.
    destruct a; simpl.
    destruct (string_dec s name); subst.

    apply ptsto_valid in H; apply ptsto_valid in H0.
    rewrite H in H0; inversion H0; subst.
    eexists; intuition.

    apply ptsto_mem_except in H.
    simpl in *; eapply IHents; eauto.
    eapply ptsto_mem_except_exF; eauto.
  Qed.

  Lemma ptsto_subtree_exists : forall F name ents dmap inum isdir,
    tree_dir_names_pred' ents dmap
    -> (F * name |-> (inum, isdir))%pred dmap
    -> exists subtree, find_dirlist name ents = Some subtree
         /\ inum = dirtree_inum subtree /\ isdir = dirtree_isdir subtree.
  Proof.
    intros.
    eapply ptsto_subtree_exists'; eauto.
    pred_apply; cancel.
  Qed.

  Lemma fold_back_dir_pred : forall xp dnum dirfile ents dsmap,
    tree_dir_names_pred' ents dsmap
    -> SDIR.rep dirfile dsmap
    -> IAlloc.ino_valid xp dnum
    -> dnum |-> dirfile * dirlist_pred (tree_pred xp) ents =p=> tree_pred xp (TreeDir dnum ents).
  Proof.
    simpl; intros.
    unfold tree_dir_names_pred.
    cancel; eauto.
  Qed.

  Lemma dirlist_pred_extract : forall xp ents name subtree,
    find_dirlist name ents = Some subtree
    -> NoDup (delete_from_list name ents)
    -> dirlist_pred (tree_pred xp) ents =p=>
       tree_pred xp subtree * dirlist_pred (tree_pred xp) (delete_from_list name ents).
  Proof.
    induction ents; intros; auto.
    inversion H.
    destruct a; simpl in *.
    destruct (string_dec s name); subst.
    inversion H; subst; auto.
    inversion H0; subst.
    rewrite IHents; eauto.
    cancel.
  Qed.

  Lemma tree_dir_names_pred_nodup : forall l m,
    tree_dir_names_pred' l m -> NoDup l.
  Proof.
    intros.
    eapply NoDup_map_inv.
    eapply dir_names_distinct' with (m := m).
    pred_apply; cancel.
  Qed.

  (* ugly lemmas for reordering sep_stars in the hypothesis *)
  Lemma helper_reorder_sep_star_1 : forall AT AEQ V (a b c d e : @pred AT AEQ V),
    a * b * c * d * e =p=> (b * c * d * e) * a.
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_reorder_sep_star_2 : forall AT AEQ V (a b c d : @pred AT AEQ V),
    a * b * c * d =p=> a * c * d * b.
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_reorder_sep_star_3: forall AT AEQ V (a b c d e : @pred AT AEQ V),
      (((a ✶ b) ✶ c) ✶ d) ✶ e =p=> (a * e) * b * c * d.
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_reorder_sep_star_4: forall AT AEQ V (a b c d: @pred AT AEQ V),
      ((a ✶ b) ✶ c) ✶ d  =p=> (d * a) * (b * c).
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_reorder_sep_star_5: forall AT AEQ V (a b c d : @pred AT AEQ V),
      ((a * b) * c) * d =p=> ((a * d) * c) * b.
  Proof.
    intros; cancel.
  Qed.

  Lemma notindomain_not_in_dirents : forall ents name dsmap,
    tree_dir_names_pred' ents dsmap
    -> notindomain name dsmap
    -> ~ In name (map fst ents).
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; simpl in *; intuition.
    apply ptsto_valid in H; congruence.
    apply ptsto_mem_except in H.
    eapply IHents; eauto.
    apply notindomain_mem_except'; auto.
  Qed.

  Lemma dirlist_pred_absorb_notin' : forall xp ents name subtree,
    ~ In name (map fst ents)
    -> NoDup ents
    -> tree_pred xp subtree * dirlist_pred (tree_pred xp) ents =p=>
       dirlist_pred (tree_pred xp) (add_to_list name subtree ents).
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; intuition.
    destruct (string_dec s name); subst; simpl in *.
    inversion H0; subst; cancel.
    inversion H0; subst.
    rewrite <- IHents; eauto.
    cancel.
  Qed.

  Lemma dirlist_pred_absorb_notin : forall xp ents name dsmap subtree,
    tree_dir_names_pred' ents dsmap
    -> notindomain name dsmap
    -> tree_pred xp subtree * dirlist_pred (tree_pred xp) ents =p=>
       dirlist_pred (tree_pred xp) (add_to_list name subtree ents).
  Proof.
    intros.
    apply dirlist_pred_absorb_notin'; auto.
    eapply notindomain_not_in_dirents; eauto.
    eapply tree_dir_names_pred_nodup; eauto.
  Qed.


  Lemma dir_names_pred_add : forall l m name subtree,
    tree_dir_names_pred' l m
    -> tree_dir_names_pred' (add_to_list name subtree l)
          (Mem.upd m name (dirtree_inum subtree, dirtree_isdir subtree)).
  Proof.
    induction l; simpl; intros; auto.
    apply sep_star_comm.
    apply ptsto_upd_disjoint; auto.

    destruct a.
    destruct (string_dec s name); subst; simpl.
    eapply ptsto_upd; eauto.

    generalize H.
    unfold_sep_star; intuition.
    repeat deex. exists m1. eexists.
    intuition.
    3: eapply IHl; eauto.

    apply functional_extensionality; intro.
    unfold Mem.upd, mem_union.
    destruct (string_dec x name); subst; auto.
    destruct (m1 name) eqn: Hx; auto.
    unfold ptsto in H2; intuition.
    pose proof (H3 _ n); congruence.

    unfold mem_disjoint, Mem.upd.
    intuition; repeat deex.
    destruct (string_dec a name); subst; auto.
    unfold ptsto in H2; intuition.
    pose proof (H6 _ n); congruence.
    unfold mem_disjoint in H0; repeat deex.
    firstorder.
  Qed.




  Lemma dir_names_pred_add_delete : forall l m name subtree,
    tree_dir_names_pred' (delete_from_list name l) m
    -> notindomain name m
    -> tree_dir_names_pred' (add_to_list name subtree l)
          (Mem.upd m name (dirtree_inum subtree, dirtree_isdir subtree)).
  Proof.
    induction l; simpl; intros; auto.
    apply sep_star_comm.
    apply ptsto_upd_disjoint; auto.

    destruct a. destruct (string_dec s name); subst; simpl in *.
    apply sep_star_comm.
    apply ptsto_upd_disjoint; auto.

    generalize H.
    unfold_sep_star; intros; repeat deex.
    exists m1; eexists; intuition.
    3: eapply IHl; eauto.

    apply functional_extensionality; intro.
    unfold Mem.upd, mem_union.
    destruct (string_dec x name); subst; auto.
    destruct (m1 name) eqn: Hx; auto.
    unfold ptsto in H3; intuition.
    pose proof (H4 _ n); congruence.

    unfold mem_disjoint, Mem.upd.
    intuition; repeat deex.
    destruct (string_dec a name); subst; auto.
    unfold ptsto in H3; intuition.
    pose proof (H7 _ n); congruence.
    unfold mem_disjoint in H1; repeat deex.
    firstorder.
    eapply notindomain_mem_union; eauto.
  Qed.

  Lemma dirlist_pred_add_notin: forall xp ents name subtree,
    ~ In name (map fst ents)
    -> NoDup (map fst ents)
    -> dirlist_pred (tree_pred xp) (add_to_list name subtree ents)
       =p=> tree_pred xp subtree * dirlist_pred (tree_pred xp) ents.
  Proof.
    induction ents; intros; simpl; auto.
    destruct a. destruct (string_dec s name); subst; simpl.
    cancel.
    cancel.
    inversion H0.
    apply IHents; auto.
  Qed.

  Lemma dirlist_pred_add_delete : forall xp ents name subtree,
    NoDup (map fst ents)
    -> dirlist_pred (tree_pred xp) (add_to_list name subtree (delete_from_list name ents))
       =p=> dirlist_pred (tree_pred xp) (add_to_list name subtree ents).
  Proof.
    induction ents; simpl; intros; auto.
    destruct a.
    destruct (string_dec s name); subst; simpl.
    inversion H; subst.
    apply dirlist_pred_add_notin; auto.
    destruct (string_dec s name); subst; simpl.
    congruence.
    cancel; apply IHents.
    inversion H; auto.
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
    tree_dir_names_pred' l <=p=>
    tree_dir_names_pred' (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    induction l; simpl; intros.
    auto.
    destruct a; simpl.
    destruct (string_dec s name); subst; try intuition.
    split; cancel; apply IHl; eauto.
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


  Theorem tree_dir_names_pred'_update_inv : forall l fnlist subtree subtree' name,
    fold_right (find_subtree_helper (find_subtree fnlist) name) None l = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    tree_dir_names_pred' (map (update_subtree_helper (update_subtree fnlist subtree') name) l)
    =p=> tree_dir_names_pred' l.
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
      erewrite <- update_subtree_preserve_name; eauto.
    - inversion H2; clear H2; subst; simpl in *.
      cancel. apply H2. inversion H4; eauto.
  Qed.

  Theorem tree_dir_names_pred_update : forall xp w l fnlist subtree subtree' name,
    fold_right (find_subtree_helper (find_subtree fnlist) name) None l = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    tree_dir_names_pred xp w l <=p=>
    tree_dir_names_pred xp w (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    unfold tree_dir_names_pred; intros; split; cancel; eauto.
    match goal with | [ H: SDIR.rep _ _ |- _ ] => clear H end.
    pred_apply.
    eapply tree_dir_names_pred'_update; eauto.
    match goal with | [ H: SDIR.rep _ _ |- _ ] => clear H end.
    pred_apply.
    eapply tree_dir_names_pred'_update_inv; eauto.
  Qed.

  Lemma dirlist_pred_except_notfound' : forall xp l fnlist name subtree',
    ~ In name (map fst l) ->
    dirlist_pred_except (tree_pred xp) (tree_pred_except xp fnlist) name l <=p=>
    dirlist_pred (tree_pred xp) (map (update_subtree_helper (update_subtree fnlist subtree') name) l).
  Proof.
    induction l; simpl; intros.
    auto.
    destruct a; simpl. destruct (string_dec s name); subst.
    - edestruct H. eauto.
    - split; cancel; apply IHl; eauto.
  Qed.

  Lemma tree_pred_except_update : forall xp path inum ents l tree,
    find_subtree path tree = Some (TreeDir inum ents)
    -> tree_pred_except xp path (update_subtree path (TreeDir inum l) tree)
    =p=> tree_pred_except xp path tree.
  Proof.
    induction path; intros; eauto.
    destruct tree; simpl in *.
    cancel.
    rewrite <- tree_dir_names_pred_update; eauto.
    rewrite dir_names_distinct at 1; cancel.

    induction l0; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst.
    destruct (string_dec a a); try congruence.

    inversion H3; subst.
    rewrite <- dirlist_pred_except_notfound; auto.
    rewrite <- dirlist_pred_except_notfound'; auto.
    cancel.
    eapply IHpath; eauto.
    contradict H2.
    erewrite <- update_subtree_preserve_name; eauto.

    destruct (string_dec s a); subst; try congruence.
    cancel.
    inversion H3; eauto.
  Qed.

  Theorem subtree_absorb : forall xp fnlist tree subtree subtree',
    find_subtree fnlist tree = Some subtree ->
    dirtree_inum subtree = dirtree_inum subtree' ->
    dirtree_isdir subtree = dirtree_isdir subtree' ->
    tree_pred_except xp fnlist tree * tree_pred xp subtree' =p=>
    tree_pred xp (update_subtree fnlist subtree' tree).
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

  Lemma subtree_prune_absorb : forall F xp inum ents ri re f path name dsmap subtree,
    find_subtree path (TreeDir ri re) = Some (TreeDir inum ents)
    -> find_dirlist name ents = Some subtree
    -> tree_dir_names_pred' (delete_from_list name ents) dsmap
    -> SDIR.rep f dsmap
    -> IAlloc.ino_valid xp inum
    -> dirlist_pred (tree_pred xp) ents *
       tree_pred_except xp path (TreeDir ri re) * F * inum |-> f
    =p=> (tree_pred xp subtree * F) *
          tree_pred xp (tree_prune inum ents path name (TreeDir ri re)).
  Proof.
    intros; unfold tree_prune.
    erewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    eapply dirlist_pred_extract; eauto.
    eapply tree_dir_names_pred_nodup; eauto.
  Qed.


  Lemma subtree_graft_absorb : forall xp inum ents root f path name dsmap subtree,
    SDIR.rep f (Mem.upd dsmap name (dirtree_inum subtree, dirtree_isdir subtree))
    -> find_subtree path root = Some (TreeDir inum ents)
    -> tree_dir_names_pred' ents dsmap
    -> notindomain name dsmap
    -> IAlloc.ino_valid xp inum
    -> inum |-> f * tree_pred xp subtree *
       tree_pred_except xp path root * dirlist_pred (tree_pred xp) ents
    =p=> tree_pred xp (tree_graft inum ents path name subtree root).
  Proof.
    intros; unfold tree_graft.
    erewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    eapply dirlist_pred_absorb_notin; eauto.
    apply dir_names_pred_add; auto.
  Qed.


  Lemma subtree_graft_absorb_delete : forall xp inum ents root f path name dsmap dsmap' subtree x,
    SDIR.rep f (Mem.upd dsmap name (dirtree_inum subtree, dirtree_isdir subtree))
    -> find_subtree path root = Some (TreeDir inum ents)
    -> tree_dir_names_pred' (delete_from_list name ents) dsmap
    -> tree_dir_names_pred' ents dsmap'
    -> notindomain name dsmap
    -> find_dirlist name ents = Some x
    -> IAlloc.ino_valid xp inum
    -> inum |-> f * tree_pred xp subtree *
       tree_pred_except xp path (update_subtree path (TreeDir inum (delete_from_list name ents)) root) *
       dirlist_pred (tree_pred xp) (delete_from_list name ents)
    =p=> tree_pred xp (tree_graft inum ents path name subtree root).
  Proof.
    intros; unfold tree_graft.
    erewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    rewrite tree_pred_except_update; eauto; cancel.
    rewrite sep_star_comm.
    rewrite dirlist_pred_absorb_notin; eauto.
    apply dirlist_pred_add_delete.
    eapply dir_names_distinct' with (m := dsmap').
    pred_apply; cancel.
    apply dir_names_pred_add_delete; auto.
  Qed.

  Lemma flist_crash_synced_file: forall F fsxp inum dirfile path tree flist flist',
    (F * tree_pred fsxp (update_subtree path (TreeFile inum (synced_dirfile dirfile)) tree))%pred (list2nmem flist) ->
    BFILE.flist_crash flist flist' ->
    find_subtree path tree = Some (TreeFile inum dirfile) ->
    (arrayN_ex (@ptsto _ _ _) flist' inum * inum |-> BFILE.synced_file (dirfile_to_bfile dirfile None))%pred (list2nmem flist').
  Proof.
    intros.
    rewrite subtree_extract in H by (eauto using find_update_subtree).
    cbn in *.
    destruct_lifts.
    unfold dirfile_to_bfile.
    eapply pimpl_apply in H; [ eapply list2nmem_sel with (i := inum) in H as Hs | cancel].
    eapply forall2_selN in H0 as Hf; eauto using list2nmem_inbound.
    unfold BFILE.file_crash in Hf.
    rewrite <- Hs in Hf. cbn in Hf.
    deex.
    denote Array.possible_crash_list as Hp.
    apply Array.possible_crash_list_synced_list_eq in Hp. subst.
    unfold BFILE.synced_file. cbn -[Array.synced_list].
    denote (selN _ _ _ = _) as Hx.
    rewrite <- Hx.
    apply list2nmem_array_pick.
    erewrite <- forall2_length by eauto.
    eauto using list2nmem_inbound.
  Unshelve.
    all: try exact BFILE.bfile0.
    all: eauto.
  Qed.