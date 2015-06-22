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
Require Import Log.
Require Import GenSep.
Require Import SepAuto.
Require Import Array.
Require Import FunctionalExtensionality.
Import ListNotations.

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

  Definition tree_dir_names_pred ibxp (dir_inum : addr) (dirents : list (string * dirtree)) : @pred _ eq_nat_dec _ := (
    exists f dsmap,
    #dir_inum |-> f *
    [[ BALLOC.valid_block ibxp dir_inum ]] *
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

  Fixpoint tree_pred ibxp e := (
    match e with
    | TreeFile inum f => #inum |-> f * [[ BALLOC.valid_block ibxp inum ]]
    | TreeDir inum s => tree_dir_names_pred ibxp inum s * dirlist_pred (tree_pred ibxp) s
    end)%pred.

  Fixpoint tree_pred_except ibxp (fnlist : list string) e {struct fnlist} :=  (
    match fnlist with
    | nil => emp
    | fn :: suffix =>
      match e with
      | TreeFile inum f => #inum |-> f * [[ BALLOC.valid_block ibxp inum ]]
      | TreeDir inum s => tree_dir_names_pred ibxp inum s *
                          dirlist_pred_except (tree_pred ibxp) (tree_pred_except ibxp suffix) fn s
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
     [[ (F * tree_pred fsxp.(FSXPInodeAlloc) tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

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
      cancel.
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

  Inductive tree_names_distinct : dirtree -> Prop :=
  | TND_file : forall inum f, tree_names_distinct (TreeFile inum f)
  | TND_dir : forall inum tree_ents,
    Forall tree_names_distinct (map snd tree_ents) ->
    NoDup (map fst tree_ents) ->
    tree_names_distinct (TreeDir inum tree_ents).

  Lemma rep_tree_names_distinct' : forall tree F xp m,
    (F * tree_pred xp tree)%pred m ->
    tree_names_distinct tree.
  Proof.
    induction tree using dirtree_ind2; simpl; intros.
    - constructor.
    - constructor.
      2: rewrite dir_names_distinct in H0; destruct_lift H0; eauto.

      apply Forall_forall. intros.
      rewrite Forall_forall in H.
      specialize (H x H1).

      apply in_map_iff in H1; repeat deex.
      destruct x0; simpl in *.
      apply in_split in H3; repeat deex.

      rewrite dirlist_pred_split in H0. simpl in H0.
      eapply H with (xp := xp).
      pred_apply' H0.
      cancel.
  Qed.

  Lemma rep_tree_names_distinct : forall tree F fsxp Ftop m,
    (F * rep fsxp Ftop tree)%pred m ->
    tree_names_distinct tree.
  Proof.
    unfold rep; intros.
    destruct_lift H.
    eapply rep_tree_names_distinct' with (xp := FSXPInodeAlloc fsxp).
    pred_apply' H1.
    cancel.
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

  Lemma update_subtree_preserve_name : forall l fnlist s subtree,
    map fst (map (update_subtree_helper (update_subtree fnlist subtree) s) l) = map fst l.
  Proof.
    induction l; simpl; intros; auto.
    unfold update_subtree_helper at 1.
    destruct a. destruct (string_dec s0 s); subst; auto.
    rewrite IHl. f_equal.
    rewrite IHl; auto.
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
    pred_apply.
    eapply tree_dir_names_pred'_update; eauto.
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

  (**
   * Helpers for higher levels that need to reason about updated trees.
   *)

  (* XXX second premise is unnecessary *)
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

  Theorem find_update_subtree' : forall prefix fn tree subtree dnum tree_elem,
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    find_subtree (prefix++[fn]) (update_subtree (prefix++[fn]) subtree tree) = Some subtree.
  Proof.
    induction prefix; simpl; try congruence; intros.
  
  Admitted.

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
       exists F s, F * tree_pred xp (TreeDir inum s).
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d. simpl in *.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl. cancel.
        instantiate (s1 := s0); instantiate (w := inum); cancel.
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
        * apply ptsto_mem_except in H0. simpl.
          rewrite IHl. cancel.
          instantiate (s1 := s0); instantiate (w := inum); cancel.
          2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
          pred_apply; cancel.
  Qed.

  Lemma tree_dir_extract_file : forall xp l F dmap name inum,
    (F * name |-> (inum, false))%pred dmap
    -> tree_dir_names_pred' l dmap
    -> dirlist_pred (tree_pred xp) l =p=>
       exists F bfile, F * tree_pred xp (TreeFile inum bfile).
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d; simpl in *.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0; inversion H0. subst. cancel.
        * apply ptsto_mem_except in H0.
          rewrite IHl with (inum:=inum). cancel. 2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF.
          pred_apply; cancel. apply pimpl_refl. auto.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl with (inum:=inum). cancel. 2: eauto.
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
        pred_apply. cancel. instantiate (F := F'). cancel.
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


  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, inum, isdir) <- ForEach fn fnrest fnlist
      Ghost [ mbase m F Fm Ftop treetop bflist freeinodes unused freeinode_pred ]
      Loopvar [ mscs inum isdir ]
      Continuation lrx
      Invariant
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
        exists tree,
        [[ (Fm * BFILE.rep bxp ixp bflist *
            BALLOC.rep_gen ibxp freeinodes unused freeinode_pred)%pred
           (list2mem m) ]] *
        [[ (Ftop * tree_pred ibxp treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ inum = dirtree_inum tree ]] *
        [[ isdir = dirtree_isdir tree ]] *
        [[ find_name fnlist treetop = find_name fnrest tree ]] *
        [[ isdir = true -> (exists Fsub, 
                   Fsub * tree_pred ibxp tree * freeinode_pred)%pred (list2nmem bflist) ]]
      OnCrash
        LOG.would_recover_old fsxp.(FSXPLog) F mbase
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
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = dirtree_inum tree ]] *
           [[ dirtree_isdir tree = true ]]
    POST RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ r = find_name fnlist tree ]]
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei.
    step.
    step.

    (* isdir = true *)
    destruct tree0; simpl in *; subst; intuition.
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
    cancel; try instantiate (1 := (TreeDir a0 s)); eauto; try cancel.
    erewrite <- find_name_subdir with (xp := (FSXPInodeAlloc fsxp)); eauto.
    pred_apply' Horig; cancel.
    hypmatch s as Hx; pred_apply' Hx; cancel.

    (* subtree is a file *)
    rewrite tree_dir_extract_file in Hx by eauto. destruct_lift Hx.
    cancel; try instantiate (1 := (TreeFile a0 bfile)); eauto; try cancel.
    erewrite <- find_name_file with (xp := (FSXPInodeAlloc fsxp)); eauto.
    pred_apply' Horig; cancel.
    hypmatch bfile as Hx; pred_apply' Hx; cancel.

    (* dslookup = None *)
    step.
    erewrite <- find_name_none; eauto.

    (* rx : isdir = false *)
    step.
    hypmatch (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct tree0; simpl in *; auto; congruence.

    (* rx : isdir = true *)
    step.
    hypmatch (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct tree0; simpl in *; subst; auto.

    Grab Existential Variables.
    all: try exact emp; try exact empty_mem; try exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (namei _ _ _ _) _) => apply namei_ok : prog.

  Definition mkfile T fsxp dnum name mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
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

 
  Definition mkdir T fsxp dnum name mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
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
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (TreeDir dnum 
                     ((name, TreeDir inum nil) :: tree_elem)))%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
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
    hypmatch dirlist_pred as Hx; hypmatch (pimpl freeinode_pred) as Hy;
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
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                      ((name, TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} mkdir fsxp dnum name mscs.
  Proof.
    intros; eapply pimpl_ok2. apply mkdir_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0 := tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (mkdir _ _ _ _) _) => apply mkdir_ok : prog.

  Lemma false_False_true : forall x,
    (x = false -> False) -> x = true.
  Proof.
    destruct x; tauto.
  Qed.

  Lemma true_False_false : forall x,
    (x = true -> False) -> x = false.
  Proof.
    destruct x; tauto.
  Qed.

  Ltac subst_bool :=
    repeat match goal with
    | [ H : ?x = true |- _ ] => is_var x; subst x
    | [ H : ?x = false |- _ ] => is_var x; subst x
    | [ H : ?x = false -> False  |- _ ] => is_var x; apply false_False_true in H; subst x
    | [ H : ?x = true -> False   |- _ ] => is_var x; apply true_False_false in H; subst x
    end.


  Fixpoint delete_from_list (name : string) (ents : list (string * dirtree)) :=
    match ents with
    | nil => nil
    | hd :: rest =>
      let (ent_name, ent_item) := hd in
      if string_dec ent_name name then
        rest
      else
        hd :: delete_from_list name rest
    end.

  Definition delete_from_dir (name : string) tree :=
    match tree with
    | TreeFile _ _ => tree
    | TreeDir inum ents => TreeDir inum (delete_from_list name ents)
    end.

  Definition delete T fsxp dnum name mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
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
        | _ => rx ^(mscs, false)
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
    -> BALLOC.valid_block xp dnum
    -> (# dnum |-> dfile) =p=> tree_dir_names_pred xp dnum (delete_from_list name dlist).
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
        (# inum |->?) * dirlist_pred (tree_pred xp) (delete_from_list name dlist).
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


  Fixpoint find_dirlist name (l : list (string * dirtree)) :=
    match l with
    | nil => None
    | (n, sub) :: rest =>
        if string_dec n name then Some sub else find_dirlist name rest
    end.

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
    instantiate (l0 := nil); cancel.

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
    destruct sub; simpl in *; subst; try congruence.
    pred_apply; cancel.
    instantiate (s := l0); cancel.
  Qed.


  Theorem delete_ok' : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = false ]] \/
            [[ r = true  ]] *
            [[ (Fm * rep fsxp Ftop (delete_from_dir name tree))%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} delete fsxp dnum name mscs.
  Proof.
    unfold delete, rep.
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.
    subst; simpl in *.
    hypmatch tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.
    unfold SDIR.rep_macro.
    do 2 eexists. intuition.
    pred_apply. cancel.
    pred_apply. cancel.
    eauto.

    step.
    step.
    do 2 eexists. intuition.
    pred_apply. cancel.
    pred_apply. cancel.
    eauto.

    step.
    step.

    hypmatch freeinode_pred as Hx.
    erewrite dirlist_extract with (inum := a) in Hx; eauto.
    destruct_lift Hx.
    destruct sub; simpl in *; try congruence; subst.
    hypmatch dirlist_pred_except as Hx; destruct_lift Hx; auto.

    step.
    apply pimpl_or_r; right; cancel.
    hypmatch freeinode_pred as Hx; rewrite <- Hx.

    rewrite dir_names_delete; eauto.
    rewrite dirlist_delete_file; eauto.
    instantiate (w := a); cancel.
    hypmatch (a, false) as Hc.
    pred_apply' Hc; cancel.
    step.

    eapply pimpl_ok2.
    (* XXX: [eauto], or even [apply SDIR.dslist_ok] without explicitly
       specifying at least one of [lxp], [bxp] and [ixp]. *)
    apply SDIR.dslist_ok with
      (lxp:=FSXPLog fsxp) (bxp:=FSXPBlockAlloc fsxp) (ixp:=FSXPInode fsxp).
    intros; norm'l.
    hypmatch dirlist_pred as Hx; subst_bool.
    rewrite dirlist_extract_subdir in Hx; eauto; simpl in Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.
    do 2 eexists. intuition.
    pred_apply; cancel.
    pred_apply; cancel.
    eauto.

    step.
    do 2 eexists. intuition.
    pred_apply; cancel.
    pred_apply; cancel.
    eauto.

    step.
    step.
    step.

    apply pimpl_or_r; right; cancel.
    hypmatch freeinode_pred as Hx; rewrite <- Hx.
    erewrite dlist_is_nil with (l := s) (m := dsmap0); eauto.
    rewrite dir_names_delete with (dmap := dsmap); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    cancel.
    step.
  Qed.

  Theorem delete_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = false ]] \/
            [[ r = true ]] * exists tree',
            [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} delete fsxp dnum name mscs.
  Proof.
    intros; eapply pimpl_ok2. apply delete_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0:=tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (delete _ _ _ _) _) => apply delete_ok : prog.

  Definition rename T fsxp dnum srcpath srcname dstpath dstname mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   (FSXPInodeAlloc fsxp), (FSXPInode fsxp)) in
    let^ (mscs, osrcdir) <- namei fsxp dnum srcpath mscs;
    match osrcdir with
    | None => rx ^(mscs, false)
    | Some (_, false) => rx ^(mscs, false)
    | Some (dsrc, true) =>
      let^ (mscs, osrc) <- SDIR.dslookup lxp bxp ixp dsrc srcname mscs;
      match osrc with
      | None => rx ^(mscs, false)
      | Some (inum, inum_isdir) =>
        let^ (mscs, _) <- SDIR.dsunlink lxp bxp ixp dsrc srcname mscs;
        let^ (mscs, odstdir) <- namei fsxp dnum dstpath mscs;
        match odstdir with
        | None => rx ^(mscs, false)
        | Some (_, false) => rx ^(mscs, false)
        | Some (ddst, true) =>
          let^ (mscs, odst) <- SDIR.dslookup lxp bxp ixp ddst dstname mscs;
          match odst with
          | None =>
            let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp ddst dstname inum inum_isdir mscs;
            rx ^(mscs, ok)
          | Some _ =>
            let^ (mscs, ok) <- delete fsxp ddst dstname mscs;
            If (bool_dec ok true) {
              let^ (mscs, ok) <- SDIR.dslink lxp bxp ixp ddst dstname inum inum_isdir mscs;
              rx ^(mscs, ok)
            } else {
              rx ^(mscs, false)
            }
          end
        end
      end
    end.

  (** add or update ([name], [item]) in directory entry list [ents]
   *)
  Fixpoint add_to_list (name : string) (item : dirtree) (ents : list (string * dirtree)) :=
    match ents with
    | nil => (name, item) :: nil
    | (ent_name, ent_item) :: rest =>
      if string_dec ent_name name then
        (name, item) :: rest
      else
        (ent_name, ent_item) :: add_to_list name item rest
    end.


  (** add or update ([name], [item]) in directory node [tree]
   *)
  Definition add_to_dir (name : string) (item : dirtree) tree :=
    match tree with
    | TreeFile _ _ => tree
    | TreeDir inum ents => TreeDir inum (add_to_list name item ents)
    end.

  (** remove [srcpath]/[srcname] from [tree], 
      where [snum] and [sents] are inum and dirents for [srcpath]
   *)
  Definition tree_prune snum sents srcpath srcname tree :=
    let new := delete_from_dir srcname (TreeDir snum sents) in
    update_subtree srcpath new tree.

  (** graft [subtree] onto [dstpath]/[dstname] in [tree],
      where [dnum] and [dents] are inum and dirents for [dstpath]
   *)
  Definition tree_graft dnum dents dstpath dstname subtree tree :=
    let new := add_to_dir dstname subtree (TreeDir dnum dents) in
    update_subtree dstpath new tree.

  Lemma find_name_exists : forall path tree inum isdir,
    find_name path tree = Some (inum, isdir)
    -> exists subtree, find_subtree path tree = Some subtree
        /\ dirtree_inum subtree = inum /\ dirtree_isdir subtree = isdir.
  Proof.
    unfold find_name; intros.
    destruct (find_subtree path tree); try destruct d;
      inversion H; subst; eauto.
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
    -> BALLOC.valid_block xp dnum
    -> # dnum |-> dirfile * dirlist_pred (tree_pred xp) ents =p=> tree_pred xp (TreeDir dnum ents).
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

  Lemma subtree_prune_absorb : forall F xp inum ents ri re f path name dsmap subtree,
    find_subtree path (TreeDir ri re) = Some (TreeDir inum ents)
    -> find_dirlist name ents = Some subtree
    -> tree_dir_names_pred' (delete_from_list name ents) dsmap
    -> SDIR.rep f dsmap
    -> BALLOC.valid_block xp inum
    -> dirlist_pred (tree_pred xp) ents *
       tree_pred_except xp path (TreeDir ri re) * F * # inum |-> f
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

  Lemma tree_prune_preserve_inum : forall path name tree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_inum (tree_prune inum ents path name tree) = dirtree_inum tree.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.

  Lemma tree_prune_preserve_isdir : forall path name tree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_isdir (tree_prune inum ents path name tree) = dirtree_isdir tree.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.

  Lemma tree_graft_preserve_inum : forall path name tree subtree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_inum (tree_graft inum ents path name subtree tree) = dirtree_inum tree.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.

  Lemma tree_graft_preserve_isdir : forall path name tree subtree inum ents,
    find_subtree path tree = Some (TreeDir inum ents)
    -> dirtree_isdir (tree_graft inum ents path name subtree tree) = dirtree_isdir tree.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.

  Lemma find_subtree_dirlist : forall name inum ents,
    find_subtree (name :: nil) (TreeDir inum ents) = find_dirlist name ents.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; simpl.
    destruct (string_dec s name); subst; auto.
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
          (Prog.upd m name (dirtree_inum subtree, dirtree_isdir subtree)).
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
    unfold Prog.upd, mem_union.
    destruct (string_dec x name); subst; auto.
    destruct (m1 name) eqn: Hx; auto.
    unfold ptsto in H2; intuition.
    pose proof (H3 _ n); congruence.

    unfold mem_disjoint, Prog.upd.
    intuition; repeat deex.
    destruct (string_dec a name); subst; auto.
    unfold ptsto in H2; intuition.
    pose proof (H6 _ n); congruence.
    unfold mem_disjoint in H0; repeat deex.
    firstorder.
  Qed.

  Lemma subtree_graft_absorb : forall xp inum ents root f path name dsmap subtree,
    SDIR.rep f (Prog.upd dsmap name (dirtree_inum subtree, dirtree_isdir subtree))
    -> find_subtree path root = Some (TreeDir inum ents)
    -> tree_dir_names_pred' ents dsmap
    -> notindomain name dsmap
    -> BALLOC.valid_block xp inum
    -> # inum |-> f * tree_pred xp subtree *
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


  Lemma dir_names_pred_add_delete : forall l m name subtree,
    tree_dir_names_pred' (delete_from_list name l) m
    -> notindomain name m
    -> tree_dir_names_pred' (add_to_list name subtree l)
          (Prog.upd m name (dirtree_inum subtree, dirtree_isdir subtree)).
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
    unfold Prog.upd, mem_union.
    destruct (string_dec x name); subst; auto.
    destruct (m1 name) eqn: Hx; auto.
    unfold ptsto in H3; intuition.
    pose proof (H4 _ n); congruence.

    unfold mem_disjoint, Prog.upd.
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

  Lemma subtree_graft_absorb_delete : forall xp inum ents root f path name dsmap dsmap' subtree x,
    SDIR.rep f (Prog.upd dsmap name (dirtree_inum subtree, dirtree_isdir subtree))
    -> find_subtree path root = Some (TreeDir inum ents)
    -> tree_dir_names_pred' (delete_from_list name ents) dsmap
    -> tree_dir_names_pred' ents dsmap'
    -> notindomain name dsmap
    -> find_dirlist name ents = Some x
    -> BALLOC.valid_block xp inum
    -> # inum |-> f * tree_pred xp subtree *
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


  Theorem rename_ok' : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = false ]] \/
            [[ r = true  ]] * exists snum sents dnum dents subtree pruned tree',
            [[ find_subtree srcpath tree = Some (TreeDir snum sents) ]] *
            [[ find_dirlist srcname sents = Some subtree ]] *
            [[ pruned = tree_prune snum sents srcpath srcname tree ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dnum dents) ]] *
            [[ tree' = tree_graft dnum dents dstpath dstname subtree pruned ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rep.

    (* namei srcpath, isolate root tree file before cancel *)
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.
    subst; simpl in *.
    hypmatch tree_dir_names_pred as Hx; assert (Horig := Hx).
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.  instantiate (tree := TreeDir dnum tree_elem).
    unfold rep; simpl.
    unfold tree_dir_names_pred; cancel.
    all: eauto.

    (* lookup srcname, isolate src directory before cancel *)
    destruct_branch; [ | step ].
    destruct_branch; destruct_branch; [ | step ].
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.

    hypmatch find_name as Htree.
    apply eq_sym in Htree.
    apply find_name_exists in Htree.
    destruct Htree. intuition.

    hypmatch find_subtree as Htree; assert (Hx := Htree).
    apply subtree_extract with (xp := (FSXPInodeAlloc fsxp)) in Hx.
    assert (Hsub := Horig); rewrite Hx in Hsub; clear Hx.
    destruct x; simpl in *; subst; try congruence.
    unfold tree_dir_names_pred in Hsub.
    destruct_lift Hsub.
    hypmatch (# w)%pred as Hsub.

    cancel.
    do 2 eexists; intuition.
    pred_apply; cancel.
    pred_apply' Hsub; cancel.
    eauto.

    (* unlink src *)
    step.
    do 2 eexists; intuition.
    pred_apply; cancel.
    pred_apply' Hsub; cancel.
    eauto.

    (* namei for dstpath, find out pruning subtree before step *)
    hypmatch (tree_dir_names_pred' l dsmap0) as Hx1.
    hypmatch ((a, a4)) as Hx2.
    pose proof (ptsto_subtree_exists _ Hx1 Hx2) as Hx.
    destruct Hx; intuition.

    step.
    eapply subtree_prune_absorb; eauto.
    apply dir_names_pred_delete'; auto.
    rewrite tree_prune_preserve_inum; auto.
    rewrite tree_prune_preserve_isdir; auto.

    (* fold back predicate for the pruned tree in hypothesis as well  *)
    hypmatch (list2nmem flist) as Hinterm.
    apply helper_reorder_sep_star_1 in Hinterm.
    erewrite subtree_prune_absorb in Hinterm; eauto.
    2: apply dir_names_pred_delete'; auto.
    apply helper_reorder_sep_star_2 in Hinterm.
    rename x into mvtree.

    (* lookup dstname *)
    destruct_branch; [ | step ].
    destruct_branch; destruct_branch; [ | step ].
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.

    hypmatch find_name as Hpruned.
    apply eq_sym in Hpruned.
    apply find_name_exists in Hpruned.
    destruct Hpruned. intuition.

    hypmatch find_subtree as Hpruned; assert (Hx := Hpruned).
    apply subtree_extract with (xp := (FSXPInodeAlloc fsxp)) in Hx.
    assert (Hdst := Hinterm); rewrite Hx in Hdst; clear Hx.
    destruct x; simpl in *; subst; try congruence; inv_option_eq.
    unfold tree_dir_names_pred in Hdst.
    destruct_lift Hdst.
    hypmatch (# w0)%pred as Hdst.

    cancel.
    do 2 eexists; intuition.
    pred_apply; cancel.
    pred_apply' Hdst; cancel.
    eauto.

    (* grafting back *)
    destruct_branch.

    (* case 1: dst exists, try delete *)
    eapply pimpl_ok2. apply delete_ok. intros; norm'l.
    split_or_l; [ unfold stars; simpl; norm'l; inv_option_eq | step ].
    hypmatch (tree_dir_names_pred' l0 dsmap1) as Hx3.
    hypmatch ((a12, a13)) as Hx4.
    pose proof (ptsto_subtree_exists _ Hx3 Hx4) as Hx.
    destruct Hx; intuition.

    (* must unify [find_subtree] in [delete]'s precondition with
       the root tree node.  have to do this manually *)
    unfold rep; norm. cancel. intuition.
    pred_apply; norm. cancel. intuition.
    instantiate (tree0 := (tree_prune w l srcpath srcname (TreeDir dnum tree_elem))).
    pred_apply' Hinterm; cancel. eauto.

    (* now, get ready for link *)
    step; try solve [ step ].
    hypmatch tree' as Hx. assert (Hdel := Hx).
    erewrite subtree_extract with (tree := tree') in Hx; eauto.
    2: subst; eapply find_update_subtree; eauto.
    simpl in Hx; unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    hypmatch (# w0) as Hx.

    step.
    do 2 eexists; intuition.
    pred_apply; cancel.
    pred_apply' Hx; cancel.
    eauto.

    step.
    apply pimpl_or_r; right; cancel; eauto.
    eapply subtree_graft_absorb_delete; eauto.

    (* dst is None *)
    step.
    do 2 eexists; intuition.
    pred_apply; cancel.
    pred_apply' Hdst; cancel.
    eauto.

    step.
    apply pimpl_or_r; right; cancel; eauto.
    eapply subtree_graft_absorb; eauto.

    Grab Existential Variables.
    all: try exact emp; try exact empty_mem; try exact nil; try exact mvtree.
  Qed.


  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = false ]] \/
            [[ r = true  ]] * exists srcnum srcents dstnum dstents subtree pruned renamed tree',
            [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
            [[ find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
            [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = update_subtree pathname renamed tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    intros; eapply pimpl_ok2. apply rename_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0:=tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel; eauto.
    rewrite <- subtree_absorb; eauto.
    cancel.
    rewrite tree_graft_preserve_inum; auto.
    rewrite tree_prune_preserve_inum; auto.
    rewrite tree_graft_preserve_isdir; auto.
    rewrite tree_prune_preserve_isdir; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.


  Definition read T fsxp inum off mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread (FSXPLog fsxp) (FSXPInode fsxp) inum off mscs;
    rx ^(mscs, v).

  Definition write T fsxp inum off v mscs rx : prog T :=
    mscs <- BFILE.bfwrite (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    rx mscs.

  Definition truncate T fsxp inum nblocks mscs rx : prog T :=
    let^ (mscs, ok) <- BFILE.bftrunc (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                     inum nblocks mscs;
    rx ^(mscs, ok).

  Definition getlen T fsxp inum mscs rx : prog T :=
    let^ (mscs, len) <- BFILE.bflen (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, len).

  Definition getattr T fsxp inum mscs rx : prog T :=
    let^ (mscs, attr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, attr).

  Definition setattr T fsxp inum attr mscs rx : prog T :=
    mscs <- BFILE.bfsetattr (FSXPLog fsxp) (FSXPInode fsxp) inum attr mscs;
    rx mscs.

  Lemma find_subtree_inum_valid : forall F F' xp m s tree inum f,
    find_subtree s tree = Some (TreeFile inum f)
    -> (F * tree_pred (FSXPInodeAlloc xp) tree * F')%pred m
    -> BALLOC.valid_block (FSXPInodeAlloc xp) inum.
  Proof.
    unfold rep; intros.
    destruct_lift H0.
    rewrite subtree_extract in H0 by eauto.
    simpl in H0; destruct_lift H0; auto.
  Qed.

  Theorem read_ok : forall fsxp inum off mscs,
    {< F mbase m pathname Fm Ftop tree f B v,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ r = v ]]
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} read fsxp inum off mscs.
  Proof.
    unfold read, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem write_ok : forall fsxp inum off v mscs,
    {< F mbase m pathname Fm Ftop tree f B v0,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET:mscs
           exists m' tree' f',
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]] *
           [[ f' = BFILE.Build_bfile (Array.upd (BFILE.BFData f) off v) (BFILE.BFAttr f) ]]
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} write fsxp inum off v mscs.
  Proof.
    unfold write, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.
  Qed.

  Theorem truncate_ok : forall fsxp inum nblocks mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:^(mscs, ok)
           exists m',
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
          ([[ ok = false ]] \/
           [[ ok = true ]] *
           exists tree' f',
           [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.Build_bfile (setlen (BFILE.BFData f) #nblocks $0) (BFILE.BFAttr f) ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} truncate fsxp inum nblocks mscs.
  Proof.
    unfold truncate, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.
  Qed.

  Theorem getlen_ok : forall fsxp inum mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ r = $ (length (BFILE.BFData f)) ]]
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} getlen fsxp inum mscs.
  Proof.
    unfold getlen, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem getattr_ok : forall fsxp inum mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ r = BFILE.BFAttr f ]]
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} getattr fsxp inum mscs.
  Proof.
    unfold getattr, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem setattr_ok : forall fsxp inum attr mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST RET:mscs
           exists m' tree' f',
           LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           [[ (Fm * rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.Build_bfile (BFILE.BFData f) attr ]]
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} setattr fsxp inum attr mscs.
  Proof.
    unfold setattr, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (truncate _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} progseq (getlen _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} progseq (getattr _ _ _) _) => apply getattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (setattr _ _ _ _) _) => apply setattr_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


  Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE    LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
           (* We always modify the memory, because we might allocate the file,
            * but then fail to link it into the directory..  When we return
            * None, the overall transaction should be aborted.
            *)
           exists m', LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (tree_graft dnum tree_elem pathname name 
                         (TreeFile inum BFILE.bfile0) tree))%pred (list2mem m') ]])
    CRASH  LOG.would_recover_old fsxp.(FSXPLog) F mbase
    >} mkfile fsxp dnum name mscs.
  Proof.
    unfold mkfile, rep.
    step. 
    subst; simpl in *.

    rewrite subtree_extract in H6; eauto.
    simpl in *.

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
    hypmatch dirlist_pred as Hx; hypmatch (pimpl freeinode_pred) as Hy;
    rewrite Hy in Hx; destruct_lift Hx.
    step.
    step.

    apply pimpl_or_r; right. cancel.

    rewrite <- subtree_graft_absorb; eauto. cancel.
   
    step.
    Grab Existential Variables.
    all: try exact emp.
    all: try exact BFILE.bfile0.
    all: try exact nil.
    all: try exact empty_mem.
  Qed.

  Hint Extern 1 ({{_}} progseq (mkfile _ _ _ _) _) => apply mkfile_ok : prog.

  Lemma lookup_name: forall tree_elem name subtree dnum tree,
    find_subtree [name] (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem)) tree) = Some subtree.
  Proof.
    unfold find_subtree, update_subtree, add_to_dir.
    induction tree_elem; intros; subst; simpl.
    - destruct (string_dec name name). reflexivity. exfalso. eauto.
    - destruct a.
      destruct (string_dec s name); subst; simpl.
      destruct (string_dec name name). reflexivity. exfalso. eauto.
      destruct (string_dec s name); subst; simpl.
      congruence.
      eauto.
  Qed.

  Lemma lookup_firstelem_path: forall  suffix tree a f,
    find_subtree (a::suffix) tree = Some f ->
    exists d, find_subtree [a] tree = Some d /\ find_subtree suffix d = Some f.
  Proof.
    intros; subst; simpl.
    destruct tree.
    simpl in *.
    congruence. 
    induction l.
    - simpl in *. congruence.
    - destruct a0. simpl in *.
      destruct (string_dec s a).
      eexists. intuition; eauto.
      eauto.
  Qed.


 Lemma lookup_firstelem_path_r: forall a dir name suffix subtree tree childdir,
    find_subtree [a] tree = Some childdir /\ 
        find_subtree (suffix ++ [name]) (update_subtree suffix (add_to_dir name subtree dir) childdir) = Some subtree ->
    find_subtree ((a::suffix) ++ [name]) (update_subtree (a::suffix) (add_to_dir name subtree dir) tree) = Some subtree.
  Proof.
    intros.
    subst; simpl.
    destruct tree.
    simpl in *.
    intuition.
    congruence.
    simpl in *.
    unfold fold_right in H.
    induction l.
    - simpl in *. intuition. congruence.
    - destruct a0. simpl in *.
      destruct (string_dec s a).
      simpl in *.
      destruct (string_dec s a).
      intuition.
      inversion H0.
      assumption.
      rewrite IHl.
      reflexivity.
      intuition.
      simpl in *.
      destruct (string_dec s a).
      congruence.
      eauto.
  Qed.

  Lemma lookup_path: forall prefix name subtree dir tree dnum tree_elem,
    dir = (TreeDir dnum tree_elem) ->
    find_subtree prefix tree = Some dir ->
    find_subtree (prefix ++ [name]) (update_subtree prefix (add_to_dir name subtree dir) tree)
        = Some subtree.
  Proof.
    induction prefix; intros.
    - rewrite app_nil_l.
      inversion H. 
      erewrite lookup_name by eauto.
      reflexivity.
    - edestruct lookup_firstelem_path; eauto.
      intuition.
      erewrite lookup_firstelem_path_r.
      eauto.
      intuition.
      instantiate (childdir :=x). 
      assumption.
      erewrite IHprefix by eauto.
      reflexivity.
  Qed.

  Theorem find_subtree_tree_graft: forall prefix name tree dnum tree_elem subtree,
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    find_subtree (prefix++[name]) (tree_graft dnum tree_elem prefix name subtree tree) = Some subtree.
  Proof.
    intros.
    unfold tree_graft.
    erewrite lookup_path with (dnum := dnum) (tree_elem := tree_elem) by eauto.
    reflexivity.
  Qed.

  Lemma update_name: forall name tree subtree subtree' dir,
    update_subtree [name] subtree' (update_subtree [] (add_to_dir name subtree dir) tree) =
    update_subtree [] (add_to_dir name subtree' dir) tree.
  Proof.
  Admitted.


  Lemma update_addelem_path: forall a prefix name tree subtree subtree' dir,
    update_subtree (prefix ++ [name]) subtree' (update_subtree prefix (add_to_dir name subtree dir) tree) =
    update_subtree prefix (add_to_dir name subtree' dir) tree ->
    update_subtree ((a :: prefix) ++ [name]) subtree' (update_subtree (a :: prefix) (add_to_dir name subtree dir) tree) =
    update_subtree (a :: prefix) (add_to_dir name subtree' dir) tree.
  Proof.
    intros.
    subst; simpl.
    destruct tree.
    reflexivity.
    induction l.
    - simpl in *. reflexivity.
    - destruct a0. simpl in *.
      destruct (string_dec s a).
      simpl in *.
      destruct (string_dec s a).
      admit.
  Admitted.

  Lemma update_path: forall prefix name subtree subtree' dir tree dnum tree_elem,
    dir = (TreeDir dnum tree_elem) ->
    update_subtree (prefix ++ [name]) subtree' (update_subtree prefix (add_to_dir name subtree dir) tree)
        = update_subtree prefix (add_to_dir name subtree' dir) tree.
  Proof.
    induction prefix; intros.
    - rewrite app_nil_l.
      erewrite update_name.
      rewrite H.
      reflexivity.
    - eapply update_addelem_path.
      eapply IHprefix with (dnum := dnum) (tree_elem := tree_elem).
      eauto.
  Admitted.


  Theorem update_subtree_tree_graft: forall prefix name tree dnum tree_elem subtree subtree',
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    update_subtree (prefix++[name]) subtree' (tree_graft dnum tree_elem prefix name subtree tree) = 
          (tree_graft dnum tree_elem prefix name subtree' tree).
  Proof.
    intros.
    unfold tree_graft.
    erewrite update_path with (dnum := dnum) (tree_elem := tree_elem) by eauto.
    reflexivity.
  Qed.


End DIRTREE.
