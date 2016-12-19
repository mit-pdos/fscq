Require Import DirName.
Require Import Balloc.
Require Import Prog ProgMonad.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import FSLayout.
Require Import Pred.
Require Import Arith.
Require Import GenSepN.
Require Import List ListUtils.
Require Import Hoare.
Require Import Log.
Require Import SepAuto.
Require Import Array.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import GenSepAuto.
Require Import Lock.
Require Import Errno.
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

  Definition dirtree_dirents (dt : dirtree) :=
    match dt with
    | TreeFile _ _ => nil
    | TreeDir  _ ents => ents
    end.

  Definition dirtree_file (dt : dirtree) :=
    match dt with
    | TreeFile _ f => f
    | TreeDir  _ _ => BFILE.bfile0
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

  Fixpoint tree_pred ibxp e := (
    match e with
    | TreeFile inum f => inum |-> f * [[ IAlloc.ino_valid ibxp inum ]]
    | TreeDir inum s => tree_dir_names_pred ibxp inum s * dirlist_pred (tree_pred ibxp) s
    end)%pred.

  Fixpoint tree_pred_except ibxp (fnlist : list string) e {struct fnlist} :=  (
    match fnlist with
    | nil => emp
    | fn :: suffix =>
      match e with
      | TreeFile inum f => inum |-> f * [[ IAlloc.ino_valid ibxp inum ]]
      | TreeDir inum s => tree_dir_names_pred ibxp inum s *
                          dirlist_pred_except (tree_pred ibxp) (tree_pred_except ibxp suffix) fn s
      end
    end)%pred.


  Fixpoint dirtree_update_inode t inum off v :=
    match t with
    | TreeFile inum' f => if (addr_eq_dec inum inum') then
          let f' := BFILE.mk_bfile (updN (BFILE.BFData f) off v) (BFILE.BFAttr f) in (TreeFile inum f')
          else (TreeFile inum' f)
    | TreeDir inum' ents =>
      TreeDir inum' (dirlist_update (fun t' => dirtree_update_inode t' inum off v) ents)
    end.

  (**
   * [F] represents the other parts of the file system above [tree],
   * in cases where [tree] is a subdirectory somewhere in the tree.
   *)

  Definition rep fsxp F tree ilist frees :=
    (exists bflist freeinodes freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) bflist ilist frees *
     IAlloc.rep fsxp freeinodes freeinode_pred *
     [[ (F * tree_pred fsxp tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

  Theorem rep_length : forall fsxp F tree ilist frees,
    rep fsxp F tree ilist frees =p=>
    (rep fsxp F tree ilist frees *
     [[ length ilist = ((INODE.IRecSig.RALen (FSXPInode fsxp)) * INODE.IRecSig.items_per_val)%nat ]])%pred.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite BFILE.rep_length_pimpl at 1.
    cancel.
  Qed.

  Definition dirtree_safe ilist1 free1 tree1 ilist2 free2 tree2 :=
    BFILE.ilist_safe ilist1 free1 ilist2 free2 /\
    forall inum off bn pathname f,
      find_subtree pathname tree2 = Some (TreeFile inum f) ->
      BFILE.block_belong_to_file ilist2 bn inum off ->
      ((BFILE.block_belong_to_file ilist1 bn inum off /\
        exists pathname' f', find_subtree pathname' tree1 = Some (TreeFile inum f')) \/
       BFILE.block_is_unused free1 bn).

  Theorem dirtree_safe_refl : forall i f t,
    dirtree_safe i f t i f t.
  Proof.
    unfold dirtree_safe; intuition eauto.
    apply BFILE.ilist_safe_refl.
  Qed.

  Theorem dirtree_safe_trans : forall i1 f1 t1 i2 t2 f2 i3 t3 f3,
    dirtree_safe i1 f1 t1 i2 f2 t2 ->
    dirtree_safe i2 f2 t2 i3 f3 t3 ->
    dirtree_safe i1 f1 t1 i3 f3 t3.
  Proof.
    unfold dirtree_safe; intros.
    intuition.
    eapply BFILE.ilist_safe_trans; eauto.
    edestruct H3; eauto.
    - intuition; repeat deex.
      edestruct H2; eauto.
    - right.
      unfold BFILE.ilist_safe in *.
      unfold BFILE.block_is_unused in *; eauto.
      intuition.
  Qed.

  Lemma dirtree_safe_file : forall ilist frees inum f f',
    dirtree_safe ilist frees (TreeFile inum f) ilist frees (TreeFile inum f').
  Proof.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.
    exists pathname. eexists.
    destruct pathname; simpl in *; try congruence.
    inversion H.
    subst; eauto.
  Qed.

  Lemma dirtree_safe_ilist_trans : forall ilist frees ilist' frees' tree tree',
    dirtree_safe ilist frees tree ilist frees tree' ->
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees tree ilist' frees' tree'.
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    specialize (H3 _ _ _ H5); intuition.
    specialize (H4 _ _ _ H6); intuition.
    eapply H2; eauto.
  Qed.

  Lemma dirtree_safe_file_trans : forall ilist frees ilist' frees' inum f f',
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees (TreeFile inum f) ilist' frees' (TreeFile inum f').
  Proof.
    intros; apply dirtree_safe_ilist_trans; auto.
    apply dirtree_safe_file.
  Qed.

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

  Lemma rep_tree_names_distinct : forall tree F fsxp Ftop m ilist frees,
    (F * rep fsxp Ftop tree ilist frees)%pred m ->
    tree_names_distinct tree.
  Proof.
    unfold rep; intros.
    destruct_lift H.
    eapply rep_tree_names_distinct' with (xp := fsxp).
    pred_apply' H1.
    cancel.
  Qed.

  Lemma tree_names_distinct_update_subtree : forall pn t subtree,
    tree_names_distinct t ->
    tree_names_distinct subtree ->
    tree_names_distinct (update_subtree pn subtree t).
  Proof.
    induction pn; simpl; eauto; intros.
    destruct t; eauto.
    constructor.
    - induction l; simpl; constructor.
      + destruct a0; simpl.
        inversion H; simpl in *; subst.
        inversion H3; subst.
        destruct (string_dec s a); subst; simpl; eauto.
      + eapply IHl.
        inversion H; subst.
        inversion H3; subst.
        inversion H4; subst.
        constructor; eauto.
    - inversion H; subst.
      replace (map fst (map (update_subtree_helper (update_subtree pn subtree) a) l)) with (map fst l); eauto.
      clear H H3 H4.
      induction l; simpl; eauto.
      f_equal; eauto.
      destruct a0; simpl.
      destruct (string_dec s a); eauto.
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

  Lemma update_dirtree_preserve_name: forall l name newtree,
    map fst (map (update_subtree_helper (fun _: dirtree => newtree) name) l) = map fst l.
  Proof.
    intros.
    induction l.
    - simpl; auto.
    - erewrite map_cons.
      unfold update_subtree_helper at 1.
      destruct a.
      destruct (string_dec s name).
      erewrite map_cons; erewrite IHl; simpl; auto.
      erewrite map_cons; erewrite IHl; simpl; auto.
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
   * Theorems about how [dwrite]'s [updN]s affect the tree state.
   *)
  Fixpoint tree_inodes t :=
    match t with
    | TreeFile inum f => [inum]
    | TreeDir inum ents => [inum] ++ (dirlist_combine tree_inodes ents)
    end.

  Definition tree_inodes_distinct t := NoDup (tree_inodes t).

  Hint Resolve in_or_app.
  Hint Resolve in_app_or.
  Hint Resolve NoDup_app_l.
  Hint Resolve NoDup_app_r.

  Theorem tree_inodes_distinct_child : forall n a d l,
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    tree_inodes_distinct d.
  Proof.
    unfold tree_inodes_distinct; simpl; intros.
    rewrite cons_app in *.
    eauto.
  Qed.

  Theorem tree_names_distinct_child : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct d.
  Proof.
    intros.
    inversion H; simpl in *.
    inversion H2; eauto.
  Qed.

  Theorem dirtree_update_inode_absent : forall tree inum off v,
    ~ In inum (tree_inodes tree) ->
    dirtree_update_inode tree inum off v = tree.
  Proof.
    induction tree using dirtree_ind2; simpl in *; intros; intuition.
    - destruct (addr_eq_dec inum0 inum); congruence.
    - f_equal.
      induction tree_ents; simpl; auto.
      destruct a; simpl in *.
      inversion H.
      rewrite H4 by eauto.
      rewrite IHtree_ents; eauto.
  Qed.

  Theorem find_subtree_inum_present : forall pathname tree sub,
    find_subtree pathname tree = Some sub ->
    In (dirtree_inum sub) (tree_inodes tree).
  Proof.
    induction pathname; simpl; intros.
    - inversion H; subst.
      destruct sub; simpl; eauto.
    - destruct tree; try congruence.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; eauto.
      edestruct IHl; eauto.
  Qed.

  Hint Resolve tree_inodes_distinct_child.
  Hint Resolve tree_names_distinct_child.
  Hint Resolve find_subtree_inum_present.

  Lemma update_subtree_notfound : forall name l f,
    ~ In name (map fst l) ->
    map (update_subtree_helper f name) l = l.
  Proof.
    induction l; simpl; intros; eauto.
    destruct a; simpl in *.
    destruct (string_dec s name); intuition.
    rewrite IHl; eauto.
  Qed.

  Lemma dirtree_update_inode_absent' : forall l inum off v,
    ~ In inum (concat (map (fun e => tree_inodes (snd e)) l)) ->
    dirlist_update (fun t' : dirtree => dirtree_update_inode t' inum off v) l = l.
  Proof.
    induction l; simpl; intros; eauto.
    destruct a; simpl in *.
    rewrite dirtree_update_inode_absent; eauto.
    rewrite IHl; eauto.
  Qed.

  Lemma tree_inodes_distinct_not_in_tail : forall l d n inum a,
    In inum (tree_inodes d) ->
    tree_inodes_distinct (TreeDir n ((a, d) :: l)) ->
    ~ In inum (concat (map (fun e : string * dirtree => tree_inodes (snd e)) l)).
  Proof.
    induction l; simpl; eauto.
    intros. destruct a; simpl in *.
    inversion H0; subst.

    intro H'; apply in_app_or in H'; destruct H'.
    rewrite app_assoc in H4. apply NoDup_app_l in H4.
    eapply not_In_NoDup_app. 2: eauto. all: eauto.
    eapply IHl; eauto.
    unfold tree_inodes_distinct; simpl.
    constructor.
    intro; apply H3.
    apply in_app_or in H2. intuition eauto.

    apply NoDup_app_comm in H4. rewrite <- app_assoc in H4.
    apply NoDup_app_comm in H4. apply NoDup_app_l in H4.
    apply NoDup_app_comm in H4. eauto.

    Unshelve. eauto.
  Qed.

  Lemma tree_inodes_distinct_not_this_child : forall n s d l pathname inum f,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    find_subtree pathname (TreeDir n l) = Some (TreeFile inum f) ->
    ~ In inum (tree_inodes d).
  Proof.
    intros.
    apply find_subtree_inum_present in H0; simpl in *.
    inversion H; subst.
    intuition; subst; eauto.
    eapply not_In_NoDup_app. 2: eauto. all: eauto.
  Qed.

  Hint Resolve tree_inodes_distinct_not_in_tail.
  Hint Resolve tree_inodes_distinct_not_this_child.

  Lemma tree_inodes_distinct_next : forall n s d l,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    tree_inodes_distinct (TreeDir n l).
  Proof.
    unfold tree_inodes_distinct; simpl; intros.
    rewrite cons_app in *.
    apply NoDup_app_comm in H. rewrite <- app_assoc in H.
    apply NoDup_app_comm in H. apply NoDup_app_l in H.
    apply NoDup_app_comm in H; eauto.
  Qed.

  Lemma tree_names_distinct_next : forall n s d l,
    tree_names_distinct (TreeDir n ((s, d) :: l)) ->
    tree_names_distinct (TreeDir n l).
  Proof.
    intros.
    inversion H.
    constructor.
    inversion H2; eauto.
    inversion H3; eauto.
  Qed.

  Hint Resolve tree_inodes_distinct_next.
  Hint Resolve tree_names_distinct_next.

  Theorem dirtree_update_inode_update_subtree : forall pathname tree inum off f v,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    off < length (BFILE.BFData f) ->
    let f' := BFILE.mk_bfile (updN (BFILE.BFData f) off v) (BFILE.BFAttr f) in
    dirtree_update_inode tree inum off v =
    update_subtree pathname (TreeFile inum f') tree.
  Proof.
    induction pathname; simpl; intros.
    - inversion H1; subst; simpl.
      destruct (addr_eq_dec inum inum); congruence.
    - destruct tree; simpl in *; try congruence.
      f_equal.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; eauto.
      + erewrite IHpathname; eauto.
        f_equal.
        inversion H0. inversion H6.
        rewrite update_subtree_notfound by eauto.
        inversion H.
        rewrite dirtree_update_inode_absent'; eauto.
        apply find_subtree_inum_present in H1; simpl in *.
        eapply tree_inodes_distinct_not_in_tail; eauto.
      + rewrite dirtree_update_inode_absent.
        rewrite IHl; eauto.
        eapply tree_inodes_distinct_not_this_child with (pathname := a :: pathname).
        2: apply H1.
        eauto.
  Qed.

  Theorem dirtree_update_inode_oob : forall pathname tree inum off f v,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    ~ off < length (BFILE.BFData f) ->
    dirtree_update_inode tree inum off v = tree.
  Proof.
    induction pathname; simpl; intros.
    - inversion H1; subst; simpl.
      destruct (addr_eq_dec inum inum); try congruence.
      rewrite updN_oob by ( apply not_lt; auto ).
      destruct f; auto.
    - destruct tree; simpl in *; try congruence.
      f_equal.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; eauto.
      + erewrite IHpathname; eauto.
        f_equal.
        inversion H0. inversion H6.
        inversion H.
        rewrite dirtree_update_inode_absent'; eauto.
        apply find_subtree_inum_present in H1; simpl in *.
        eapply tree_inodes_distinct_not_in_tail; eauto.
      + rewrite dirtree_update_inode_absent.
        rewrite IHl; eauto.
        eapply tree_inodes_distinct_not_this_child with (pathname := a :: pathname).
        2: apply H1.
        eauto.
  Qed.

  Lemma rep_tree_inodes_distinct : forall tree F fsxp Ftop m ilist frees,
    (F * rep fsxp Ftop tree ilist frees)%pred m ->
    tree_inodes_distinct tree.
  Proof.
    unfold rep, tree_inodes_distinct; intros.
    destruct_lift H.
    eapply ListPred.listpred_nodup_F.
    apply addr_eq_dec.
    apply ptsto_conflict.
    eapply pimpl_apply. 2: apply H1.

    cancel. instantiate (F0 := (dummy1 * Ftop)%pred). cancel.
    clear H1.
    induction tree using dirtree_ind2; simpl.
    cancel.
    unfold tree_dir_names_pred. cancel. clear H4.
    induction tree_ents; simpl.
    - cancel.
    - inversion H0.
      destruct a.
      rewrite H3; simpl.
      rewrite ListPred.listpred_app.
      rewrite IHtree_ents; eauto.
  Qed.

  Theorem dirtree_rep_used_block_eq : forall pathname F0 tree fsxp F ilist freeblocks inum off bn m f,
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    selN (BFILE.BFData f) off ($0, nil) = selN m bn ($0, nil).
  Proof.
    intros.
    apply rep_tree_names_distinct in H as Hnames.
    apply rep_tree_inodes_distinct in H as Hinodes.

    unfold rep in *.
    destruct_lift H.

    erewrite <- BFILE.rep_used_block_eq with (m := m).
    2: pred_apply; cancel.
    2: eauto.
    f_equal.
    f_equal.

    rewrite subtree_extract in H3 by eassumption.
    simpl in H3.
    apply eq_sym.
    eapply BFILE.rep_used_block_eq_Some_helper.
    rewrite <- list2nmem_sel_inb.

    eapply ptsto_valid. pred_apply; cancel.
    eapply list2nmem_inbound.
    pred_apply; cancel.
  Qed.

  Theorem dirtree_update_block : forall pathname F0 tree fsxp F ilist freeblocks inum off v bn m f,
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    (F0 * rep fsxp F (dirtree_update_inode tree inum off v) ilist freeblocks)%pred (list2nmem (updN m bn v)).
  Proof.
    intros.
    apply rep_tree_names_distinct in H as Hnames.
    apply rep_tree_inodes_distinct in H as Hinodes.

    unfold rep in *.
    destruct_lift H.
    eapply pimpl_apply; [ | eapply BFILE.rep_safe_used; eauto; pred_apply; cancel ].
    cancel.

    rewrite subtree_extract in H3; eauto.
    remember H3 as H3'; clear HeqH3'.
    erewrite dirtree_update_inode_update_subtree; eauto.
    rewrite <- subtree_absorb; eauto; simpl in *.
    eapply pimpl_apply. 2: eapply list2nmem_updN; pred_apply; cancel.
    eapply pimpl_apply in H3. eapply list2nmem_sel with (i := inum) in H3. 2: cancel.
    rewrite <- H3.
    cancel.

    destruct_lift H3'; eauto.

    simpl in *.
    eapply pimpl_apply in H3'.
    eapply list2nmem_sel with (i := inum) in H3'.
    2: cancel.
    rewrite H3'.

    eapply BFILE.block_belong_to_file_bfdata_length; eauto.
    eapply pimpl_apply; [ | apply H ]. cancel.
  Qed.

  Theorem dirtree_update_free : forall tree fsxp F F0 ilist freeblocks v bn m flag,
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    BFILE.block_is_unused (BFILE.pick_balloc freeblocks flag) bn ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem (updN m bn v)).
  Proof.
    intros.
    unfold rep in *.
    destruct_lift H.
    eapply pimpl_apply; [ | eapply BFILE.rep_safe_unused; eauto; pred_apply; cancel ].
    cancel.
  Qed.

  Lemma tree_names_distinct_head_not_rest : forall inum e ents name path subtree,
    tree_names_distinct (TreeDir inum (e :: ents)) ->
    find_subtree (name::path) (TreeDir inum ents) = Some subtree ->
    find_subtree (name::path) (TreeDir inum (e :: ents)) = Some subtree.
  Proof.
    destruct e; simpl; intros.
    destruct (string_dec s name); eauto; subst.
    inversion H.
    inversion H4; subst.
    clear H H3 H4 H8.
    exfalso.
    induction ents; simpl in *; try congruence.
    destruct a; simpl in *; intuition.
    destruct (string_dec s name); simpl in *; try congruence.
    eapply IHents; eauto.
  Qed.

  Theorem tree_inodes_pathname_exists : forall tree inum,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    In inum (tree_inodes tree) ->
    exists pathname subtree,
    find_subtree pathname tree = Some subtree /\ dirtree_inum subtree = inum.
  Proof.
    induction tree using dirtree_ind2.
    - simpl; intros.
      intuition; subst.
      exists nil; eexists.
      simpl; intuition eauto.
    - simpl; intros.
      intuition; subst.

      exists nil; eexists.
      simpl; intuition eauto.

      cut (inum0 <> inum).
      induction tree_ents; simpl in *; try solve [ exfalso; eauto ].
      destruct a; simpl in *.
      apply in_app_or in H3.
      intuition.

      * inversion H; subst. edestruct H6; repeat deex; eauto.
        exists (s :: x). eexists. intuition eauto.
        simpl. destruct (string_dec s s); congruence.

      * inversion H; subst.
        edestruct IHtree_ents; eauto.
        destruct H3. destruct H3.
        exists x; eexists.
        intuition eauto.
        destruct x.

        simpl in *.
        inversion H3. rewrite <- H10 in H5. simpl in *. congruence.
        erewrite tree_names_distinct_head_not_rest; eauto.

      * inversion H1.
        intro; apply H5. subst; eauto.
  Qed.

  Theorem dirtree_update_safe_inum : forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks v bn inum off m flag,
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    exists tree',
    (F0 * rep fsxp F tree' ilist freeblocks)%pred (list2nmem (updN m bn v)) /\
    (tree' = tree \/
     exists pathname' f', find_subtree pathname' tree = Some (TreeFile inum f') /\
     tree' = dirtree_update_inode tree inum off v).
  Proof.
    intros.
    unfold dirtree_safe, BFILE.ilist_safe in H1.
    intuition.
    specialize (H4 _ _ _ _ _ H H0).
    intuition; repeat deex.
    - (**
       * The block still belongs to the same inode in this earlier disk.
       *)
      eexists; split.
      2: right; intuition.
      eapply dirtree_update_block; eauto.
      eauto.
    - (**
       * The block is now in the free list.
       *)
      eexists; split.
      2: left; reflexivity.
      eapply dirtree_update_free; eauto.
  Qed.

  (* This lemma is just for compatibility with old proofs.. *)
  Theorem dirtree_update_safe : forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks v bn inum off m flag,
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    exists tree',
    (F0 * rep fsxp F tree' ilist freeblocks)%pred (list2nmem (updN m bn v)) /\
    (tree' = tree \/ tree' = dirtree_update_inode tree inum off v).
  Proof.
    intros; destruct v.
    edestruct dirtree_update_safe_inum; intuition eauto.
    repeat deex; intuition eauto.
  Qed.

  Theorem dirtree_update_safe_pathname :
    forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks v bn inum off m flag,
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    exists tree',
    (F0 * rep fsxp F tree' ilist freeblocks)%pred (list2nmem (updN m bn v)) /\
    (tree' = tree \/
     exists pathname' f', find_subtree pathname' tree = Some (TreeFile inum f') /\
     let f'new := BFILE.mk_bfile (updN (BFILE.BFData f') off v) (BFILE.BFAttr f') in
     tree' = update_subtree pathname' (TreeFile inum f'new) tree).
  Proof.
    intros; destruct v.
    edestruct dirtree_update_safe_inum; eauto.
    intuition; subst; eauto.
    destruct (in_dec addr_eq_dec inum (tree_inodes tree)).
    - (* inum is in the tree.. *)
      edestruct tree_inodes_pathname_exists; eauto; repeat deex.
      eapply rep_tree_names_distinct; eauto.
      eapply rep_tree_inodes_distinct; eauto.
      destruct (lt_dec off (length (BFILE.BFData f'))).
      + (* in-bounds write *)
        erewrite dirtree_update_inode_update_subtree in H4; eauto.
        eexists; split.
        eauto.
        right; eauto.
        eapply rep_tree_inodes_distinct; eauto.
        eapply rep_tree_names_distinct; eauto.
      + (* out-of-bounds write *)
        erewrite dirtree_update_inode_oob in H4; eauto.
        eapply rep_tree_inodes_distinct; eauto.
        eapply rep_tree_names_distinct; eauto.
    - (* inum is not in the tree *)
      repeat deex.
      erewrite dirtree_update_inode_absent in H4 by eauto.
      eauto.
  Qed.

  Theorem dirtree_update_safe_pathname_pred :
    forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks v bn inum off m flag,
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    (F0 * rep fsxp F tree ilist freeblocks \/
     exists pathname' f',
     [[ find_subtree pathname' tree = Some (TreeFile inum f') ]] *
     let f'new := BFILE.mk_bfile (updN (BFILE.BFData f') off v) (BFILE.BFAttr f') in
     let tree' := update_subtree pathname' (TreeFile inum f'new) tree in
     F0 * rep fsxp F tree' ilist freeblocks)%pred (list2nmem (updN m bn v)).
  Proof.
    intros.
    edestruct dirtree_update_safe_pathname; eauto.
    intuition.
    eapply pimpl_apply; try eassumption. cancel.
    eapply pimpl_apply; try eassumption. cancel.
  Qed.


  Lemma find_subtree_ents_not_in : forall T ents name acc (rec : _ -> option T),
    ~ In name (map fst ents) ->
    fold_right (find_subtree_helper rec name) acc ents = acc.
  Proof.
    induction ents; intros; auto; simpl.
    destruct a; simpl in *; intuition.
    destruct (string_dec s name); subst; try congruence; auto.
  Qed.


  Lemma find_subtree_ents_rev_nodup : forall path ents dnum inum f,
    NoDup (map fst ents) ->
    find_subtree path (TreeDir dnum ents) = Some (TreeFile inum f) ->
    find_subtree path (TreeDir dnum (rev ents)) = Some (TreeFile inum f).
  Proof.
    induction path; simpl. 
    try congruence.
    intros.
    induction ents; simpl; intros; auto.
    destruct a0; inversion H; subst; simpl in *.
    rewrite fold_right_app; simpl.
    destruct (string_dec s a); subst.
    - rewrite H0.
      apply find_subtree_ents_not_in.
      rewrite map_rev.
      rewrite <- in_rev; auto.
    - apply IHents; auto.
  Qed.


  (**
   * Helpers for proving [dirlist_safe] in postconditions.
   *)
  Theorem dirlist_safe_mkdir : forall ilist freeblocks ilist' freeblocks'
                                      dnum tree_elem name inum,
    BFILE.ilist_safe ilist freeblocks ilist' freeblocks' ->
    dirtree_safe ilist freeblocks (TreeDir dnum tree_elem)
                 ilist' freeblocks' (TreeDir dnum ((name, TreeDir inum []) :: tree_elem)).
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    specialize (H1 _ _ _ H2); destruct H1.
    2: right; intuition.
    left; intuition.

    (**
     * Need to prove that the new directory's filename didn't change the existing
     * pathname for [inum0].  This should follow from the fact that the new inode
     * corresponds to a directory, not a file.
     **)
    destruct pathname; simpl in *; try congruence.
    destruct (string_dec name s); subst; eauto.
    destruct pathname; simpl in *; try congruence.
    exists (s :: pathname). eexists. eauto.
  Qed.


  Theorem dirlist_safe_mkfile : forall ilist freeblocks ilist' freeblocks' frees
                                      dnum tree_elem name inum m flist' bxp ixp F Fm,
   (Fm * BFILE.rep bxp ixp flist' ilist' frees)%pred m ->
   (F * inum |-> BFILE.bfile0 )%pred (list2nmem flist') ->
    BFILE.ilist_safe ilist  freeblocks ilist' freeblocks' ->
    tree_names_distinct (TreeDir dnum tree_elem) ->
    ~ In name (map fst tree_elem) ->
    dirtree_safe ilist  freeblocks (TreeDir dnum tree_elem)
                 ilist' freeblocks' (TreeDir dnum (tree_elem ++ [(name, TreeFile inum BFILE.bfile0)])).
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    denote (forall _, _ ) as Hx; denote (BFILE.block_belong_to_file) as Hy.
    specialize (Hx _ _ _ Hy); destruct Hx.
    2: right; intuition.  (* Unused block. *)
    destruct pathname.
    simpl in *; congruence.

    denote tree_names_distinct as Hz; inversion Hz; subst.
    apply find_subtree_ents_rev_nodup in H1.
    rewrite rev_app_distr in H1; simpl in *.
    destruct (string_dec name s); subst; eauto.

    - (* Same filename; contradiction because the file is empty *)
      exfalso.
      destruct pathname; simpl in *; try congruence.

      inversion H1; subst.
      unfold BFILE.rep in H; destruct_lift H.
      unfold BFILE.block_belong_to_file in Hy; intuition subst.
      extract.
      eapply list2nmem_sel in H0; rewrite <- H0 in *.
      setoid_rewrite ListPred.listmatch_length_pimpl in H at 2.
      destruct_lift H; rewrite map_length in *.
      denote (0 = _) as Heq; rewrite <- Heq in *.
      denote (off < _) as Hlt; inversion Hlt.
    - (* Different filename *)
      left; intuition.
      do 2 eexists.
      rewrite <- rev_involutive with (l := tree_elem).
      apply find_subtree_ents_rev_nodup.
      rewrite map_rev.
      apply NoDup_rev_1; auto.
      eassign (s :: pathname); simpl; eauto.

    - rewrite map_app; simpl.
      apply NoDup_app_comm; simpl.
      constructor; auto.

    Unshelve. all: eauto; exact unit.
  Qed.


  Theorem find_subtree_app : forall p0 p1 tree subtree,
    find_subtree p0 tree = Some subtree ->
    find_subtree (p0 ++ p1) tree = find_subtree p1 subtree.
  Proof.
    induction p0; simpl; intros.
    inversion H; eauto.
    destruct tree; try congruence.
    induction l; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); eauto.
  Qed.

  Lemma find_subtree_extend: forall p1 p2 tree subtree,
      find_subtree p1 tree = Some subtree ->
      find_subtree p2 subtree = find_subtree (p1++p2) tree.
  Proof.
    intros.
    erewrite find_subtree_app; eauto.
  Qed.

  Theorem find_subtree_app_none : forall p0 p1 tree,
    find_subtree p0 tree = None ->
    find_subtree (p0 ++ p1) tree = None.
  Proof.
    induction p0; simpl; intros.
    inversion H; eauto.
    destruct tree; try congruence.
    induction l; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); eauto.
  Qed.

  Theorem pathname_decide_prefix : forall (base pn : list string),
    (exists suffix, pn = base ++ suffix) \/
    (~ exists suffix, pn = base ++ suffix).
  Proof.
    induction base; simpl. eauto.
    destruct pn.
    right. intro H'; destruct H'. congruence.
    destruct (string_dec s a); subst.
    - destruct (IHbase pn); repeat deex.
      left; eauto.
      right. intro H'; apply H. deex. inversion H0; eauto.
    - right. intro H. deex. inversion H. eauto.
  Qed.

  Theorem find_subtree_update_subtree_oob : forall base pn tree subtree inum f,
    (~ exists suffix, pn = base ++ suffix) ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    find_subtree pn (update_subtree base subtree tree) = Some (TreeFile inum f).
  Proof.
    induction base; intros.
    simpl in *.
    contradict H. eauto.

    destruct pn.
    simpl in *. inversion H0; subst. eauto.
    destruct tree; simpl in *; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s0 s); destruct (string_dec s0 a); subst; subst; simpl in *.
    - destruct (string_dec a a); try congruence.
      eapply IHbase; eauto.
      intro H'; apply H. deex. exists suffix. eauto.
    - destruct (string_dec s s); try congruence.
    - destruct (string_dec a s); try congruence.
      eauto.
    - destruct (string_dec s0 s); try congruence.
      eauto.
  Qed.

  Theorem find_subtree_update_subtree_oob' : forall base pn tree subtree inum f,
    (~ exists suffix, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree tree) = Some (TreeFile inum f) ->
    find_subtree pn tree = Some (TreeFile inum f).
  Proof.
    induction base; intros.
    simpl in *.
    contradict H. eauto.

    destruct pn.
    simpl in *. inversion H0; subst. eauto.
    destruct tree; simpl in *; try congruence.
    destruct tree; simpl in *; try congruence.

    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s0 s); destruct (string_dec s0 a); subst; subst; simpl in *.
    - destruct (string_dec s s); try congruence.
      eapply IHbase; eauto.
      intro H'; apply H. deex. exists suffix. eauto.
    - destruct (string_dec s s); try congruence.
    - destruct (string_dec a s); try congruence; eauto.
    - destruct (string_dec s0 s); try congruence; eauto.
  Qed.

  Theorem find_subtree_helper1 : forall pathname suffix tree subtree subtree' r,
    find_subtree pathname tree = Some subtree ->
    find_subtree (pathname ++ suffix) (update_subtree pathname subtree' tree) = Some r ->
    find_subtree suffix subtree' = Some r.
  Proof.
    induction pathname; simpl in *; intros; eauto.
    destruct tree; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl in *.
    - destruct (string_dec a a); try congruence.
      eauto.
    - destruct (string_dec s a); try congruence.
      apply IHl; eauto.
  Qed.

  Theorem dirlist_safe_subtree : forall pathname tree
                                        ilist  freeblocks  subtree
                                        ilist' freeblocks' subtree',
    find_subtree pathname tree = Some subtree ->
    dirtree_safe ilist  freeblocks  subtree
                 ilist' freeblocks' subtree' ->
    dirtree_safe ilist  freeblocks  tree
                 ilist' freeblocks' (update_subtree pathname subtree' tree).
  Proof.
    unfold dirtree_safe; intuition.
    destruct (pathname_decide_prefix pathname pathname0); repeat deex.
    - edestruct H2; eauto.
      eapply find_subtree_helper1. 2: eauto. eauto.
      left; intuition. repeat deex.
      do 2 eexists.
      erewrite find_subtree_app; eauto.
    - clear H2.
      unfold BFILE.ilist_safe in H0.
      destruct H1.
      specialize (H2 _ _ _ H3).
      intuition.
      left.
      intuition.
      exists pathname0; eexists.
      erewrite <- find_subtree_update_subtree_oob'; eauto.
  Qed.

  (**
   * Helpers for higher levels that need to reason about updated trees.
   *)

 Lemma tree_names_distinct_head_name : forall inum name subtree rest,
    tree_names_distinct (TreeDir inum ((name, subtree) :: rest)) ->
    ~ In name (map fst rest).
  Proof.
    inversion 1.
    simpl in *.
    inversion H3; auto.
  Qed.

  Lemma tree_names_distinct_head_name' : forall  rest name  f,
    map fst (map (update_subtree_helper f name) rest) = map fst rest.
  Proof.
    induction rest; simpl; intros.
    auto.
    erewrite IHrest.
    unfold update_subtree_helper.
    destruct a.
    destruct (string_dec s name); eauto.
  Qed.

  Lemma tree_name_distinct_rest: forall inum x l,
        tree_names_distinct (TreeDir inum (x::l)) ->
        tree_names_distinct (TreeDir inum l).
  Proof.
    intros.
    inversion H.
    rewrite map_cons in H2.
    apply Forall_cons2 in H2.
    rewrite map_cons in H3.
    rewrite NoDup_cons_iff in H3.
    intuition.
    constructor; eauto.
  Qed.

  Lemma tree_name_distinct_head: forall inum name l t,
        tree_names_distinct (TreeDir inum ((name, t)::l)) ->
        tree_names_distinct t.
  Proof.
    intros.
    destruct t.
    constructor.
    inversion H.
    rewrite map_cons in H2.
    apply Forall_inv in H2.
    simpl in H2.
    inversion H2.
    constructor; eauto.
  Qed.

  Theorem find_update_subtree : forall fnlist tree subtree subtree0,
    find_subtree fnlist tree = Some subtree0 ->
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

  Lemma find_update_subtree_suffix: forall path suffix tree subtree d,
    find_subtree path tree = Some d ->
    find_subtree (path++suffix) (update_subtree path subtree tree) =
    find_subtree suffix subtree.
  Proof.
    induction path; simpl; try congruence; intros.
    destruct tree; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl.
    - destruct (string_dec a a); try congruence; eauto.
    - destruct (string_dec s a); try congruence; eauto.
  Qed.


  Lemma update_subtree_same: forall pn tree subtree,
    tree_names_distinct tree ->
    find_subtree pn tree = Some subtree ->
    update_subtree pn subtree tree = tree.
  Proof.
    induction pn; simpl; intros.
    - inversion H0; reflexivity.
    - destruct tree; eauto.
      f_equal.
      induction l.
      + simpl; eauto.
      + erewrite map_cons.
        unfold update_subtree_helper at 1.

        destruct a0.
        destruct (string_dec s a).
        rewrite e.
        rewrite IHpn; eauto.
        erewrite update_subtree_notfound; eauto.
        eapply tree_names_distinct_head_name with (inum := n); eauto.
        rewrite <- e; eauto.

        unfold find_subtree_helper in H0.
        simpl in H0.
        destruct (string_dec a a) in H0; eauto.
        rewrite e in H0.
        simpl in H0.
        destruct (string_dec a a) in H0; eauto.
        congruence.
        congruence.

        f_equal.
        rewrite IHl; eauto.
        unfold find_subtree_helper in H0.
        simpl in H0.
        destruct (string_dec s a) in H0; eauto.
        congruence.
  Qed.

  Lemma find_subtree_update_subtree_ne_file :
    forall p2 p1 tree inum1 inum2 f1 f1' f2,
    find_subtree p1 tree = Some (TreeFile inum1 f1) ->
    find_subtree p2 tree = Some (TreeFile inum2 f2) ->
    p1 <> p2 ->
    find_subtree p2 (update_subtree p1 (TreeFile inum1 f1') tree) =
    find_subtree p2 tree.
  Proof.
    induction p2.
    - simpl; intros. inversion H0; simpl. destruct p1; try congruence. simpl; congruence.
    - intros.
      destruct tree; try solve [ simpl in *; congruence ].
      destruct p1; try solve [ inversion H ].
      destruct (string_dec s a); subst; simpl in *.
      + induction l; try solve [ simpl in *; congruence ].
        destruct a0. simpl in *.
        destruct (string_dec s a); subst; simpl.
        * destruct (string_dec a a); try congruence.
          eapply IHp2; eauto.
          intro; apply H1; congruence.
        * destruct (string_dec s a); try congruence.
          eauto.
      + clear IHp2.
        clear H.
        induction l; try solve [ simpl in *; congruence ].
        destruct a0. simpl in *.
        destruct (string_dec s0 a); subst; simpl.
        * destruct (string_dec a s); try congruence.
          simpl. destruct (string_dec a a); try congruence.
        * destruct (string_dec s0 s); subst; simpl in *.
          destruct (string_dec s a); try congruence. eauto.
          destruct (string_dec s0 a); try congruence; eauto.
  Qed.

  Lemma dirtree_safe_update_subtree : forall ilist frees tree ilist' frees' tree' inum pathname f f',
    dirtree_safe ilist frees tree ilist' frees' tree' ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    dirtree_safe ilist frees (update_subtree pathname (TreeFile inum f') tree) ilist' frees' tree'.
  Proof.
    unfold dirtree_safe; intros.
    intuition.
    specialize (H2 _ _ _ _ _ H H3).
    intuition; repeat deex.
    left; intuition.
    destruct (list_eq_dec string_dec pathname pathname'); subst.
    - rewrite H4 in H0. inversion H0.
      repeat eexists.
      erewrite find_update_subtree; eauto.
    - repeat eexists.
      erewrite find_subtree_update_subtree_ne_file; eauto.
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
       exists F s, F * tree_pred xp (TreeDir inum s).
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d. simpl in *.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl. cancel.
        eassign s0; eassign inum; cancel.
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
          eassign s0; eassign inum; cancel.
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

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Ltac msalloc_eq :=
    repeat match goal with
    | [ H: MSAlloc _ = MSAlloc _ |- _ ] => rewrite H in *; clear H
    end.

  Definition namei fsxp dnum (fnlist : list string) mscs :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, inum, isdir, valid) <- ForEach fn fnrest fnlist
      Hashmap hm
      Ghost [ mbase m F Fm Ftop treetop bflist freeinodes freeinode_pred ilist freeblocks mscs0 ]
      Loopvar [ mscs inum isdir valid ]
      Invariant
        LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
        exists tree,
        [[ (Fm * BFILE.rep bxp ixp bflist ilist freeblocks *
            IAlloc.rep ibxp freeinodes freeinode_pred)%pred
           (list2nmem m) ]] *
        [[ (Ftop * tree_pred ibxp treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ valid = OK tt -> inum = dirtree_inum tree ]] *
        [[ valid = OK tt -> isdir = dirtree_isdir tree ]] *
        [[ valid = OK tt -> find_name fnlist treetop = find_name fnrest tree ]] *
        [[ isError valid -> find_name fnlist treetop = None ]] *
        [[ valid = OK tt -> isdir = true -> (exists Fsub,
                   Fsub * tree_pred ibxp tree * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ MSAlloc mscs = MSAlloc mscs0 ]]
      OnCrash
        LOG.intact fsxp.(FSXPLog) F mbase hm
      Begin
        match valid with
        | Err e =>
          Ret ^(mscs, inum, isdir, Err e)
        | OK _ =>
          If (bool_dec isdir true) {
            let^ (mscs, r) <- SDIR.lookup lxp ixp inum fn mscs;
            match r with
            | Some (inum, isdir) => Ret ^(mscs, inum, isdir, OK tt)
            | None => Ret ^(mscs, inum, isdir, Err ENOENT)
            end
          } else {
            Ret ^(mscs, inum, isdir, Err ENOTDIR)
          }
        end
    Rof ^(mscs, dnum, true, OK tt);
    match valid with
    | OK _ =>
      Ret ^(mscs, OK (inum, isdir))
    | Err e =>
      Ret ^(mscs, Err e)
    end.

   Local Hint Unfold SDIR.rep_macro rep : hoare_unfold.

  Theorem namei_ok : forall fsxp dnum fnlist mscs,
    {< F mbase m Fm Ftop tree ilist freeblocks,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist freeblocks)%pred (list2nmem m) ]] *
           [[ dnum = dirtree_inum tree ]] *
           [[ dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') hm' *
           [[ (isError r /\ None = find_name fnlist tree) \/
              (exists v, (r = OK v /\ Some v = find_name fnlist tree))%type ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei.
    step.

    destruct_branch.
    step.

    (* isdir = true *)
    destruct tree0; simpl in *; subst; intuition.
    step.
    denote (tree_dir_names_pred) as Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    safestep; eauto.

    denote (dirlist_pred) as Hx; assert (Horig := Hx).
    destruct_branch.

    (* dslookup = Some _: extract subtree before [cancel] *)
    prestep.
    norml; unfold stars; simpl; clear_norm_goal; inv_option_eq.
    destruct a2.

    (* subtree is a directory *)
    rewrite tree_dir_extract_subdir in Hx by eauto; destruct_lift Hx.
    norm. cancel. intuition simpl.
    eassign (TreeDir a1 dummy6). auto. auto.
    erewrite <- find_name_subdir with (xp := fsxp); eauto.
    pred_apply' Horig; cancel.
    pred_apply; cancel.
    pred_apply; cancel.
    eauto. eauto.

    (* subtree is a file *)
    rewrite tree_dir_extract_file in Hx by eauto. destruct_lift Hx.
    cancel. eassign (TreeFile a1 dummy6). auto. auto.
    erewrite <- find_name_file with (xp := fsxp); eauto.
    pred_apply' Horig; cancel.
    pred_apply; cancel.

    (* dslookup = None *)
    step.
    erewrite <- find_name_none; eauto.
    cancel.
    apply LOG.active_intact.
    step.
    denote (find_name) as Hx; rewrite Hx.
    destruct tree0; intuition.
    step.
    destruct_branch.

    (* Ret : OK *)
    step.
    right; eexists; intuition.
    denote (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct tree0; simpl in *; subst; auto.

    (* Ret : Error *)
    step.
    left; intuition.
    eapply eq_sym; eauto.

    Grab Existential Variables.
    all: eauto; try exact Mem.empty_mem; try exact tt.
  Qed.

  Hint Extern 1 ({{_}} Bind (namei _ _ _ _) _) => apply namei_ok : prog.

  Definition mkfile fsxp dnum name fms :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, oi) <- IAlloc.alloc lxp ibxp ms;
    let fms := BFILE.mk_memstate al ms in
    match oi with
    | None => Ret ^(fms, Err ENOSPCINODE)
    | Some inum =>
      let^ (fms, ok) <- SDIR.link lxp bxp ixp dnum name inum false fms;
      match ok with
      | OK _ =>
        fms <- BFILE.reset lxp bxp ixp inum fms;
        Ret ^(fms, OK (inum : addr))
      | Err e =>
        Ret ^(fms, Err e)
      end
    end.


  Definition mkdir fsxp dnum name fms :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, oi) <- IAlloc.alloc lxp ibxp ms;
    let fms := BFILE.mk_memstate al ms in
    match oi with
    | None => Ret ^(fms, Err ENOSPCINODE)
    | Some inum =>
      let^ (fms, ok) <- SDIR.link lxp bxp ixp dnum name inum true fms;
      match ok with
      | OK _ =>
        fms <- BFILE.reset lxp bxp ixp inum fms;
        Ret ^(fms, OK (inum : addr))
      | Err e =>
        Ret ^(fms, Err e)
      end
    end.


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


  Theorem mkdir_ok' : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem ilist freeblocks,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist freeblocks)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum ilist' freeblocks',
            let tree' := TreeDir dnum ((name, TreeDir inum nil) :: tree_elem) in
            [[ r = OK inum ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' freeblocks')%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc freeblocks  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc freeblocks' (MSAlloc mscs')) tree' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} mkdir fsxp dnum name mscs.
  Proof.
    unfold mkdir, rep.
    step.
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.
    eapply IAlloc.ino_valid_goodSize; eauto.

    destruct_branch; [ | step ].
    prestep; norml; inv_option_eq.

    denote dirlist_pred as Hx; denote (pimpl dummy1) as Hy.
    rewrite Hy in Hx; destruct_lift Hx.
    cancel.
    step.
    or_r; cancel.

    unfold tree_dir_names_pred at 1. cancel; eauto.
    unfold tree_dir_names_pred; cancel.
    apply SDIR.bfile0_empty.
    apply emp_empty_mem.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    msalloc_eq.
    eapply dirlist_safe_mkdir; auto.
    eapply BFILE.ilist_safe_trans; eauto.

    step.
    Unshelve.
    all: try eauto; exact emp; try exact nil; try exact empty_mem; try exact BFILE.bfile0.
  Qed.


  Theorem mkdir_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum tree' ilist' frees', [[ r = OK inum ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                      ((name, TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees')%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} mkdir fsxp dnum name mscs.
  Proof.
    intros; eapply pimpl_ok2. apply mkdir_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0 := tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
    eapply dirlist_safe_subtree; eauto.
  Qed.


  Theorem mkfile_ok' : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r) exists m',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum ilist' tree' frees',
            [[ r = OK inum ]] * [[ ~ In name (map fst tree_elem) ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                        (tree_elem ++ [(name, (TreeFile inum BFILE.bfile0))] )) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' )%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} mkfile fsxp dnum name mscs.
  Proof.
    unfold mkfile, rep.
    step. 
    subst; simpl in *.

    denote tree_pred as Ht;
    rewrite subtree_extract in Ht; eauto.
    assert (tree_names_distinct (TreeDir dnum tree_elem)).
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep, IAlloc.rep; cancel.

    simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.
    unfold SDIR.rep_macro.
    eapply IAlloc.ino_valid_goodSize; eauto.

    destruct_branch; [ | step ].
    prestep; norml; inv_option_eq.

    denote dirlist_pred as Hx; denote (pimpl dummy1) as Hy.
    rewrite Hy in Hx; destruct_lift Hx.
    cancel.
    step.

    or_r; cancel.
    eapply dirname_not_in; eauto.

    rewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    rewrite dirlist_pred_split; simpl; cancel.
    apply tree_dir_names_pred'_app; simpl.
    apply sep_star_assoc; apply emp_star_r.
    apply ptsto_upd_disjoint; auto.

    eapply dirlist_safe_subtree; eauto.
    msalloc_eq.
    eapply dirlist_safe_mkfile; eauto.
    eapply BFILE.ilist_safe_trans; eauto.
    eapply dirname_not_in; eauto.

    step.
    Unshelve.
    all: eauto.
  Qed.

  Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.


  Lemma tree_graft_not_in_dirents : forall path ents name tree subtree dnum,
    ~ In name (map fst ents) ->
    update_subtree path (TreeDir dnum (ents ++ [(name, subtree)])) tree =
    tree_graft dnum ents path name subtree tree.
  Proof.
    unfold tree_graft, add_to_dir.
    induction path; intros.
    induction ents; intros; simpl; auto.
    destruct a; destruct (string_dec s name); simpl in *; subst; intuition.
    inversion H; rewrite H3; auto.
    destruct tree; simpl; auto.
    f_equal. f_equal. f_equal.
    apply functional_extensionality; intros.
    apply IHpath; auto.
  Qed.


  (* same as previous one, but use tree_graft *)
  Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r) exists m',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum ilist' tree' frees',
            [[ r = OK inum ]] *
            [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum BFILE.bfile0) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' )%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} mkfile fsxp dnum name mscs.
  Proof.
    unfold mkfile; intros.
    eapply pimpl_ok2. apply mkfile_ok'.
    cancel.
    eauto.
    step.

    or_r; cancel.
    rewrite tree_graft_not_in_dirents; auto.
    rewrite <- tree_graft_not_in_dirents; auto.
  Qed.


  Hint Extern 1 ({{_}} Bind (mkdir _ _ _ _) _) => apply mkdir_ok : prog.
  Hint Extern 1 ({{_}} Bind (mkfile _ _ _ _) _) => apply mkfile_ok : prog.

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


  Definition delete fsxp dnum name mscs :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, oi) <- SDIR.lookup lxp ixp dnum name mscs;
    match oi with
    | None => Ret ^(mscs, Err ENOENT)
    | Some (inum, isdir) =>
      let^ (mscs, ok) <- If (bool_dec isdir false) {
        Ret ^(mscs, true)
      } else {
        let^ (mscs, l) <- SDIR.readdir lxp ixp inum mscs;
        match l with
        | nil => Ret ^(mscs, true)
        | _ => Ret ^(mscs, false)
        end
      };
      If (bool_dec ok false) {
        Ret ^(mscs, Err ENOTEMPTY)
      } else {
        let^ (mscs, ok) <- SDIR.unlink lxp ixp dnum name mscs;
        match ok with
        | OK _ =>
          mscs' <- IAlloc.free lxp ibxp inum (MSLL mscs);
          mscs <- BFILE.reset lxp bxp ixp inum (MSAlloc mscs, mscs');
          Ret ^(mscs, OK tt)
        | Err e =>
          Ret ^(mscs, Err e)
        end
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

  Lemma find_dirlist_same: forall ents name b subtree,
    NoDup (name :: (map fst ents)) ->
    find_dirlist name ((name, b) :: ents) = Some subtree ->
    b = subtree.
  Proof.
    intros; cbn.
    unfold find_dirlist in H0. 
    destruct (string_dec name name); try congruence.
  Qed.

  Lemma find_dirlist_ne: forall name1 name2 b ents,
    NoDup (name2 :: (map fst ents)) ->
    name1 <> name2 ->
    find_dirlist name1 ((name2, b) :: ents) = find_dirlist name1 ents .
  Proof.
    intros; cbn.
    unfold find_dirlist in H0. 
    destruct (string_dec name2 name1); try congruence.
  Qed.

  Lemma find_dirlist_in : forall name ents tree,
     find_dirlist name ents = Some tree ->
     In name (map fst ents).
  Proof.
    induction ents; simpl; intros; try congruence.
    destruct a.
    destruct (string_dec s name); subst.
    left; auto.
    right; simpl in *.
    eapply IHents.
    destruct (string_dec s name); try congruence; eauto.
  Qed.

  Lemma find_dirlist_find_subtree_helper : forall ents tree name,
    find_dirlist name ents = Some tree ->
    NoDup (map fst ents) ->
    fold_right (find_subtree_helper (fun x => Some x) name) None ents = Some tree.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; destruct (string_dec s name); subst.
    - inversion H; inversion H0; subst; simpl in *.
      destruct (string_dec name name); congruence.
    - inversion H0; subst; simpl in *.
      destruct (string_dec s name); subst.
      contradict H3; eapply find_dirlist_in; eauto.
      apply IHents; eauto.
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

  Lemma find_subtree_helper_in : forall T (rec : _ -> option T) ents name node,
    fold_right (find_subtree_helper rec name) None ents = Some node ->
    In name (map fst ents).
  Proof.
    induction ents; simpl; intros; try congruence.
    destruct a.
    destruct (string_dec s name); subst.
    left; auto.
    right; simpl in *.
    eapply IHents.
    destruct (string_dec s name); try congruence; eauto.
  Qed.

  Lemma find_subtree_delete' : forall pathname name ents inum dnum f,
    NoDup (map fst ents) ->
    find_subtree pathname (TreeDir dnum (delete_from_list name ents)) = Some (TreeFile inum f) ->
    find_subtree pathname (TreeDir dnum ents) = Some (TreeFile inum f).
  Proof.
    induction pathname; simpl in *; intuition.
    inversion H0.
    induction ents; simpl in *; try congruence.
    destruct a0 as [ename subtree]; simpl in *.
    destruct (string_dec ename name); subst.
    - inversion H; subst; destruct (string_dec name a); subst; auto.
      contradict H3.
      eapply find_subtree_helper_in; eauto.
    - inversion H; subst; simpl in *.
      destruct (string_dec ename a); destruct (string_dec a a); subst; try congruence.
      apply IHents; auto.
  Qed.

  Lemma dirlist_safe_delete : forall ilist frees ilist' frees' dnum name ents,
    tree_names_distinct (TreeDir dnum ents) ->
    BFILE.ilist_safe ilist frees ilist' frees' ->
    dirtree_safe ilist frees (TreeDir dnum ents)
                 ilist' frees' (TreeDir dnum (delete_from_list name ents)).
  Proof.
    unfold dirtree_safe; intuition.
    unfold BFILE.ilist_safe in *; intuition.
    specialize (H4 _ _ _ H2); intuition.
    left; split; auto.
    repeat eexists.
    eapply find_subtree_delete'; eauto.
    inversion H; auto.
  Qed.

  Lemma dirlist_combine_app: forall l (f : dirtree -> list addr) a,
    dirlist_combine f (a::l) = dirlist_combine f [a] ++ (dirlist_combine f l).
  Proof.
    intros. 
    rewrite cons_app.
    unfold dirlist_combine; subst; simpl.
    destruct a.
    rewrite app_nil_r; eauto.
  Qed.

  Lemma find_dirlist_tree_inodes: forall elem name d dnum,
    tree_names_distinct (TreeDir dnum elem) ->
    find_dirlist name elem = Some d ->
    In (dirtree_inum d) (dirlist_combine tree_inodes elem).
  Proof.
    induction elem; intros.
    - simpl in *. inversion H0.
    - rewrite dirlist_combine_app.
      destruct a.
      destruct (string_dec s name); subst.
      + rewrite in_app_iff.
        left.
        simpl in H0.
        destruct (string_dec name name); try congruence; subst.
        inversion H0; subst.
        simpl.
        rewrite app_nil_r; simpl.
        unfold tree_inodes; simpl.
        destruct d; subst; simpl.
        left; eauto.
        left; eauto.
      + rewrite in_app_iff.
        right.
        eapply IHelem; eauto.
        rewrite find_dirlist_ne in H0; eauto.
        inversion H. simpl in H4. eauto.
  Qed.

  Lemma tree_inodes_distinct_delete: forall elem name dnum d n inum, 
    tree_names_distinct (TreeDir dnum elem) ->
    tree_inodes_distinct (TreeDir dnum elem) ->
    find_dirlist name elem = Some d ->
    dirtree_inum d = n ->
    In inum (dirlist_combine tree_inodes (delete_from_list name elem)) ->
    inum <> n.
  Proof.
    induction elem; intros.
    - unfold find_dirlist in H1. inversion H1.
    - destruct a.
      destruct (string_dec name s); subst.
      + 
        unfold delete_from_list in H3.
        unfold find_dirlist in H1.
        destruct (string_dec s s); subst.
        ++
          inversion H1; subst. clear H1.
          inversion H0.
          eapply not_In_NoDup_app with (l2 := tree_inodes d) in H3.
          intro; subst.
          eapply H3.
          destruct d; simpl.
          left; eauto.
          right; eauto.
          simpl in H3.
          destruct H3.
          left; auto.
          eapply NoDup_app_comm; eauto.
        ++
          rewrite dirlist_combine_app in H3.
          eapply in_app_or in H3.
          intuition.
      + unfold delete_from_list in H3.
        destruct (string_dec s name); try congruence.
        rewrite dirlist_combine_app in H3.
        eapply in_app_or in H3.
        intuition.
        ++  
          eapply IHelem with (name := name); eauto.
          rewrite find_dirlist_ne in H1; eauto.
          inversion H1.
          inversion H. simpl in H8; eauto.
          simpl in H4.
          rewrite app_nil_r in H4.
          rewrite H2 in H4.
          inversion  H0.
          eapply not_In_NoDup_app with (l1 := tree_inodes d0) in H7; eauto.
          rewrite find_dirlist_ne in H1; eauto.
          eapply find_dirlist_tree_inodes in H1.
          exfalso.
          eapply H7; eauto.
          inversion H. simpl in H11; eauto.
          inversion H. simpl in H11; eauto.
        ++  
          eapply IHelem with (name := name); eauto.
          rewrite find_dirlist_ne in H1; eauto.
          inversion H. simpl in H7; eauto.
          rewrite <- H2; eauto.
  Qed.

  Hint Extern 0 (okToUnify (tree_dir_names_pred _ _ _) (tree_dir_names_pred _ _ _)) => constructor : okToUnify.

  Theorem delete_ok' : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem frees ilist,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] * exists frees' ilist',
            let tree' := delete_from_dir name tree in
            [[ (Fm * rep fsxp Ftop tree' ilist' frees')%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum def', inum <> dnum ->
                 (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
                 selN ilist inum def' = selN ilist' inum def' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} delete fsxp dnum name mscs.
  Proof.
    unfold delete, rep.

    (* extract some basic facts from rep *)
    intros; eapply pimpl_ok2; monad_simpl; eauto with prog; intros; norm'l.
    assert (tree_inodes_distinct (TreeDir dnum tree_elem)) as HiID.
    eapply rep_tree_inodes_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.
    assert (tree_names_distinct (TreeDir dnum tree_elem)) as HdID.
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.

    (* lookup *)
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    safecancel. 2: eauto.
    unfold SDIR.rep_macro.
    cancel; eauto.
    step.
    step.
    step.

    (* unlink *)
    step.

    (* is_file: prepare for free *)
    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := a0) in Hx; eauto.
    destruct_lift Hx.
    destruct dummy4; simpl in *; try congruence; subst.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.
    step.

    (* prepare for reset *)
    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := n) in Hx; eauto.
    destruct_lift Hx.
    destruct dummy4; simpl in *; try congruence; subst.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.
    step.

    (* post conditions *)
    step.
    or_r; safecancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    rewrite dir_names_delete with (dnum := dnum); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    cancel.
    apply dirlist_safe_delete; auto.

    (* inum inside the new modified tree *)
    eapply find_dirlist_exists in H8 as H8'.
    deex.
    denote dirlist_combine as Hx.
    eapply tree_inodes_distinct_delete in Hx as Hx'; eauto.
    eassumption.

    (* inum outside the original tree *)
    eapply H31.
    intro; subst.
    eapply H36.
    eapply find_dirlist_exists in H8 as H8'.
    deex.
    eapply find_dirlist_tree_inodes; eauto.
    eassumption.

    (* case 2: is_dir: check empty *)
    prestep.
    intros; norm'l.
    denote dirlist_pred as Hx; subst_bool.
    rewrite dirlist_extract_subdir in Hx; eauto; simpl in Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel. eauto.

    step.
    step.
    step.
    step.
    step.
    step.

    (* post conditions *)
    or_r; cancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    denote (tree_dir_names_pred' _ _) as Hz.
    erewrite (@dlist_is_nil _ _ _ _ _ Hz); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    rewrite dir_names_delete with (dnum := dnum).
    cancel. eauto. eauto. eauto.
    apply dirlist_safe_delete; auto.

    (* inum inside the new modified tree *)
    eapply find_dirlist_exists in H8 as H8'.
    deex.
    denote dirlist_combine as Hx.
    eapply tree_inodes_distinct_delete in Hx as Hx'; eauto.
    eassumption.

    (* inum outside the original tree *)
    eapply H33.
    intro; subst.
    eapply H32.
    eapply find_dirlist_exists in H8 as H8'.
    deex.
    eapply find_dirlist_tree_inodes; eauto.
    eassumption.

    step.
    step.
    cancel; auto.
    cancel; auto.

    Unshelve.
    all: try exact addr_eq_dec.  6: eauto. all: eauto.
    auto using Build_balloc_xparams.
  Qed.

  Lemma tree_names_distinct_subtree : forall path tree subtree,
    tree_names_distinct tree ->
    find_subtree path tree = Some subtree ->
    tree_names_distinct subtree.
  Proof.
    induction path.
    intros; inversion H0; subst; auto.
    induction tree; simpl; try congruence; intros.
    inversion H0; subst.

    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl in *.
    - inversion H; inversion H4; subst; simpl in *.
      eapply IHpath; eauto.
    - inversion H; inversion H4; subst; simpl in *.
      apply IHl; eauto.
  Qed.

  Definition rename fsxp dnum srcpath srcname dstpath dstname mscs :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, osrcdir) <- namei fsxp dnum srcpath mscs;
    match osrcdir with
    | Err _ => Ret ^(mscs, Err ENOENT)
    | OK (_, false) => Ret ^(mscs, Err ENOTDIR)
    | OK (dsrc, true) =>
      let^ (mscs, osrc) <- SDIR.lookup lxp ixp dsrc srcname mscs;
      match osrc with
      | None => Ret ^(mscs, Err ENOENT)
      | Some (inum, inum_isdir) =>
        let^ (mscs, _) <- SDIR.unlink lxp ixp dsrc srcname mscs;
        let^ (mscs, odstdir) <- namei fsxp dnum dstpath mscs;
        match odstdir with
        | Err _ => Ret ^(mscs, Err ENOENT)
        | OK (_, false) => Ret ^(mscs, Err ENOTDIR)
        | OK (ddst, true) =>
          let^ (mscs, odst) <- SDIR.lookup lxp ixp ddst dstname mscs;
          match odst with
          | None =>
            let^ (mscs, ok) <- SDIR.link lxp bxp ixp ddst dstname inum inum_isdir mscs;
            Ret ^(mscs, ok)
          | Some _ =>
            let^ (mscs, ok) <- delete fsxp ddst dstname mscs;
            match ok with
            | OK _ =>
              let^ (mscs, ok) <- SDIR.link lxp bxp ixp ddst dstname inum inum_isdir mscs;
              Ret ^(mscs, ok)
            | Err e =>
              Ret ^(mscs, Err e)
            end
          end
        end
      end
    end.

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


  Lemma tree_pred_ino_goodSize : forall V F Fm xp tree m d frees prd,
    (Fm * (@IAlloc.rep V xp frees prd))%pred m ->
    (F * tree_pred xp tree)%pred d ->
    goodSize addrlen (dirtree_inum tree).
  Proof.
    induction tree using dirtree_ind2; simpl; intros.
    destruct_lift H0.
    eapply IAlloc.ino_valid_goodSize; eauto.
    unfold tree_dir_names_pred in H1; destruct_lift H1.
    eapply IAlloc.ino_valid_goodSize; eauto.
  Qed.


  Lemma find_subtree_leaf_in : forall ents name tree dnum,
    In (name, tree) ents ->
    NoDup (map fst ents) ->
    find_subtree [ name ] (TreeDir dnum ents) = Some tree.
  Proof.
    induction ents; simpl; intuition.
    - inversion H0; inversion H1; subst; simpl in *.
      destruct (string_dec name name); congruence.
    - inversion H0; subst; simpl in *.
      destruct (string_dec a0 name); subst.
      contradict H3.
      apply in_map_iff; eexists; split; eauto; simpl; auto.
      apply IHents; auto.
  Qed.


  Definition pathname_prefix p1 p2 :=
    (exists suffix : list string, p1 ++ suffix = p2).

  Lemma pathname_prefix_neq: forall path path',
    ~ (exists suffix : list string, path = path' ++ suffix) ->
    ~ pathname_prefix path' path.
  Proof.
    unfold pathname_prefix; eauto.
    intros. 
    intro.
    eapply H.
    destruct H0.
    eexists x; eauto.
  Qed.

  Lemma pathname_prefix_head_neq': forall path name name',
    ~ pathname_prefix [name] (name' :: path) ->
    name <> name'.
  Proof.
    intros.
    unfold pathname_prefix in H.
    intro; subst.
    eapply H.
    exists path; eauto.
  Qed.

  Lemma pathname_prefix_trim : forall a b c,
    pathname_prefix a b <-> pathname_prefix (c ++ a) (c ++ b).
  Proof.
    unfold pathname_prefix; split; intros; repeat deex.
    - eexists. rewrite <- app_assoc. eauto.
    - rewrite <- app_assoc in H. eexists.
      apply app_inv_head in H. eauto.
  Qed.

  Lemma find_subtree_app': forall suffix path tree subtree,
    find_subtree (path++suffix) tree = Some subtree ->
    exists subtree_base, find_subtree path tree = Some subtree_base /\
      find_subtree suffix subtree_base = Some subtree.
  Proof.
    intros.
    destruct path.
    - eexists tree; intros; subst.
      intuition.
    - case_eq (find_subtree (s :: path) tree); intros; subst.
      eexists d.
      intuition.
      erewrite find_subtree_app with (p0 := (s::path)) in H; eauto.
      exfalso.
      eapply find_subtree_app_none with (p1 := suffix) in H0.
      rewrite H0 in H.
      inversion H.
  Qed.

  Lemma find_subtree_head: forall l name n d,
    find_subtree [name] (TreeDir n ((name,d) :: l)) = Some d.
  Proof.
    intros.
    simpl.
    destruct (string_dec name name); try congruence.
  Qed.

  Lemma find_subtree_head_ne: forall name s n d l,
    name <> s ->
    find_subtree [name] (TreeDir n ((s,d) :: l)) = find_subtree [name] (TreeDir n l).
  Proof.
    intros.
    simpl.
    destruct (string_dec s name); try congruence.
  Qed.

  Lemma update_subtree_update_trim_head_dir: forall l name path n subtree_head subtree,
    find_subtree [name] (TreeDir n l) = Some subtree_head ->
    find_subtree [name] (update_subtree ([name]++path) subtree (TreeDir n l)) =
      Some (update_subtree path subtree subtree_head).
  Proof.
    induction l; intros.
    - exfalso.
      simpl in H.
      inversion H.
    - destruct a; simpl.
      destruct (string_dec s name); subst.
      + simpl.
        destruct (string_dec name name); try congruence.
        rewrite find_subtree_head in H.
        inversion H; eauto.
      + simpl.
        destruct (string_dec s name); try congruence.
        unfold find_subtree in IHl at 2; simpl.
        case_eq (update_subtree ([name] ++ path) subtree (TreeDir n l)); intros.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
  Qed.

  Lemma find_subtree_update_trim_head: forall name path subtree tree subtree_head,
    find_subtree [name] tree = Some subtree_head ->
    find_subtree [name] (update_subtree ([name] ++ path) subtree tree) =
      Some (update_subtree path subtree subtree_head).
  Proof.
    intros. case_eq tree; intros.
    - exfalso.
      subst.
      unfold find_subtree in H; simpl.
      inversion H.
    - erewrite update_subtree_update_trim_head_dir; eauto.
      subst; eauto.
  Qed.

  Lemma update_subtree_update_trim_head_ne: forall tree name s path subtree,
    s <> name ->
    find_subtree [name] (update_subtree (s::path) subtree tree) = 
        find_subtree [name] tree.
  Proof.
    intros; simpl.
    destruct tree; subst; eauto.
    induction l; subst; simpl in *; eauto.
    destruct a; simpl.
    unfold find_subtree_helper at 1; simpl.
    destruct (string_dec s0 s); subst; simpl.
    + destruct (string_dec s name); simpl in *; try congruence.
    + destruct (string_dec s name); simpl in *; try congruence.
      destruct (string_dec s0 name); try congruence.
  Qed.

  Lemma find_subtree_update_subtree_child: forall path suffix tree subtree subtree_child, 
      find_subtree path tree = Some subtree_child ->
      find_subtree path (update_subtree (path++suffix) subtree tree) = 
       Some (update_subtree suffix subtree subtree_child).
  Proof.
    induction path; intros; subst; auto.
    - rewrite app_nil_l.
      simpl in *.
      inversion H; eauto.
     - rewrite cons_app in *.
      eapply find_subtree_app' in H.
      deex.
      erewrite find_subtree_app with (subtree := 
        (update_subtree (path ++ suffix) subtree subtree_base)).
      eapply IHpath; eauto.
      eapply find_subtree_update_trim_head; eauto.
  Qed.

  Lemma find_subtree_update_trim: forall p1 p2 a tree elem subtree d,
    find_subtree [a] tree = Some subtree ->
    find_subtree p2 subtree = Some d ->
    find_subtree p1 (update_subtree p2 elem subtree) = find_subtree p1 subtree ->
    find_subtree (a :: p1) (update_subtree (a::p2) elem tree) = find_subtree (a :: p1) tree.
  Proof.
    intros.
    destruct tree.
    - rewrite cons_app.
      erewrite find_subtree_app.
      2: eauto.
      erewrite find_subtree_app.
      2: eauto.
      reflexivity.
    - rewrite cons_app. 
      erewrite find_subtree_app.
      erewrite find_subtree_app.
      2: eauto.
      eauto.
      setoid_rewrite cons_app at 2.
      erewrite find_subtree_update_subtree_child; eauto.
  Qed.

  Theorem find_subtree_update_subtree_oob'' : forall pn tree a subtree,
    pn <> nil ->
    (~ pathname_prefix [a] pn) ->
    find_subtree [a] (update_subtree pn subtree tree) = find_subtree [a] tree.
  Proof.
    intros.
    destruct pn; try congruence.
    destruct (string_dec a s); subst.
    + exfalso.
      eapply H0.
      unfold pathname_prefix.
      eexists pn.
      eauto.
    + erewrite update_subtree_update_trim_head_ne; eauto.
  Qed.


  Theorem find_subtree_update_subtree_none : forall tree a suffix subtree,
    find_subtree [a] tree = None ->
    find_subtree [a] (update_subtree ([a]++suffix) subtree tree) = None.
  Proof.
    intros.
    destruct tree; eauto.
    induction l; intros.
    - simpl in *; eauto.
    - destruct a0; simpl.
      destruct (string_dec s a); subst.
      + simpl.
        destruct (string_dec a a); try congruence.
        rewrite find_subtree_head in H.
        inversion H; eauto.
      + simpl.
        destruct (string_dec s a); try congruence.
        unfold find_subtree in IHl at 2; simpl.
        case_eq (update_subtree ([a] ++ suffix) subtree (TreeDir n l)); intros.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
  Qed.

  Lemma find_subtree_none_In: forall name n l,
    find_subtree [name] (TreeDir n l) = None ->
    ~In name (map fst l).
  Proof.
    induction l; intros; subst; eauto.
    destruct a.
    erewrite map_cons; simpl.
    intuition.
    subst. erewrite find_subtree_head in H.
    inversion H.
    eapply IHl; eauto.
    destruct (string_dec s name); subst.
    erewrite find_subtree_head in H. inversion H.
    rewrite find_subtree_head_ne in H; eauto.
  Qed.

 Lemma tree_names_distinct_nodup : forall dnum ents,
    tree_names_distinct (TreeDir dnum ents) ->
    NoDup (map fst ents).
  Proof.
    intros; inversion H; auto.
  Qed.


  Lemma update_subtree_path_notfound: forall p tree subtree,
    tree_names_distinct tree ->
    find_subtree p tree = None ->
    update_subtree p subtree tree = tree.
  Proof.
    induction p; intros; subst.
    - simpl in *. exfalso. inversion H0.
    - destruct tree; simpl; eauto.
      f_equal.
      induction l; subst; simpl; eauto.
      destruct a0.
      destruct (string_dec a s); subst.
      simpl.
      destruct (string_dec s s); try congruence.
      rewrite update_subtree_notfound; eauto.
      erewrite IHp; eauto.
      simpl in H0.
      destruct (string_dec s s) in H0; try congruence.
      eapply tree_names_distinct_nodup in H.
      simpl in H.
      inversion H; eauto.
      simpl.
      destruct (string_dec s a); try congruence.
      f_equal.
      eapply IHl.
      eapply tree_name_distinct_rest in H; eauto.
      simpl in H0.
      destruct (string_dec s a) in H0; try congruence.
      simpl; eauto.
  Qed.

  Lemma find_subtree_update_subtree_ne_path : forall p1 p2 tree subtree,
    tree_names_distinct tree ->
    (~ pathname_prefix p2 p1) ->
    (~ pathname_prefix p1 p2) ->
    find_subtree p1 (update_subtree p2 subtree tree) = DIRTREE.find_subtree p1 tree.
  Proof.
    induction p1; intros; auto.
    - exfalso.
      unfold pathname_prefix in *.
      eapply H1.
      exists p2; eauto.
    - destruct (pathname_decide_prefix [a] p2).
      + deex; subst.
        case_eq(find_subtree [a] tree); intros; subst; try congruence.
          -- 
            case_eq(find_subtree ([a]++suffix) tree); intros; subst; try congruence.
            eapply find_subtree_update_trim; eauto.
            eapply find_subtree_app' in H3 as H3'.
            deex.
            rewrite H5 in H2.
            inversion H2; subst.
            eauto.
            eapply IHp1; eauto.
            eapply tree_names_distinct_subtree; eauto.
            setoid_rewrite cons_app in H0 at 3.
            rewrite <- pathname_prefix_trim in H0; eauto.
            rewrite cons_app in H1.
            rewrite <- pathname_prefix_trim in H1; eauto.
            erewrite update_subtree_path_notfound; eauto.
          --  (* a is None *)
          rewrite cons_app.
          erewrite find_subtree_app_none; eauto.
          erewrite find_subtree_app_none; eauto.
          eapply find_subtree_update_subtree_none; eauto.
      + (* p2 doesn't start with a *)
        rewrite cons_app.
        subst; try congruence.
        ++ case_eq(find_subtree [a] tree); intros; subst; try congruence.
          -- (* a is a directory or file *)
            case_eq(find_subtree p2 tree); intros; subst; try congruence.
            erewrite find_subtree_app.
            2: erewrite find_subtree_update_subtree_oob'' with (pn := p2); eauto.
            erewrite find_subtree_app; eauto.
            intro; subst.
            eapply H0.
            unfold pathname_prefix.
            eexists (a::p1); eauto.
            unfold pathname_prefix; intro; apply H2.
            destruct H5.
            exists x; eauto.
            erewrite update_subtree_path_notfound; eauto.
          -- (* a is not present *)
            repeat erewrite find_subtree_app_none; eauto.
            erewrite find_subtree_update_subtree_oob''; eauto.
            intro; subst.
            eapply H0.
            unfold pathname_prefix.
            eexists (a::p1); eauto.
            unfold pathname_prefix; intro; apply H2.
            destruct H4.
            exists x; eauto.
  Qed.

  Lemma find_subtree_delete_same' : forall l rest name n,
    NoDup (map fst l) ->
    find_subtree (name :: rest) (TreeDir n (delete_from_list name l)) = None.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *.
    inversion H; subst.
    destruct (string_dec s name); subst.
    apply find_subtree_ents_not_in; auto.
    simpl. rewrite IHl; auto.
    destruct (string_dec s name); congruence; auto.
  Qed.

  Lemma find_subtree_delete_same : forall l rest name n,
    NoDup (map fst l) ->
    find_subtree (name :: rest) (delete_from_dir name (TreeDir n l)) = None.
  Proof.
    unfold delete_from_dir; eapply find_subtree_delete_same'.
  Qed.

  Lemma find_subtree_delete_ne' : forall l suffix name name' n,
    NoDup (map fst l) ->
    name <> name' ->
    find_subtree (name :: suffix) (TreeDir n (delete_from_list name' l)) = 
      find_subtree (name :: suffix) (TreeDir n l).
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *.
    inversion H; subst.
    destruct (string_dec s name); subst; simpl.
    destruct (string_dec name name'); subst; simpl; try congruence.
    destruct (string_dec name name); subst; simpl; try congruence.
    destruct (string_dec s name); subst; simpl; try congruence.
    destruct (string_dec s name'); subst; simpl; try congruence.
    destruct (string_dec s name); subst; simpl; try congruence.
    eapply IHl; eauto. 
  Qed.


  Lemma find_subtree_delete_ne : forall l suffix name name' n,
    NoDup (map fst l) ->
    name <> name' ->
    find_subtree (name :: suffix) (delete_from_dir name' (TreeDir n l)) = 
      find_subtree (name :: suffix) (TreeDir n l).
  Proof.
    unfold delete_from_dir; eapply find_subtree_delete_ne'.
  Qed.

  Lemma In_delete_from_list_snd : forall l x name,
    In x (map snd (delete_from_list name l)) ->
    In x (map snd l).
  Proof.
    induction l; simpl; auto; intros.
    destruct a.
    destruct (string_dec s name); simpl in *; intuition.
    right; eapply IHl; eauto.
  Qed.

  Lemma In_delete_from_list_fst : forall l x name,
    In x (map fst (delete_from_list name l)) ->
    In x (map fst l).
  Proof.
    induction l; simpl; auto; intros.
    destruct a.
    destruct (string_dec s name); simpl in *; intuition.
    right; eapply IHl; eauto.
  Qed.

  Lemma NoDup_delete_from_list : forall l name,
    NoDup (map fst l) ->
    NoDup (map fst (delete_from_list name l)).
  Proof.
    induction l; simpl; auto; intros.
    inversion H; destruct a; subst; simpl in *.
    destruct (string_dec s name); try congruence.
    simpl; constructor.
    contradict H2.
    eapply In_delete_from_list_fst; eauto.
    apply IHl; auto.
  Qed.

  Lemma tree_names_distinct_delete_from_list : forall l n name,
    tree_names_distinct (TreeDir n l) ->
    tree_names_distinct (TreeDir n (delete_from_list name l)).
  Proof.
    induction l; simpl; intros; auto.
    destruct a; simpl in *.
    inversion H; subst; simpl in *.
    inversion H2; inversion H3; subst.
    destruct (string_dec s name); subst; auto.
    constructor; auto.
    constructor.
    rewrite Forall_forall in *; simpl in *; intuition.
    apply H5.
    eapply In_delete_from_list_snd; eauto.
    simpl; constructor.
    contradict H8.
    eapply In_delete_from_list_fst; eauto.
    apply NoDup_delete_from_list; auto.
  Qed.

  Lemma tree_names_distinct_delete_ne: forall l path name' n subtree,
    NoDup (map fst l) ->
    (~ pathname_prefix [name'] path) ->
    tree_names_distinct (TreeDir n l) ->
    find_subtree path (delete_from_dir name' (TreeDir n l)) = Some subtree ->
    tree_names_distinct subtree.
  Proof.
    induction path; intros; auto.
    - unfold find_subtree in H2; subst; simpl. 
      inversion H2.
      eapply tree_names_distinct_delete_from_list; eauto.
    - rewrite find_subtree_delete_ne in H2; eauto.
      eapply tree_names_distinct_subtree; eauto.
      intro.
      eapply pathname_prefix_head_neq'; eauto.
  Qed.

  Lemma tree_names_distinct_prune_child_subtree: forall path suffix tree name subtree n l,
    tree_names_distinct tree ->
    find_subtree (path ++ suffix) tree = Some (TreeDir n l) ->
    find_subtree path (update_subtree (path++suffix) (delete_from_dir name (TreeDir n l)) tree) 
      = Some subtree ->
    tree_names_distinct subtree.
  Proof.
    intros.
    eapply find_subtree_app' in H0 as H0'.
    destruct H0'; intuition.
    erewrite find_subtree_update_subtree_child in H1; eauto.
    inversion H1.
    eapply tree_names_distinct_update_subtree.
    eapply tree_names_distinct_subtree; eauto.
    eapply tree_names_distinct_delete_from_list; eauto.
    eapply tree_names_distinct_subtree; eauto.
  Qed.


  Lemma tree_names_distinct_prune_subtree : forall path tree path' name subtree n l,
    tree_names_distinct tree ->
    find_subtree path' tree = Some (TreeDir n l) ->
    find_subtree path (tree_prune n l path' name tree) = Some subtree ->
    tree_names_distinct subtree.
  Proof.
    intros.
    unfold tree_prune in *.
    destruct (pathname_decide_prefix path' path).
    + (* path is inside of tree pointed to by path' *)
      (* name cannot be on path because path isn't pruned (H1) *)
      destruct (list_eq_dec string_dec path' path); subst.
      - erewrite find_update_subtree in H1; eauto.
        inversion H1; subst.
        eapply tree_names_distinct_delete_from_list; eauto.
        eapply tree_names_distinct_subtree; eauto.
      - (* compare first component of suffix with name *)         
        destruct H2; subst.
        erewrite find_subtree_app in H1; eauto.
        destruct (pathname_decide_prefix [name] x).
        destruct H2; subst.
        -- (* if equal to name -> contradiction with H1 *)
          erewrite find_subtree_app_none in H1.
          exfalso; congruence.
          erewrite find_subtree_delete_same; eauto.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
         -- (* not equal to name, so not effect *)
          eapply tree_names_distinct_delete_ne; eauto.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
          eapply pathname_prefix_neq; eauto.
          eapply tree_names_distinct_subtree; eauto.
    + destruct (pathname_decide_prefix path path').
      - (* path' is inside of path *)
        destruct H3; subst.
        eapply tree_names_distinct_prune_child_subtree; eauto.
      - (* paths are disjoint, pruning path1 doesn't effect path *)
        erewrite find_subtree_update_subtree_ne_path in H1; eauto.
        eapply tree_names_distinct_subtree; eauto.
        eapply pathname_prefix_neq; eauto.
        eapply pathname_prefix_neq; eauto.
  Qed.

  Lemma pathname_prefix_ex_falso: forall name suffix,
    ~ pathname_prefix [name] suffix ->
    (exists suffix0 : list string, suffix = [name] ++ suffix0) -> False.
  Proof.
    intros.
    deex. exfalso.
    eapply H.
    unfold pathname_prefix.
    exists suffix0; eauto.
  Qed.

  Lemma find_subtree_add_to_dir_same: forall name suffix n subtree l,
    find_subtree (name :: suffix) (TreeDir n (add_to_list name subtree l)) =
    find_subtree suffix subtree.
  Proof.
    induction l; intros; auto.
    - unfold add_to_list.
      rewrite cons_app.
      erewrite find_subtree_app.
      Focus 2.
      erewrite find_subtree_dirlist.
      unfold find_dirlist.
      destruct (string_dec name name); try congruence.
      eauto.
      f_equal.
    -
      destruct a; simpl in *.
      destruct (string_dec s name); subst.
      simpl.
      destruct (string_dec name name); try congruence.
      simpl.
      destruct (string_dec name name); subst; try congruence.
      destruct (string_dec s name); subst; try congruence.
  Qed.

  Lemma find_subtree_add_to_list_oob: forall ents dnum s name subtree d,
    tree_names_distinct (TreeDir dnum ents) ->
    s <> name ->
    find_subtree [s] (TreeDir dnum (add_to_list name subtree ents)) = Some d ->
    find_subtree [s] (TreeDir dnum ents) = Some d.
  Proof.
    induction ents; intros; subst.
    + simpl in H1.
      destruct (string_dec name s); try congruence.
    + destruct a; simpl.
      unfold add_to_list in H1.
      destruct (string_dec s0 name) in H1; try congruence.
      ++ 
        destruct (string_dec s0 s); try congruence.
        simpl in H1.
        destruct (string_dec name s); try congruence.
      ++ 
        destruct (string_dec s0 s); try congruence.
        simpl in H1.
        destruct (string_dec s0 s) in H1; try congruence.
        rewrite find_subtree_head_ne in H1.
        unfold find_subtree in IHents.
        eapply IHents; eauto.
        try congruence.
  Qed.

  Lemma find_subtree_add_to_dir_oob: forall suffix name dnum ents subtree inum f,
     tree_names_distinct (TreeDir dnum ents) ->
     (~pathname_prefix [name] suffix) ->
     find_subtree suffix (add_to_dir name subtree (TreeDir dnum ents)) = Some (TreeFile inum f)->
     find_subtree suffix (add_to_dir name subtree (TreeDir dnum ents)) = find_subtree suffix (TreeDir dnum ents).
  Proof.
    intros.
    destruct suffix.
    - unfold add_to_dir in *. simpl in *.
      inversion H1.
    - destruct (string_dec s name); subst.
      + exfalso.
        eapply H0;  unfold pathname_prefix.
        exists suffix; eauto.
      + erewrite cons_app. erewrite cons_app in H1.
        eapply find_subtree_app' in H1.
        deex.
        erewrite find_subtree_app.
        2: eauto.
        erewrite find_subtree_app; eauto.
        unfold add_to_dir in H2.
        eapply find_subtree_add_to_list_oob; eauto.
  Qed.

  Lemma find_subtree_add_to_dir_oob': forall suffix name tree subtree inum f,
     tree_names_distinct tree ->
     (~pathname_prefix [name] suffix) ->
     find_subtree suffix (add_to_dir name subtree tree) = Some (TreeFile inum f)->
     find_subtree suffix (add_to_dir name subtree tree) = find_subtree suffix tree.
  Proof.
    intros. destruct tree.
    - simpl in H1. 
      destruct suffix.
      + simpl; eauto.
      + unfold find_subtree in H1; simpl.
        inversion H1.
    - erewrite find_subtree_add_to_dir_oob; eauto.
  Qed.

  Lemma find_subtree_rename_oob: forall x n l n' l' dnum ents inum f srcpath srcname dstpath dstname mvtree,
    tree_names_distinct (TreeDir dnum ents) ->
    ~pathname_prefix [dstname] x ->
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_dirlist srcname l = Some mvtree ->
    find_subtree dstpath (tree_prune n l srcpath srcname (TreeDir dnum ents)) =
       Some (TreeDir n' l') ->
    find_subtree (dstpath ++ x) (tree_graft n' l' dstpath dstname mvtree
            (tree_prune n l srcpath srcname (TreeDir dnum ents))) = 
      Some (TreeFile inum f) ->
    find_subtree (dstpath ++ x) (TreeDir dnum ents) = Some (TreeFile inum f).
  Proof.
    intros; cbn.
    unfold tree_prune, tree_graft in *.
    destruct (pathname_decide_prefix srcpath dstpath).
    + repeat deex.
      erewrite find_update_subtree_suffix in H4; eauto.
      erewrite find_update_subtree_suffix in H3; eauto.
      destruct suffix; subst; try congruence.
      -- (* suffix is nil *)
        destruct x; repeat rewrite app_nil_r in *.
        {
          (* x is nil *)
          simpl in H4.
          inversion H4.
        }
        destruct (string_dec srcname s); subst; try congruence.
        ++ (* x starts with srcname *)
          erewrite find_subtree_add_to_dir_oob in H4; eauto.
          simpl in H3.
          inversion H3; subst.
          rewrite find_subtree_delete_same' in H4.
          exfalso; inversion H4.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
          simpl in H3; subst.
          inversion H3.
          rewrite <- H6.
          eapply tree_names_distinct_delete_from_list.
          eapply tree_names_distinct_subtree; eauto.
        ++ (* x doesn't start with srcname *)
          erewrite find_subtree_add_to_dir_oob in H4; eauto.
          simpl in H3.
          inversion H3; subst.
          erewrite find_subtree_delete_ne' in H4; eauto.
          erewrite find_subtree_app; eauto.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
          simpl in H3; subst.
          inversion H3.
          rewrite <- H6.
          eapply tree_names_distinct_delete_from_list.
          eapply tree_names_distinct_subtree; eauto.
      -- (* suffix starts with s *)
        destruct (string_dec s srcname); subst; try congruence.
        {
          rewrite find_subtree_delete_same in H3. exfalso; inversion H3.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        }
        { (* s <> srcname *)
          rewrite find_subtree_delete_ne in H3; eauto.
          destruct x; repeat rewrite app_nil_r in *.
          { (* x is nil *)
            simpl in H4.
            inversion H4.
          }
          erewrite find_subtree_add_to_dir_oob in H4; eauto.
          erewrite find_subtree_app; eauto.
          erewrite find_subtree_app; eauto.
          eapply tree_names_distinct_subtree in H3; eauto.
          eapply tree_names_distinct_subtree; eauto.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        }
    + destruct (pathname_decide_prefix dstpath srcpath).
      - (* dstpath is a prefix of srcpath *)
        deex.
        erewrite find_update_subtree_suffix in H4; eauto.
        eapply find_subtree_app' in H1.
        deex.
        erewrite find_subtree_app. 2:eauto.
        destruct suffix; subst; try congruence.
        -- (* dstpath = srcpath *)
          simpl in H7. inversion H7. subst.
          clear H7.
          repeat rewrite app_nil_r in *.
          erewrite find_update_subtree in H3; eauto.
          inversion H3.
          rewrite <- H8 in *. clear H8. subst.
          unfold add_to_dir, delete_from_dir in *. clear H3.
          destruct H5.
          exists []; rewrite app_nil_r; eauto.
        -- {(* suffix starts with s: srcpath = dstpath+s+suffix *)
            destruct (pathname_decide_prefix (s::suffix++[srcname]) x).
            - (* x is a prefix of s::suffix++srcname. srcname is equal or below x
               * s <> dstname, because x doesn't start with dstname *) 
              deex. subst.
              erewrite find_subtree_add_to_dir_oob in H4; eauto.
              erewrite find_subtree_extend with (p1 := dstpath) in H4.
              2: eauto.
              replace (dstpath ++ (s :: suffix ++ [srcname]) ++ suffix0) with
                      ((dstpath ++ s :: suffix)++([srcname]++suffix0)) in H4.
              erewrite find_update_subtree_suffix in H4.
              rewrite <- cons_app in H4.
              unfold delete_from_dir in H4.
              erewrite find_subtree_delete_same' in H4.
              inversion H4.
              eapply tree_names_distinct_nodup with (dnum:= n).
              eapply tree_names_distinct_subtree in H7; eauto.
              eapply tree_names_distinct_subtree in H6; eauto.
              erewrite find_subtree_app; eauto.
              rewrite <- app_assoc. f_equal. rewrite app_assoc. f_equal.
              eapply tree_names_distinct_subtree. 2: eauto.
              eapply tree_names_distinct_update_subtree;eauto.
              eapply tree_names_distinct_delete_from_list; eauto.
              eapply tree_names_distinct_subtree in H7; eauto.
              eapply tree_names_distinct_subtree in H6; eauto.
            - (* s::suffix++[srcname] isn't a prefix of x *)
              erewrite find_subtree_extend with (p1 := dstpath) in H4.
              2: eauto.
              erewrite find_update_subtree_suffix in H4; eauto.
              erewrite find_subtree_add_to_dir_oob in H4; eauto.
              erewrite find_subtree_extend with (p1 := dstpath) in H4.
              2: eauto.
              destruct (pathname_decide_prefix x ([s]++suffix)).
              ++ (* x is a prefix of [s]++suffix *)
                deex.
                rewrite cons_app in H4.
                rewrite H8 in H4.
                rewrite cons_app in H3.
                rewrite H8 in H3.
                rewrite cons_app in H7.
                rewrite H8 in H7.
                eapply find_subtree_app' in H7.
                deex; intuition.
                erewrite find_subtree_app in H4.
                2: eauto.
                erewrite find_subtree_update_subtree_child in H3.
                2: eauto.
                inversion H3.
                rewrite <- H11 in H4.
                clear H3. clear H11.
                destruct suffix0.
                -- (* x is [s]++suffix] *)
                  rewrite app_nil_r in *.
                  erewrite find_update_subtree in H4; eauto. inversion H4.
                -- 
                  erewrite find_subtree_update_subtree_child in H4; eauto.
                  destruct subtree_base0.
                  unfold find_subtree in H10; inversion H10.
                  unfold update_subtree in H4; simpl in *.
                  inversion H4.
              ++ (* x isn't a prefix of [s]++suffix *)
                destruct (pathname_decide_prefix ([s]++suffix) x).
                +++ (* [s]++suffix is prefix of x *)
                  deex.
                  rewrite app_assoc in H4.
                  erewrite find_update_subtree_suffix in H4.
                  unfold delete_from_dir in H4.
                  destruct suffix0.
                  simpl in H4; inversion H4.
                  erewrite find_subtree_delete_ne' in H4.
                  erewrite find_subtree_app; eauto.
                  eapply tree_names_distinct_nodup with (dnum:= n).
                  eapply tree_names_distinct_subtree in H7; eauto.
                  eapply tree_names_distinct_subtree in H6; eauto.
                  intro.
                  exfalso. eapply H1.
                  eexists suffix0.
                  subst.
                  rewrite cons_app with (a := srcname). 
                  rewrite app_assoc with (l := [s]++suffix).
                  f_equal.
                  erewrite find_subtree_app; eauto.
                +++ (* neither is a prefix of the other *)
                  rewrite find_subtree_update_subtree_ne_path in H4.
                  erewrite find_subtree_app in H4; eauto.
                  eauto.
                  rewrite <- pathname_prefix_trim.
                  unfold pathname_prefix.
                  intro.
                  eapply H9.
                  deex.
                  exists suffix0.
                  f_equal.
                  rewrite <- pathname_prefix_trim.
                  unfold pathname_prefix.
                  intro. eapply H8.
                  deex. eexists suffix0.
                  rewrite cons_app in H10. 
                  rewrite <- H10. reflexivity.
              ++
                  eapply tree_names_distinct_subtree in H3; eauto.
                  eapply tree_names_distinct_update_subtree;eauto.
                  eapply tree_names_distinct_delete_from_list; eauto.
                  eapply tree_names_distinct_subtree in H7; eauto.
                  eapply tree_names_distinct_subtree in H6; eauto.
         }
      - (* dstpath isn't a prefix of srcpath *)
        erewrite find_update_subtree_suffix in H4; eauto.
        erewrite find_subtree_update_subtree_ne_path in H3; eauto.
        erewrite find_subtree_add_to_dir_oob in H4; eauto.
        eapply find_subtree_app with (p1 := x) in H3; eauto.
        rewrite H4 in H3; eauto.
        eapply tree_names_distinct_subtree; eauto.
        eapply pathname_prefix_neq; eauto.
        eapply pathname_prefix_neq; eauto.
  Qed.

  (* pathname outside of srcpath++srcname and dst tree, but maybe in srcpath *)
  Lemma find_subtree_rename_oob_srcname_dst: forall pathname dstpath dstname srcpath srcname n l dnum ents inum f,
    (~pathname_prefix (srcpath++[srcname]) pathname) ->
    (~pathname_prefix (dstpath++[dstname]) pathname) ->
    (~pathname_prefix dstpath pathname) ->
    tree_names_distinct (TreeDir dnum ents) ->   
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_subtree pathname
       (update_subtree srcpath (TreeDir n (delete_from_list srcname l))
          (TreeDir dnum ents)) = Some (TreeFile inum f) ->
    find_subtree pathname (TreeDir dnum ents) = Some (TreeFile inum f).
  Proof.
    intros; cbn.
    destruct (pathname_decide_prefix srcpath pathname).
    -- (* srcpath is a prefix of pathname *)
      deex. 
      denote update_subtree as Hx.
      erewrite find_update_subtree_suffix in Hx; eauto.
      {
        destruct suffix.
        - rewrite app_nil_r in *. unfold find_subtree in Hx; inversion Hx.
        - destruct (string_dec srcname s); subst.
          + exfalso. eapply H. exists suffix. rewrite <- app_assoc.
            f_equal.
          + erewrite find_subtree_delete_ne' in Hx.
            erewrite find_subtree_app; eauto.
            eapply tree_names_distinct_nodup; eauto.
            eapply tree_names_distinct_subtree; eauto.
            congruence.
      }
    -- destruct (pathname_decide_prefix pathname srcpath).
      {
        deex.
        eapply find_subtree_app' in H3. deex; intuition.
        destruct subtree_base; try congruence.
        + unfold find_subtree in H7.
          destruct suffix; try congruence.
        + erewrite find_subtree_update_subtree_child in H4; eauto.
          destruct suffix; unfold update_subtree in H4; try congruence.
       }
      (* pathname has nothing in common with srcpath and dstpath *)
      erewrite find_subtree_update_subtree_ne_path in H4; eauto.
      eapply pathname_prefix_neq; eauto.
      eapply pathname_prefix_neq; eauto.
  Qed.

  Lemma rename_safe_dest_none : 
    forall ilist1 ilist2 frees1 frees2 srcpath srcname dstpath dstname dnum ents n l n' l' mvtree,
    let pruned  := tree_prune n l srcpath srcname (TreeDir dnum ents) in
    let grafted := tree_graft n' l' dstpath dstname mvtree pruned in
    tree_names_distinct (TreeDir dnum ents) ->
    tree_inodes_distinct (TreeDir dnum ents) ->
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_subtree dstpath pruned = Some (TreeDir n' l') ->
    ~ In dstname (map fst l') ->
    find_dirlist srcname l = Some mvtree ->
    BFILE.ilist_safe ilist1 frees1 ilist2 frees2 ->
    dirtree_safe ilist1 frees1 (TreeDir dnum ents) ilist2 frees2 grafted.
  Proof.
    cbn; intros.
    eapply dirtree_safe_ilist_trans; eauto.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.

    destruct (pathname_decide_prefix (dstpath ++ [dstname]) pathname).
    - repeat deex.
      exists (srcpath ++ [srcname] ++ suffix); exists f.
      denote tree_graft as Hx.
      rewrite <- app_assoc in Hx.
      erewrite find_subtree_app in Hx by (
        erewrite <- tree_graft_not_in_dirents by auto;
        eapply find_update_subtree; eauto).

      erewrite find_subtree_app by eauto.
      erewrite find_subtree_app.

      2: apply find_dirlist_find_subtree_helper; eauto.
      erewrite find_subtree_app in Hx; eauto.
      apply find_subtree_leaf_in.
      apply in_app_iff.
      right; simpl; auto.
      rewrite map_app; apply NoDup_app_comm; simpl.
      constructor; auto.

      eapply tree_names_distinct_nodup.
      eapply tree_names_distinct_prune_subtree; eauto.
      eapply tree_names_distinct_nodup.
      eapply tree_names_distinct_subtree; eauto.

    - exists pathname, f.
      destruct (pathname_decide_prefix dstpath pathname).
      + (* in dstpath, but not in dstpath/dstname *)
        deex.
        eapply find_subtree_rename_oob; eauto.
        intro.
        eapply H8.
        unfold pathname_prefix in H9.
        deex.
        exists suffix0.
        rewrite app_assoc; eauto. 
      + (* not in dstpath *)
        apply find_subtree_update_subtree_oob' in H6; auto.
        unfold tree_prune, delete_from_dir in H6.
        destruct (pathname_decide_prefix (srcpath++[srcname]) pathname); repeat deex.
        * (* srcpath++srcname is a prefix of pathname *)
          exfalso.
          erewrite <- app_assoc in H6.
          erewrite find_update_subtree_suffix in H6; eauto.
          rewrite <- cons_app in H6.
          rewrite find_subtree_delete_same' in H6; try congruence.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        * (* pathname outside of srcpath++srcname and dst tree, but maybe in srcpath *)
          erewrite find_subtree_rename_oob_srcname_dst; eauto.
          eapply pathname_prefix_neq; eauto.
          eapply pathname_prefix_neq with (path' := (dstpath++[dstname])); eauto.
          eapply pathname_prefix_neq; eauto.
  Qed.

  Lemma rename_safe_dest_exists : 
    forall ilist1 ilist2 ilist3 frees1 frees2 frees3
           srcpath srcname dstpath dstname dnum ents n l n' l' mvtree,
    let pruned  := tree_prune n l srcpath srcname (TreeDir dnum ents) in
    let deleted := update_subtree dstpath (TreeDir n' (delete_from_list dstname l')) pruned in
    let grafted := tree_graft n' l' dstpath dstname mvtree pruned in
    tree_names_distinct (TreeDir dnum ents) ->
    tree_inodes_distinct (TreeDir dnum ents) ->
    find_subtree srcpath (TreeDir dnum ents) = Some (TreeDir n l) ->
    find_subtree dstpath pruned = Some (TreeDir n' l') ->
    find_dirlist srcname l = Some mvtree ->
    dirtree_safe ilist1 frees1 pruned ilist2 frees2 deleted ->
    BFILE.ilist_safe ilist2 frees2 ilist3 frees3 ->
    dirtree_safe ilist1 frees1 (TreeDir dnum ents) ilist3 frees3 grafted.
  Proof.
    cbn; intros.
    eapply dirtree_safe_ilist_trans; eauto.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.
    destruct (pathname_decide_prefix (dstpath ++ [dstname]) pathname).
    - repeat deex.
      exists (srcpath ++ [srcname] ++ suffix); exists f.
      denote tree_graft as Hx.
      rewrite <- app_assoc in Hx.
      unfold tree_graft, tree_prune, add_to_dir in Hx.
      erewrite find_update_subtree_suffix in Hx; eauto.
      rewrite <- cons_app in Hx.
      erewrite find_subtree_add_to_dir_same in Hx.
      erewrite find_subtree_app; eauto.
      erewrite find_subtree_app; eauto.
      apply find_dirlist_find_subtree_helper; eauto.
      eapply tree_names_distinct_nodup with (dnum := n).
      eapply tree_names_distinct_subtree; eauto.
    - exists pathname, f.
      destruct (pathname_decide_prefix dstpath pathname).
      + (* in dstpath, but not in dstpath/dstname *)
        deex.
        eapply find_subtree_rename_oob; eauto.
        intro.
        eapply H8.
        unfold pathname_prefix in H9.
        deex.
        exists suffix0.
        rewrite app_assoc; eauto.          
      + (* not in dstpath *)
        apply find_subtree_update_subtree_oob' in H6; auto.
        unfold tree_prune, delete_from_dir in H6.
        destruct (pathname_decide_prefix (srcpath++[srcname]) pathname); repeat deex.
        * (* srcpath++srcname is a prefix of pathname *)
          exfalso.
          erewrite <- app_assoc in H6.
          erewrite find_update_subtree_suffix in H6; eauto.
          rewrite <- cons_app in H6.
          rewrite find_subtree_delete_same' in H6; try congruence.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        * (* pathname outside of srcpath++srcname and dst tree, but maybe in srcpath *)
          erewrite find_subtree_rename_oob_srcname_dst; eauto.
          eapply pathname_prefix_neq; eauto.
          eapply pathname_prefix_neq with (path' := (dstpath++[dstname])); eauto.
          eapply pathname_prefix_neq; eauto.
    - unfold dirtree_safe in *; eapply BFILE.ilist_safe_trans; intuition eauto.
  Qed.

  Definition read fsxp inum off mscs :=
    let^ (mscs, v) <- BFILE.read (FSXPLog fsxp) (FSXPInode fsxp) inum off mscs;
    Ret ^(mscs, v).

  Definition write fsxp inum off v mscs :=
    mscs <- BFILE.write (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    Ret mscs.

  Definition dwrite fsxp inum off v mscs :=
    mscs <- BFILE.dwrite (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    Ret mscs.

  Definition datasync fsxp inum mscs :=
    mscs <- BFILE.datasync (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    Ret mscs.

  Definition sync fsxp mscs :=
    mscs <- BFILE.sync (FSXPLog fsxp) (FSXPInode fsxp) mscs;
    Ret mscs.

  Definition sync_noop fsxp mscs :=
    mscs <- BFILE.sync_noop (FSXPLog fsxp) (FSXPInode fsxp) mscs;
    Ret mscs.

  Definition truncate fsxp inum nblocks mscs :=
    let^ (mscs, ok) <- BFILE.truncate (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                     inum nblocks mscs;
    Ret ^(mscs, ok).

  Definition getlen fsxp inum mscs :=
    let^ (mscs, len) <- BFILE.getlen (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    Ret ^(mscs, len).

  Definition getattr fsxp inum mscs :=
    let^ (mscs, attr) <- BFILE.getattrs (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    Ret ^(mscs, attr).

  Definition setattr fsxp inum attr mscs :=
    mscs <- BFILE.setattrs (FSXPLog fsxp) (FSXPInode fsxp) inum attr mscs;
    Ret mscs.

  Definition updattr fsxp inum kv mscs :=
    mscs <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum kv mscs;
    Ret mscs.

  Lemma find_subtree_inum_valid : forall F F' xp m s tree inum f,
    find_subtree s tree = Some (TreeFile inum f)
    -> (F * tree_pred xp tree * F')%pred m
    -> IAlloc.ino_valid xp inum.
  Proof.
    unfold rep; intros.
    destruct_lift H0.
    rewrite subtree_extract in H0 by eauto.
    simpl in H0; destruct_lift H0; auto.
  Qed.

  Theorem read_ok : forall fsxp inum off mscs,
    {< F mbase m pathname Fm Ftop tree f B v ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') hm' *
           [[ r = fst v /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} read fsxp inum off mscs.
  Proof.
    unfold read, rep.
    safestep.
    eapply list2nmem_inbound; eauto.
    rewrite subtree_extract; eauto. cancel.
    eauto.
    step.
    cancel; eauto.
  Qed.

  Theorem dwrite_ok : forall fsxp inum off v mscs,
    {< F ds pathname Fm Ftop tree f Fd vs ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds ds!!) (MSLL mscs) hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           exists ds' tree' f' bn,
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds' ds'!!) (MSLL mscs') hm' *
           [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
           [[ BFILE.block_belong_to_file ilist bn inum off ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           (* spec about files on the latest diskset *)
           [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees) ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = BFILE.mk_bfile (updN (BFILE.BFData f) off (v, vsmerge vs)) (BFILE.BFAttr f) ]] *
           [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                           ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm' \/
           exists bn, [[ BFILE.block_belong_to_file ilist bn inum off ]] *
           LOG.recover_any fsxp.(FSXPLog) F (dsupd ds bn (v, vsmerge vs)) hm'
    >} dwrite fsxp inum off v mscs.
  Proof.
    unfold dwrite, rep.
    step.
    eapply list2nmem_inbound; eauto.
    rewrite subtree_extract; eauto. cancel.
    eauto.
    step.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file.
  Qed.

 Theorem datasync_ok : forall fsxp inum mscs,
    {< F ds pathname Fm Ftop tree f ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds ds!!) (MSLL mscs) hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           exists ds' tree' al,
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds' ds'!!) (MSLL mscs') hm' *
           [[ tree' = update_subtree pathname (TreeFile inum (BFILE.synced_file f)) tree ]] *
           [[ ds' = dssync_vecs ds al ]] *
           [[[ ds'!! ::: (Fm * rep fsxp Ftop tree' ilist frees) ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]] *
           [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                           ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    CRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
    >} datasync fsxp inum mscs.
  Proof.
    unfold datasync, rep.
    safestep.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file.
  Qed.


  Theorem sync_ok : forall fsxp mscs,
    {< F ds Fm Ftop tree ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees ]]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn (ds!!, nil)) (MSLL mscs') hm' *
           [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
     >} sync fsxp mscs.
  Proof.
    unfold sync, rep.
    hoare.
  Qed.

  Theorem sync_noop_ok : forall fsxp mscs,
    {< F ds Fm Ftop tree ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees ]]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) (MSLL mscs') hm' *
           [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
     >} sync_noop fsxp mscs.
  Proof.
    unfold sync_noop, rep.
    hoare.
  Qed.

  Theorem truncate_ok : forall fsxp inum nblocks mscs,
    {< F ds d pathname Fm Ftop tree f frees ilist,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) (MSLL mscs) hm *
           [[[ d ::: Fm * rep fsxp Ftop tree ilist frees ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs', ok)
           exists d',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
          ([[ isError ok ]] \/
           [[ ok = OK tt ]] *
           exists tree' f' ilist' frees',
           [[[ d' ::: Fm * rep fsxp Ftop tree' ilist' frees' ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) nblocks ($0, nil)) (BFILE.BFAttr f) ]] *
           [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                           ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
           [[ nblocks >= Datatypes.length (BFILE.BFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F ds hm'
    >} truncate fsxp inum nblocks mscs.
  Proof.
    unfold truncate, rep.
    intros.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    or_r.
    cancel.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file_trans; auto.
  Qed.


  Theorem getlen_ok : forall fsxp inum mscs,
    {< F mbase m pathname Fm Ftop tree f frees ilist,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') hm' *
           [[ r = length (BFILE.BFData f) ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} getlen fsxp inum mscs.
  Proof.
    unfold getlen, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
  Qed.

  Theorem getattr_ok : forall fsxp inum mscs,
    {< F ds d pathname Fm Ftop tree f ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) (MSLL mscs) hm *
           [[[ d ::: Fm * rep fsxp Ftop tree ilist frees ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) (MSLL mscs') hm' *
           [[ r = BFILE.BFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F ds hm'
    >} getattr fsxp inum mscs.
  Proof.
    unfold getattr, rep.
    safestep.
    rewrite subtree_extract; eauto. cancel.
    step.
    cancel; eauto.
  Qed.

  Theorem setattr_ok : forall fsxp inum attr mscs,
    {< F mbase m pathname Fm Ftop tree f ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] 
    POST:hm' RET:mscs'
           exists m' tree' f' ilist',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ (Fm * rep fsxp Ftop tree' ilist' frees)%pred (list2nmem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                           ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
           [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} setattr fsxp inum attr mscs.
  Proof.
    unfold setattr, rep.
    step.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.
    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file_trans; auto.
  Qed.


  Hint Extern 1 ({{_}} Bind (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (datasync _ _ _) _) => apply datasync_ok : prog.
  Hint Extern 1 ({{_}} Bind (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (sync_noop _ _) _) => apply sync_noop_ok : prog.
  Hint Extern 1 ({{_}} Bind (truncate _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} Bind (getlen _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} Bind (getattr _ _ _) _) => apply getattr_ok : prog.
  Hint Extern 1 ({{_}} Bind (setattr _ _ _ _) _) => apply setattr_ok : prog.


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
      eauto.
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
 
  Lemma update_name_twice: forall tree_elem name tree subtree subtree' dnum,
    tree_names_distinct
      (update_subtree ([name]) subtree'
         (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem))
            tree)) ->
    update_subtree [name] subtree' (update_subtree [] (add_to_dir name subtree (TreeDir dnum tree_elem)) tree) =
    update_subtree [] (add_to_dir name subtree' (TreeDir dnum tree_elem)) tree.
  Proof.
    induction tree_elem; intros; subst; simpl.
    - destruct (string_dec name name).
      reflexivity.
      congruence.
    - destruct a.
      destruct (string_dec s name); subst; simpl in *.
      destruct (string_dec name name); try congruence.
      rewrite update_subtree_notfound.
      reflexivity.
      erewrite <- tree_names_distinct_head_name'.
      eapply tree_names_distinct_head_name.
      simpl in H.
      destruct (string_dec name name); try congruence.
      apply H.
      destruct (string_dec s name); try congruence.
      simpl in H.
      apply tree_name_distinct_rest in H.
      specialize (IHtree_elem name d subtree subtree' dnum H).
      inversion IHtree_elem.
      rewrite H1.
      reflexivity.
  Qed.


  (* Rewrite using the tree induction principle doesn't really work out *)
  Lemma update_update_subtree_twice: forall prefix name subtree' subtree d dnum tree_elem,
    tree_names_distinct 
       (update_subtree (prefix ++ [name]) subtree'
          (update_subtree prefix
             (add_to_dir name subtree (TreeDir dnum tree_elem)) d)) ->
    update_subtree (prefix ++ [name]) subtree'
       (update_subtree prefix (add_to_dir name subtree (TreeDir dnum tree_elem)) d) =
        update_subtree prefix (add_to_dir name subtree' (TreeDir dnum tree_elem)) d.
  Proof.
   induction prefix; intros.
   - rewrite app_nil_l.
     rewrite update_name_twice by auto.
     reflexivity.
   - destruct d. 
     simpl.
     reflexivity.
     induction l; subst; simpl.
     + reflexivity.
     + destruct a0.
      simpl in *.
      destruct (string_dec s a).
      simpl in *.
      destruct (string_dec s a).
      subst; simpl in *.
      erewrite IHprefix.
      apply tree_name_distinct_rest in H.
      specialize (IHl H).
      inversion IHl.
      rewrite H1.
      eauto.
      eapply tree_name_distinct_head.
      eauto.
      exfalso.
      congruence.
      simpl in *.
      destruct (string_dec s a).
      exfalso.
      congruence.
      simpl in *.
      apply tree_name_distinct_rest in H.
      specialize (IHl H).
      inversion IHl.
      rewrite H1.
      eauto.
  Qed.

  Lemma update_update_subtree_same : forall pn tree subtree subtree',
    update_subtree pn subtree (update_subtree pn subtree' tree) = update_subtree pn subtree tree.
  Proof.
    induction pn; simpl; intros; eauto.
    destruct tree; eauto.
    f_equal.
    induction l; eauto.
    destruct a0; simpl.
    rewrite IHl; f_equal.
    destruct (string_dec s a); subst; simpl.
    destruct (string_dec a a); congruence.
    destruct (string_dec s a); congruence.
  Qed.

  Theorem update_subtree_tree_graft: 
    forall prefix name tree dnum tree_elem subtree subtree' F Ftop m fsxp ilist frees,
    (F * rep fsxp Ftop (update_subtree (prefix++[name]) subtree' 
                        (tree_graft dnum tree_elem prefix name subtree tree)) ilist frees)%pred m -> 
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    update_subtree (prefix++[name]) subtree' (tree_graft dnum tree_elem prefix name subtree tree) = 
            (tree_graft dnum tree_elem prefix name subtree' tree).
  Proof.
    intros.
    unfold tree_graft in *.
    erewrite update_update_subtree_twice with (dnum := dnum) (tree_elem := tree_elem).
    reflexivity.
    eapply rep_tree_names_distinct.
    eauto.
  Qed.


  Theorem dirtree_dir_parts : forall t,
    dirtree_isdir t = true ->
    t = TreeDir (dirtree_inum t) (dirtree_dirents t).
  Proof.
    destruct t; simpl; intros; congruence.
  Qed.

  Theorem dirtree_file_parts : forall t,
    dirtree_isdir t = false ->
    t = TreeFile (dirtree_inum t) (dirtree_file t).
  Proof.
    destruct t; simpl; intros; congruence.
  Qed.

  Lemma find_subtree_file_none: forall s suffix n b,
    find_subtree (s::suffix) (TreeFile n b) = None.
  Proof.
    intros.
    rewrite cons_app.
    rewrite find_subtree_app_none; eauto.
  Qed.

  Lemma tree_inodes_distinct_elem: forall a n l subtree,
    tree_inodes_distinct (TreeDir n l) ->
    find_subtree [a] (TreeDir n l) = Some subtree ->
    tree_inodes_distinct subtree.
  Proof.
    induction l; intros; subst.
    - simpl in H0. inversion H0.
    - destruct a0.
      destruct (string_dec a s); subst.
      + rewrite find_subtree_head in H0. inversion H0. subst. clear H0.
        eapply tree_inodes_distinct_child in H; eauto.
      + erewrite find_subtree_head_ne in H0.
        eapply tree_inodes_distinct_next in H; eauto.
        eauto.
  Qed.

  Lemma tree_inodes_distinct_subtree : forall path tree subtree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree path tree = Some subtree ->
    tree_inodes_distinct subtree.
  Proof.
    induction path; intros.
    - simpl in H1. inversion H1. subst. eauto. 
    - destruct tree.
      + rewrite find_subtree_file_none in H1. inversion H1.
      + destruct l.
        -- 
          simpl in H1. inversion H1.
        -- 
          destruct p.
          destruct (string_dec a s); subst.
          ++
            rewrite cons_app in H1.
            eapply find_subtree_app' in H1.
            deex.
            eapply tree_inodes_distinct_child in H0.
            rewrite find_subtree_head in H2; eauto.
            inversion H2. subst. clear H2.
            eauto.
          ++
            rewrite cons_app in H1.
            eapply find_subtree_app' in H1.
            deex.
            eapply IHpath in H3; eauto.
            eapply tree_names_distinct_subtree; eauto.
            rewrite find_subtree_head_ne in H2; eauto.
            eapply tree_inodes_distinct_next in H0; eauto.
            eapply tree_inodes_distinct_elem in H2; eauto.
  Qed.

  Lemma leaf_in_inodes_parent : forall path name n l subtree_base d,
    tree_names_distinct (TreeDir n l) ->
    find_subtree [name] (TreeDir n l) = Some subtree_base ->
    find_subtree path subtree_base = Some d ->
    In (dirtree_inum d) (dirlist_combine tree_inodes l).
  Proof.
    induction l; intros.
    - unfold find_subtree in H0. simpl in H0. inversion H0.
    - rewrite dirlist_combine_app.
      eapply in_or_app.
      destruct a.
      destruct (string_dec name s); subst.
      ++ 
        left; simpl. rewrite app_nil_r.
        erewrite find_subtree_dirlist in H0; eauto.
        apply find_dirlist_same in H0 as H0'; subst.
        eapply find_subtree_inum_present; eauto.
        inversion H.
        simpl in H5; eauto.
      ++
        right; simpl.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H0; eauto.
  Qed.

  Lemma tree_inodes_not_distinct: forall l n s f suffix,
    tree_names_distinct (TreeDir n l) ->
    tree_inodes_distinct (TreeDir n l) ->
    find_subtree (s :: suffix) (TreeDir n l) = Some f ->
    dirtree_inum (TreeDir n l) = dirtree_inum f ->
    False.
  Proof.
    intros.
    rewrite cons_app in H1.
    eapply find_subtree_app' in H1; eauto.
    deex.
    eapply leaf_in_inodes_parent in H4 as H4'; eauto.
    rewrite <- H2 in H4'. simpl in H4'.
    inversion H0.
    eapply H6; eauto.
  Qed.

  Theorem find_subtree_inode_pathname_unique : forall path1 path2 tree f1 f2,
    tree_inodes_distinct tree ->
    tree_names_distinct tree ->
    find_subtree path1 tree = Some f1 ->
    find_subtree path2 tree = Some f2 -> 
    dirtree_inum f1 = dirtree_inum f2 ->
    path1 = path2.
  Proof.
    induction path1; intros.
    - destruct path2; try congruence.
      destruct tree. simpl in *; try congruence.
      exfalso; eapply tree_inodes_not_distinct; eauto.
      simpl in *; inversion H1; subst; simpl in *; congruence.
    - destruct path2.
      + destruct tree. simpl in *; try congruence.
        exfalso; eapply tree_inodes_not_distinct; eauto.
        simpl in *; inversion H2; subst; simpl in *; congruence.
      + destruct (string_dec a s); subst.
        * f_equal.
          rewrite cons_app in *.
          case_eq (find_subtree [s] tree); intros. destruct d.
         -- erewrite find_subtree_app in * by eauto; simpl in *.
            destruct path1; destruct path2; simpl in *; congruence.
         -- erewrite find_subtree_app in * by eauto.
            eapply IHpath1 with (tree := TreeDir n l); eauto.
            eapply tree_inodes_distinct_subtree; eauto.
            eapply tree_names_distinct_subtree; eauto.
         -- erewrite find_subtree_app_none in * by eauto; congruence.
        * destruct tree. simpl in *; try congruence.
          unfold tree_inodes_distinct in H; simpl in *.
          exfalso.
          induction l; simpl in *; try congruence.
          destruct a0; simpl in *.
          destruct (string_dec s0 a).
          {
            clear IHl.
            apply find_subtree_inum_present in H1.
            destruct (string_dec s0 s); try congruence.
            induction l; simpl in *; try congruence.
            destruct a0; simpl in *.
            destruct (string_dec s1 s).
            {
              apply find_subtree_inum_present in H2.
              rewrite cons_app in H; rewrite app_assoc in H.
              rewrite H3 in *.
              eapply not_In_NoDup_app with (a := dirtree_inum f2). 2: eauto. eauto. eauto.
            }
            eapply IHl; eauto.
            rewrite app_comm_cons in *; eapply NoDup_remove_mid; eauto.
            inversion H0; constructor; eauto; simpl in *.
            inversion H6. inversion H11. eauto.
            rewrite cons_app with (a := s0) in *.
            rewrite cons_app with (a := s1) in *.
            eapply NoDup_remove_mid; eauto.
          }
          destruct (string_dec s0 s).
          {
            clear IHl.
            apply find_subtree_inum_present in H2.
            destruct (string_dec s0 a); try congruence.
            induction l; simpl in *; try congruence.
            destruct a0; simpl in *.
            destruct (string_dec s1 a).
            {
              apply find_subtree_inum_present in H1.
              rewrite cons_app in H; rewrite app_assoc in H.
              rewrite H3 in *.
              eapply not_In_NoDup_app with (a := dirtree_inum f2). 2: eauto. eauto. eauto.
            }
            eapply IHl; eauto.
            rewrite app_comm_cons in *; eapply NoDup_remove_mid; eauto.
            inversion H0; constructor; eauto; simpl in *.
            inversion H6. inversion H11. eauto.
            rewrite cons_app with (a := s0) in *.
            rewrite cons_app with (a := s1) in *.
            eapply NoDup_remove_mid; eauto.
          }
          eapply IHl; eauto.
          inversion H; constructor; eauto.
  Qed.

  Theorem update_subtree_app : forall p0 p1 tree subtree t,
    tree_names_distinct tree ->
    find_subtree p0 tree = Some subtree ->
    update_subtree (p0 ++ p1) t tree = update_subtree p0 (update_subtree p1 t subtree) tree.
  Proof.
    induction p0; simpl; intros.
    congruence.
    destruct tree; try congruence.
    f_equal.
    induction l; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; eauto.
    - erewrite IHp0; eauto.
      f_equal.
      repeat rewrite update_subtree_notfound; eauto.
      inversion H; inversion H4; eauto.
      inversion H; inversion H4; eauto.
    - f_equal.
      eapply IHl; eauto.
  Qed.

  Lemma dirtree_safe_dupdate: forall old_tree old_free old_ilist tree ilist freelist inum f p off v,
    tree_names_distinct tree ->
    dirtree_safe old_ilist old_free old_tree ilist freelist tree ->
    find_subtree p tree = Some (TreeFile inum f) ->
    dirtree_safe old_ilist old_free old_tree ilist freelist
      (update_subtree p (TreeFile inum
        {| BFILE.BFData := (BFILE.BFData f) ⟦ off := v ⟧;
            BFILE.BFAttr := BFILE.BFAttr f |}) tree).
   Proof.
    unfold dirtree_safe; intuition.
    destruct (pathname_decide_prefix pathname p); repeat deex.
    {
      destruct suffix; try rewrite app_nil_r in *.
      - erewrite find_update_subtree in H0 by eauto. inversion H0; subst. eauto.
      - case_eq (find_subtree pathname tree); intros. destruct d.
        + erewrite find_subtree_app in H1 by eauto; simpl in *; congruence.
        + erewrite find_subtree_app in H1 by eauto.
          erewrite update_subtree_app in H0 by eauto.
          erewrite find_update_subtree in H0 by eauto.
          simpl in *; congruence.
        + erewrite find_subtree_app_none in H1 by eauto; congruence.
    }

    destruct (pathname_decide_prefix p pathname); repeat deex.
    {
      exfalso.
      destruct suffix; try rewrite app_nil_r in *.
      apply H5. exists nil. rewrite app_nil_r; auto.
      erewrite find_subtree_app in H0.
      2: erewrite find_update_subtree; eauto.
      simpl in *; congruence.
    }

    rewrite find_subtree_update_subtree_ne_path in H0; eauto.
    unfold pathname_prefix. contradict H6; deex; eauto.
    unfold pathname_prefix. contradict H5; deex; eauto.
  Qed.

  Lemma find_subtree_dir_after_update_subtree : forall base pn t num ents subtree,
    tree_names_distinct t ->
    find_subtree pn t = Some (TreeDir num ents) ->
    ~ (exists suffix : list string, pn = base ++ suffix) ->
    exists ents,
    find_subtree pn (update_subtree base subtree t) = Some (TreeDir num ents).
  Proof.
    induction base; intros.
    - simpl in *.
      contradiction H1; eauto.
    - destruct pn; simpl in *.
      + destruct t; try congruence.
        inversion H0; subst. eauto.
      + destruct t; simpl in *; try congruence.
        induction l; simpl in *; eauto.
        destruct a0. simpl in *.
        destruct (string_dec s0 s); destruct (string_dec s0 a); repeat subst; simpl in *.
        * destruct (string_dec a a); subst; try congruence.
          eapply IHbase; eauto.
          intro. deex. eauto.
        * destruct (string_dec s s); try congruence; eauto.
        * destruct (string_dec a s); try congruence; eauto.
        * destruct (string_dec s0 s); try congruence; eauto.
  Qed.

  Lemma find_subtree_none_after_update_subtree : forall base pn t subtree,
    tree_names_distinct t ->
    find_subtree pn t = None ->
    ~ (exists suffix : list string, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree t) = None.
  Proof.
    induction base; intros.
    - simpl in *.
      contradiction H1; eauto.
    - destruct pn; simpl in *.
      + destruct t; try congruence.
      + destruct t; simpl in *; try congruence.
        induction l; simpl in *; eauto.
        destruct a0. simpl in *.
        destruct (string_dec s0 s); destruct (string_dec s0 a); repeat subst; simpl in *.
        * destruct (string_dec a a); subst; try congruence.
          eapply IHbase; eauto.
          intro. deex. eauto.
        * destruct (string_dec s s); try congruence; eauto.
        * destruct (string_dec a s); try congruence; eauto.
        * destruct (string_dec s0 s); try congruence; eauto.
  Qed.


  Theorem find_subtree_graft_subtree_oob: forall pn num ents base name tree subtree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    find_subtree pn (tree_graft num ents base name subtree tree) = Some (TreeFile inum f).
  Proof.
    unfold tree_graft; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1 by eassumption.
      erewrite find_subtree_app.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; congruence.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * specialize (IHents H1).
          destruct (string_dec s0 name); subst.
          -- simpl. destruct (string_dec name s); congruence.
          -- simpl. destruct (string_dec s0 s); congruence.
    - eapply find_subtree_update_subtree_oob; eauto.
  Qed.

 Theorem find_subtree_graft_subtree_oob': forall pn num ents base name tree subtree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn (tree_graft num ents base name subtree tree) = Some (TreeFile inum f) ->
    find_subtree pn tree = Some (TreeFile inum f).
  Proof.
    unfold tree_graft; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1.
      erewrite find_subtree_app by eassumption.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; try congruence.
        destruct (string_dec name s); subst; simpl in *; try congruence.
        contradict H0; eauto.
        exists suffix.
        rewrite <- app_assoc.
        simpl. eauto.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * destruct (string_dec s0 name); subst; simpl in *; try congruence.
          destruct (string_dec name s); subst; simpl in *; try congruence.
          destruct (string_dec s0 s); subst; simpl in *; try congruence.
          specialize (IHents H1).
          eauto.
    - eapply find_subtree_update_subtree_oob'; eauto.
  Qed.

  Theorem find_subtree_prune_subtree_oob: forall pn num ents base name tree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn tree = Some (TreeFile inum f) ->
    find_subtree pn (tree_prune num ents base name tree) = Some (TreeFile inum f).
  Proof.
    unfold tree_prune; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1 by eassumption.
      erewrite find_subtree_app.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; congruence.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * specialize (IHents H1).
          destruct (string_dec s0 name); subst.
          -- simpl. destruct (string_dec name s); congruence.
          -- simpl. destruct (string_dec s0 s); congruence.
    - eapply find_subtree_update_subtree_oob; eauto.
  Qed.

  Theorem find_subtree_prune_subtree_oob': forall pn num ents base name tree inum f,
    find_subtree base tree = Some (TreeDir num ents) ->
    (~ pathname_prefix (base ++ [name]) pn) ->
    find_subtree pn (tree_prune num ents base name tree) = Some (TreeFile inum f) ->
    find_subtree pn tree = Some (TreeFile inum f).
  Proof.
   unfold tree_prune; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1.
      erewrite find_subtree_app by eassumption.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; try congruence.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * destruct (string_dec s0 name); subst; simpl in *; try congruence.
          destruct (string_dec s0 s); subst; simpl in *; try congruence.
          specialize (IHents H1).
          eauto.
    - eapply find_subtree_update_subtree_oob'; eauto.
  Qed.

  Lemma find_rename_oob: forall tree subtree cwd dnum tree_elem srcnum srcbase 
         srcents srcname dstnum dstbase dstents dstname pathname inum f,
    (~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname) ->
    (~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname) -> 
    find_subtree pathname tree = Some (TreeFile inum f) ->
    find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some subtree ->
    find_subtree dstbase
      (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)) =
      Some (TreeDir dstnum dstents) ->
    find_subtree pathname
     (update_subtree cwd
       (tree_graft dstnum dstents dstbase dstname subtree
        (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)))
     tree) = Some (TreeFile inum f).
  Proof.
    intros.
    destruct (pathname_decide_prefix cwd pathname).
    + destruct (pathname_decide_prefix (cwd ++ srcbase ++ [srcname]) pathname).
      - (* pathname is inside src subtree; contradiction *)
        destruct H7.
        rewrite H7 in H.
        unfold prefix in H.
        destruct H.
        eexists x; eauto.
       - (* pathname isn't inside src subtree *)
        destruct (pathname_decide_prefix (cwd ++ dstbase ++ [dstname]) pathname).
        ++ (* pathname is inside dst tree; contradiction *)
          destruct H8.
          rewrite H8 in *.
          unfold pathname_prefix in H0.
          destruct H0.
          eexists x; eauto.
        ++ (* pathname isn't inside src and isn't inside dst tree, but inside cwd *)
          deex.
          erewrite find_subtree_app; eauto.
          erewrite find_subtree_graft_subtree_oob; eauto.
          intro; apply H0. apply pathname_prefix_trim. eauto.
          erewrite find_subtree_prune_subtree_oob; eauto.
          intro; apply H. apply pathname_prefix_trim. eauto.
          erewrite find_subtree_app in H1; eauto.
    + (* pathname is outside of cwd *)
      unfold tree_graft, tree_prune.
      erewrite find_subtree_update_subtree_oob; eauto.
  Qed.

  Lemma find_rename_oob': forall tree subtree cwd dnum tree_elem srcnum srcbase 
         srcents srcname dstnum dstbase dstents dstname pathname inum f,
    (~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname) ->
    (~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname) -> 
    find_subtree cwd tree = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some subtree ->
    find_subtree dstbase
      (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)) =
      Some (TreeDir dstnum dstents) ->
    find_subtree pathname
     (update_subtree cwd
       (tree_graft dstnum dstents dstbase dstname subtree
        (tree_prune srcnum srcents srcbase srcname (TreeDir dnum tree_elem)))
     tree) = Some (TreeFile inum f) ->
    find_subtree pathname tree = Some (TreeFile inum f).
  Proof.
    intros.
    destruct (pathname_decide_prefix cwd pathname).
    + destruct (pathname_decide_prefix (cwd ++ srcbase ++ [srcname]) pathname).
      - (* pathname is inside src subtree; contradiction *)
        destruct H7.
        rewrite H7 in H.
        unfold pathname_prefix in H.
        destruct H.
        eexists x; eauto.
       - (* pathname isn't inside src subtree *)
        destruct (pathname_decide_prefix (cwd ++ dstbase ++ [dstname]) pathname).
        ++ (* pathname is inside dst tree; contradiction *)
          destruct H8.
          rewrite H8 in *.
          unfold pathname_prefix in H0.
          destruct H0.
          eexists x; eauto.
        ++ (* pathname isn't inside src and isn't inside dst tree, but inside cwd *)
          deex.
          erewrite find_subtree_app in H5; eauto.
          erewrite find_subtree_app.
          2: eauto.
          erewrite find_subtree_prune_subtree_oob'. 
          Focus 4.
          eapply find_subtree_graft_subtree_oob'.
          3: eauto.
          eauto.
          intro; apply H0. apply pathname_prefix_trim. eauto.
          all: eauto.
          intro; apply H. apply pathname_prefix_trim. eauto.
    + (* pathname is outside of cwd *)
      unfold tree_graft, tree_prune.
      erewrite find_subtree_update_subtree_oob'; eauto.
  Qed. 


  Lemma dirtree_name_in_dents: forall T name tree_elem elem f,
    fold_right (DIRTREE.find_subtree_helper f name) (@None T) tree_elem = Some elem
    -> In name (map fst tree_elem).
  Proof.
    intros.
    induction tree_elem.
    - intros. simpl in H. congruence.
    - destruct a.
      destruct (string_dec s name).
      rewrite cons_app.
      rewrite map_app.
      apply in_app_iff.
      simpl.
      left.
      auto.
      rewrite cons_app.
      rewrite map_app.
      apply in_or_app.
      right.
      apply IHtree_elem.
      rewrite cons_app in H.
      rewrite fold_right_app in H.
      simpl in H.
      destruct (string_dec s name).
      congruence.
      assumption.
  Qed.

  Lemma find_subtree_tree_names_distinct: forall pn t subtree,
      tree_names_distinct t ->
      find_subtree pn t = Some subtree ->
      tree_names_distinct subtree.
  Proof.
    induction pn; intros; simpl in *.
    - congruence.
    - destruct t; try congruence.
      induction l.
      -- simpl in *; try congruence.
      -- destruct a0; subst; simpl in *.
        destruct (string_dec s a); subst; simpl in *.
        + eapply IHpn. 2: eauto.
          eapply tree_names_distinct_child; eauto.
        + eapply IHl; eauto.
  Qed.      

  Lemma find_subtree_tree_inodes_distinct: forall pn t subtree,
      tree_inodes_distinct t ->
      find_subtree pn t = Some subtree ->
      tree_inodes_distinct subtree.
  Proof.
    induction pn; intros; simpl in *.
    - congruence.
    - destruct t; try congruence.
      induction l.
      -- simpl in *; try congruence.
      -- destruct a0; subst; simpl in *.
        destruct (string_dec s a); subst; simpl in *.
        + eapply IHpn. 2: eauto.
          eapply tree_inodes_distinct_child; eauto.
        + eapply IHl; eauto.
  Qed.

  Lemma find_subtree_before_prune_general : forall pn t num ents base name subtree,
    tree_names_distinct t ->
    find_subtree base t = Some (TreeDir num ents) ->
    find_subtree pn (tree_prune num ents base name t) = Some subtree ->
    exists subtree',
      find_subtree pn t = Some subtree' /\
      dirtree_inum subtree = dirtree_inum subtree' /\
      dirtree_isdir subtree = dirtree_isdir subtree'.
  Proof.
    unfold tree_prune; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1; eauto.
      cut (exists subtree',
                find_subtree (suffix) (TreeDir num ents) = Some subtree' /\
                dirtree_inum subtree = dirtree_inum subtree' /\
                dirtree_isdir subtree = dirtree_isdir subtree').
      intros.
      deex.
      eexists.
      erewrite find_subtree_app; eauto.
      eapply find_subtree_tree_names_distinct in H; eauto.
      clear H0.
      destruct suffix; simpl in *.
      + inversion H1; subst.
        eauto.
      + 
        induction ents; simpl in *.
        * destruct suffix; simpl in *.
          inversion H1; subst.
          eexists; eauto.
        * destruct a; simpl in *.
          destruct (string_dec s0 name); subst.
          ** rewrite H1; simpl.
             destruct (string_dec name s); subst; try congruence.
             eapply dirtree_name_in_dents in H1; eauto.
             inversion H.
             inversion H4; eauto.
             exfalso; eauto.
             eauto.
          ** simpl in *.
             destruct (string_dec s0 s); subst; eauto.
    - clear H0.
      generalize dependent (delete_from_dir name (TreeDir num ents)).
      generalize dependent pn.
      generalize dependent t.
      induction base; intros.
      + simpl in *.
        contradiction H2.
        eauto.
      + destruct pn.
        ++ simpl in *.
            destruct t.
            inversion H1; subst; eauto.
            inversion H1; subst; eauto.
        ++ destruct t; simpl in *; try congruence.
           induction l.
           * simpl in *; try congruence.
           * destruct a0. simpl in *.
             destruct (string_dec s0 s); destruct (string_dec s0 a); repeat subst; simpl in *.
             -- destruct (string_dec s s); subst; try congruence. 
                eapply IHbase; eauto.
                intro. deex.
                apply H2. subst. eexists.
                eauto.
             -- destruct (string_dec s s); try congruence; eauto.
             -- destruct (string_dec a s); try congruence; eauto.
             -- destruct (string_dec s0 s); try congruence; eauto.
  Qed.

  Lemma find_subtree_before_prune : forall pn t num ents base name dnum0 ents0,
    tree_names_distinct t ->
    find_subtree base t = Some (TreeDir num ents) ->
    find_subtree pn (tree_prune num ents base name t) = Some (TreeDir dnum0 ents0) ->
    exists ents1,
    find_subtree pn t = Some (TreeDir dnum0 ents1).
  Proof.
    intros.
    edestruct find_subtree_before_prune_general; eauto.
    intuition.
    destruct x; simpl in *; try congruence; subst.
    eexists; eauto.
  Qed.

  Lemma find_subtree_pruned_none : forall tree base name basenum basedents,
    tree_names_distinct tree ->
    find_subtree base tree = Some (TreeDir basenum basedents) ->
    find_subtree (base ++ [name]) (tree_prune basenum basedents base name tree) = None.
  Proof.
    intros.
    unfold tree_prune.
    erewrite find_subtree_app.
    2: erewrite find_update_subtree; eauto.
    simpl.
    eapply find_subtree_tree_names_distinct in H0; eauto.
    inversion H0; clear H0; subst.
    clear H3.
    induction basedents; simpl in *; eauto.
    destruct a.
    destruct (string_dec s name); subst.
    - rewrite find_subtree_ents_not_in; eauto.
      inversion H4; eauto.
    - simpl.
      destruct (string_dec s name); try congruence.
      eapply IHbasedents.
      inversion H4; eauto.
  Qed.


  Lemma tree_names_distinct_prune_subtree' : forall inum ents base name tree,
    tree_names_distinct tree ->
    find_subtree base tree = Some (TreeDir inum ents) ->
    tree_names_distinct (tree_prune inum ents base name tree).
  Proof.
    intros.
    eapply tree_names_distinct_prune_subtree with (path := nil) in H0.
    eauto.
    eauto.
    simpl; eauto.
  Qed.

  Lemma rep_tree_distinct_impl : forall fsxp Ftop tree ilist frees,
    rep fsxp Ftop tree ilist frees =p=> rep fsxp Ftop tree ilist frees *
      [[ tree_names_distinct tree ]] *
      [[ tree_inodes_distinct tree ]].
  Proof.
    unfold pimpl; intros.
    assert ((emp * rep fsxp Ftop tree ilist frees)%pred m) by ( pred_apply; cancel ).
    eapply rep_tree_names_distinct in H0 as H0'.
    eapply rep_tree_inodes_distinct in H0 as H0''.
    pred_apply; cancel.
  Qed.

  Lemma tree_inodes_distinct_update_subtree : forall pn t subtree subtree',
    tree_names_distinct t ->
    tree_inodes_distinct t ->
    tree_inodes_distinct subtree ->
    find_subtree pn t = Some subtree' ->
    incl (tree_inodes subtree) (tree_inodes subtree') ->
    (tree_inodes_distinct (update_subtree pn subtree t) /\
     incl (tree_inodes (update_subtree pn subtree t)) (tree_inodes t)).
  Proof.
    unfold tree_inodes_distinct.
    induction pn; simpl; intros.
    {
      intuition. inversion H2; subst. eauto.
    }

    destruct t; simpl. intuition eauto. eapply incl_refl.

    induction l; simpl; eauto.
    intuition.

    destruct a0; simpl in *.
    inversion H2; subst.

    destruct (string_dec s a).

    - rewrite update_subtree_notfound by
        ( inversion H; inversion H8; subst; eauto ).
      edestruct IHpn with (t := d); eauto.

      eapply NoDup_app_l.
      eapply NoDup_app_r.
      rewrite cons_app in *; eauto.

      split.
      + rewrite cons_app in *. eapply NoDup_incl_l; eauto.
        eapply NoDup_incl_r; eauto.
        eapply incl_app2l; eauto.
      + repeat rewrite cons_app with (l := app _ _).
        eapply incl_app2r; eauto.
        eapply incl_app2l; eauto.

    - edestruct IHl; eauto.
      rewrite cons_app in *.
      eapply NoDup_remove_mid; eauto.

      split.
      + rewrite cons_app in *. rewrite app_assoc in *.
        eapply NoDup_incl_l; eauto.
        eapply incl_cons2_inv; simpl in *; eauto.
        inversion H4; eauto.
      + repeat rewrite cons_app with (l := app _ _) in *.
        eapply incl_app. intuition.
        eapply incl_app. eapply incl_appr. eapply incl_appl. apply incl_refl.
        intro; intro. eapply In_incl.
        2: eapply incl_tran.
        eauto.
        eapply incl_tl; apply incl_refl.
        eapply incl_tran; eauto.
        rewrite cons_app.
        eapply incl_app. apply incl_appl. apply incl_refl.
        apply incl_appr. apply incl_appr. apply incl_refl.
  Qed.

  Lemma tree_inodes_incl_delete_from_list : forall name l,
    incl (dirlist_combine tree_inodes (delete_from_list name l))
         (dirlist_combine tree_inodes l).
  Proof.
    induction l; simpl; eauto.
    eapply incl_refl.
    destruct a.
    destruct (string_dec s name); subst.
    - eapply incl_appr; apply incl_refl.
    - simpl.
      eapply incl_app2r. eauto.
  Qed.

  Lemma tree_inodes_nodup_delete_from_list : forall name l,
    NoDup (dirlist_combine tree_inodes l) ->
    NoDup (dirlist_combine tree_inodes (delete_from_list name l)).
  Proof.
    induction l; simpl; eauto; intros.
    destruct a.
    destruct (string_dec s name); subst.
    - eapply NoDup_app_r; eauto.
    - simpl.
      eapply NoDup_incl_l; eauto.
      eapply tree_inodes_incl_delete_from_list.
  Qed.

  Lemma tree_inodes_distinct_delete_from_list : forall l n name,
    tree_inodes_distinct (TreeDir n l) ->
    tree_inodes_distinct (TreeDir n (delete_from_list name l)).
  Proof.
    unfold tree_inodes_distinct; simpl; intros.
    inversion H; subst.
    constructor.
    - contradict H2.
      eapply In_incl; eauto.
      eapply tree_inodes_incl_delete_from_list.
    - eapply tree_inodes_nodup_delete_from_list; eauto.
  Qed.

  Lemma tree_inodes_find_subtree_incl : forall pathname t subtree,
    find_subtree pathname t = Some subtree ->
    incl (tree_inodes subtree) (tree_inodes t).
  Proof.
    induction pathname; simpl; intros.
    congruence.
    destruct t; simpl in *; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst.
    - rewrite cons_app. apply incl_appr. apply incl_appl. eapply IHpathname. eauto.
    - rewrite cons_app in *.
      specialize (IHl H).
      intro; intro. specialize (IHl _ H0).
      apply in_app_or in IHl; intuition.
  Qed.

  Theorem delete_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] * exists tree' ilist' frees',
            [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees')%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum def', inum <> dnum ->
                 (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
                selN ilist inum def' = selN ilist' inum def' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} delete fsxp dnum name mscs.
  Proof.
    intros; eapply pimpl_ok2. apply delete_ok'.

    intros; norml; unfold stars; simpl.
    rewrite rep_tree_distinct_impl in *.
    unfold rep in *; cancel.

    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0:=tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
    eapply dirlist_safe_subtree; eauto.
    specialize (H12 inum def' H4).
    intuition; try congruence.

    destruct_lift H0.
    edestruct tree_inodes_pathname_exists. 3: eauto.
    eapply tree_names_distinct_update_subtree; eauto.
    eapply tree_names_distinct_delete_from_list.
    eapply tree_names_distinct_subtree; eauto.

    eapply tree_inodes_distinct_update_subtree; eauto.
    eapply tree_inodes_distinct_delete_from_list.
    eapply tree_inodes_distinct_subtree; eauto.
    simpl. eapply incl_cons2.
    eapply tree_inodes_incl_delete_from_list.

    (* case A: inum inside tree' *)

    repeat deex.
    destruct (pathname_decide_prefix pathname x); repeat deex.

    (* case 1: in the directory *)
    erewrite find_subtree_app in *; eauto.
    eapply H12.

    eapply find_subtree_inum_present in H16; simpl in *.
    intuition. exfalso; eauto.

    (* case 2: outside the directory *)
    eapply H9.
    intro.
    edestruct tree_inodes_pathname_exists with (tree := TreeDir dnum tree_elem) (inum := dirtree_inum subtree).
    3: eassumption.

    eapply tree_names_distinct_subtree; eauto.
    eapply tree_inodes_distinct_subtree; eauto.

    destruct H20.
    destruct H20.

    eapply H6.
    exists x0.

    edestruct find_subtree_before_prune_general; eauto.

    eapply find_subtree_inode_pathname_unique.
    eauto. eauto.
    intuition eauto.
    erewrite find_subtree_app; eauto.
    intuition congruence.

    (* case B: outside original tree *)
    eapply H12; eauto.
    right.
    contradict H7; intuition eauto. exfalso; eauto.
    eapply tree_inodes_find_subtree_incl; eauto.
    simpl; intuition.
  Qed.

  Hint Extern 1 ({{_}} Bind (delete _ _ _ _) _) => apply delete_ok : prog.


  Definition conflicting (p q : Prop) := (p -> ~ q) /\ (q -> ~ p).
  Definition xor (p q : Prop) := (p /\ ~ q) \/ (q /\ ~ p).

  Lemma NoDup_In_conflicting : forall T (l1 l2 : list T) x,
    NoDup (l1 ++ l2) ->
    conflicting (In x l1) (In x l2).
  Proof.
    unfold conflicting; split; intros; eapply not_In_NoDup_app; eauto.
    eapply NoDup_app_comm; eauto.
  Qed.

  Lemma tree_inodes_after_prune' : forall srcpath t srcnum srcents srcname mvtree,
    tree_names_distinct t ->
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    permutation addr_eq_dec
      (tree_inodes mvtree ++ tree_inodes (tree_prune srcnum srcents srcpath srcname t))
      (tree_inodes t).
  Proof.
    induction srcpath; simpl; intros.
    - inversion H0; clear H0; subst; simpl in *.

      induction srcents; simpl in *; try congruence; intros.
      destruct a.
      destruct (string_dec s srcname).
      + inversion H1; clear H1; subst.
        rewrite cons_app. rewrite cons_app with (l := app _ _).
        repeat rewrite app_assoc.
        eauto with permutation_app.

      + simpl in *.
        rewrite cons_app. rewrite cons_app with (l := app _ _).
        rewrite app_assoc. eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_app_split. apply permutation_refl.
        eapply permutation_trans. eapply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_trans. apply IHsrcents; eauto.
        eapply permutation_trans. 2: apply permutation_app_comm.
        apply permutation_refl.

    - destruct t; simpl in *; try congruence.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite update_subtree_notfound in * by ( inversion H; inversion H5; eauto ).
        eapply IHsrcpath in H1; clear IHsrcpath. 3: eauto. 2: eauto.
        unfold tree_prune, delete_from_dir in *.

        rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        apply permutation_app_split. apply permutation_refl. rewrite <- app_assoc.
        eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_trans. 2: apply permutation_app_comm.
        eapply permutation_app_split. apply permutation_refl.
        eauto.

      + clear IHsrcpath.
        rewrite cons_app. rewrite cons_app with (l := app _ _).
        rewrite app_assoc. eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_app_split. apply permutation_refl.
        eapply permutation_trans. 2: apply permutation_app_comm.
        eapply permutation_trans. 2: eapply IHl; eauto.
        eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        eapply permutation_app_split. apply permutation_refl.
        apply permutation_refl.
  Qed.

  Lemma tree_inodes_after_prune : forall srcpath t srcnum srcents srcname mvtree inum,
    tree_inodes_distinct t ->
    tree_names_distinct t ->
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    conflicting (In inum (tree_inodes mvtree))
                (In inum (tree_inodes (tree_prune srcnum srcents srcpath srcname t))).
  Proof.
    intros.
    eapply NoDup_In_conflicting.
    unfold tree_inodes_distinct in *.
    eapply tree_inodes_after_prune' in H2; eauto.
    eapply permutation_incl_count in H2.
    eapply NoDup_incl_count; eauto.
  Qed.

  Lemma tree_inodes_after_graft' : forall dstpath t dstnum dstents dstname mvtree,
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    permutation
      addr_eq_dec
      (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t))
      ((tree_inodes mvtree) ++
       (tree_inodes (tree_prune dstnum dstents dstpath dstname t))).
  Proof.
    unfold tree_graft, tree_prune.
    induction dstpath; simpl; intros.
    - inversion H0; clear H0; subst.
      induction dstents; simpl; intros.
      + rewrite app_nil_r. rewrite cons_app.
        apply permutation_app_comm.
      + destruct a.
        destruct (string_dec s dstname); subst.
        * simpl. rewrite cons_app. rewrite cons_app with (l := dirlist_combine _ _).
          repeat rewrite app_assoc. apply permutation_app_split.
          2: apply permutation_refl.
          apply permutation_app_comm.
        * simpl. rewrite cons_app. rewrite cons_app with (l := app _ _).
          eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
          eapply permutation_trans. 2: rewrite app_assoc. 2: apply permutation_app_comm.
          rewrite <- app_assoc.
          apply permutation_app_split. apply permutation_refl.
          eapply permutation_trans. apply permutation_app_comm.
          eapply permutation_trans. 2: apply permutation_app_comm.
          rewrite <- app_assoc.
          eauto.
    - destruct t; simpl in *; try congruence.
      induction l; simpl in *; try congruence; intros.
      destruct a0; simpl.
      destruct (string_dec s a); subst; simpl in *.
      + inversion H; inversion H4; subst.
        repeat rewrite update_subtree_notfound by auto.
        rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        apply permutation_app_split. apply permutation_refl.
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite app_assoc.
        apply permutation_app_split. 2: apply permutation_refl.
        destruct (string_dec a a); try congruence.
        eapply IHdstpath; eauto.
      + rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
        rewrite app_assoc with (l := tree_inodes mvtree).
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        apply permutation_app_split. apply permutation_refl.
        eapply permutation_trans. apply permutation_app_comm.
        eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
        destruct (string_dec s a); try congruence.
        eauto.
  Qed.

  Lemma tree_inodes_tree_graft_incl_count : forall dstpath t dstnum dstents dstname mvtree,
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    incl_count addr_eq_dec
      (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t))
      (tree_inodes t ++ tree_inodes mvtree).
  Proof.
    unfold tree_graft.
    induction dstpath; simpl; intros.
    - inversion H0; clear H0; subst.
      induction dstents; simpl in *; intros.
      rewrite app_nil_r. apply incl_count_refl.
      destruct a.
      destruct (string_dec s dstname); subst; simpl in *.
      + apply incl_count_cons.
        eapply incl_count_trans. 2: apply incl_count_app_comm.
        eapply incl_count_app_split. apply incl_count_refl.
        rewrite <- app_nil_l at 1.
        eapply incl_count_app_split. 2: apply incl_count_refl.
        apply incl_count_nil.
      + rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply incl_count_trans. apply incl_count_app_comm.
        eapply incl_count_trans. 2: apply incl_count_app_comm.
        repeat rewrite <- app_assoc.
        eapply incl_count_app_split. apply incl_count_refl.
        eapply incl_count_trans. apply incl_count_app_comm.
        rewrite app_assoc. eapply incl_count_trans. 2: apply incl_count_app_comm.
        eauto.
    - destruct t; simpl in *; try congruence.
      induction l; simpl in *; try congruence; intros.
      destruct a0; simpl.
      destruct (string_dec s a); subst; simpl in *.
      + destruct (string_dec a a); try congruence.
        inversion H. inversion H4. subst.
        repeat rewrite update_subtree_notfound by auto.
        rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply incl_count_app_split. apply incl_count_refl.
        eapply incl_count_trans. 2: apply incl_count_app_comm.
        rewrite app_assoc. eapply incl_count_app_split. 2: apply incl_count_refl.
        eapply incl_count_trans. 2: apply incl_count_app_comm.
        eauto.
      + rewrite cons_app. rewrite cons_app with (l := app _ _).
        eapply incl_count_trans. apply incl_count_app_comm.
        eapply incl_count_trans. 2: apply incl_count_app_comm.
        repeat rewrite <- app_assoc.
        eapply incl_count_app_split. apply incl_count_refl.
        rewrite app_assoc.
        eapply incl_count_trans. apply incl_count_app_comm.
        eapply incl_count_trans. 2: apply incl_count_app_comm.
        destruct (string_dec s a); try congruence.
        eauto.
  Qed.

  Lemma tree_inodes_after_graft : forall dstpath t dstnum dstents dstname mvtree inum,
    NoDup (tree_inodes t ++ tree_inodes mvtree) ->
    tree_names_distinct t ->
    find_subtree dstpath t = Some (TreeDir dstnum dstents) ->
    In inum (tree_inodes (tree_graft dstnum dstents dstpath dstname mvtree t)) ->
    xor (In inum (tree_inodes mvtree))
        (In inum (tree_inodes (tree_prune dstnum dstents dstpath dstname t))).
  Proof.
    unfold xor; intros.
    pose proof (tree_inodes_after_graft' _ dstname mvtree H0 H1).
    eapply NoDup_incl_count in H; [ | apply tree_inodes_tree_graft_incl_count; eauto ].
    eapply NoDup_incl_count in H; [ | apply permutation_incl_count; apply permutation_comm; eauto ].
    eapply NoDup_In_conflicting with (x := inum) in H as H'; unfold conflicting in *; intuition.
    eapply In_incl in H2.
    2: apply incl_count_incl with (E := addr_eq_dec).
    2: apply permutation_incl_count; eauto.
    apply in_app_or in H2.
    intuition.
  Qed.

  Lemma tree_inodes_nodup_delete_from_list' : forall srcpath srcname srcents srcnum t mvtree top_extras,
    forall (Hd : tree_names_distinct t),
    find_subtree srcpath t = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    NoDup (top_extras ++ tree_inodes t) ->
    NoDup (top_extras ++ tree_inodes (tree_prune srcnum srcents srcpath srcname t) ++ tree_inodes mvtree).
  Proof.
    induction srcpath; simpl; intros.
    - inversion H; clear H; subst.
      simpl in *.

      match goal with
      | [ H : NoDup (top_extras ++ ?n :: ?x) |- NoDup (top_extras ++ ?n :: ?y) ] =>
        cut (forall extra_inodes, NoDup (n :: extra_inodes ++ x) -> NoDup (n :: extra_inodes ++ y));
        [ intro Hcut; specialize (Hcut top_extras); nodupapp
        | intros ]
      end.

      clear H1.
      generalize dependent extra_inodes.
      induction srcents; simpl in *; try congruence; intros.
      destruct a.
      destruct (string_dec s srcname); subst; simpl.
      + inversion H0; clear H0; subst.
        nodupapp.
      + rewrite app_assoc. rewrite app_assoc. rewrite <- app_assoc.
        eapply IHsrcents; eauto. nodupapp.
    - destruct t; simpl in *; try congruence.

      match goal with
      | [ H : NoDup (top_extras ++ ?n :: ?x) |- NoDup (top_extras ++ ?n :: ?y) ] =>
        cut (forall extra_inodes, NoDup (n :: extra_inodes ++ x) -> NoDup (n :: extra_inodes ++ y));
        [ intro Hcut; specialize (Hcut top_extras); nodupapp
        | intros ]
      end.

      clear H1.
      generalize dependent extra_inodes.
      induction l; simpl in *; try congruence; intros.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; simpl.
      + rewrite update_subtree_notfound.
        rewrite cons_app in H2. rewrite app_assoc in H2. rewrite app_assoc in H2. apply NoDup_app_comm in H2.
        rewrite app_assoc in H2.
        eapply IHsrcpath in H2; eauto.
        unfold tree_prune in H2.
        simpl in *.
        nodupapp.
        inversion Hd; inversion H5; eauto.
      + rewrite app_assoc in H2.
        eapply IHl in H2; eauto.
        nodupapp.
  Grab Existential Variables.
    all: exact addr_eq_dec.
  Qed.

  Lemma prune_graft_preserves_inodes : forall srcpath srcname srcnum srcents
                                              dstpath dstname dstnum dstents
                                              mvtree tree_elem dnum inum,
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    tree_names_distinct (TreeDir dnum tree_elem) ->
    find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ->
    find_dirlist srcname srcents = Some mvtree ->
    find_subtree dstpath (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)) =
      Some (TreeDir dstnum dstents) ->
    In inum (tree_inodes
      (tree_graft dstnum dstents dstpath dstname mvtree
        (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)))) ->
    (In inum (tree_inodes
       (update_subtree dstpath (TreeDir dstnum (delete_from_list dstname dstents))
         (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)))) \/
     ~ In inum (tree_inodes (tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem)))).
  Proof.
    intros.
    apply tree_inodes_after_graft in H4; eauto; unfold xor in H4.
    intuition.
    right; intros.
    eapply tree_inodes_after_prune in H4.
    6: eauto.
    all: eauto.
    2: eapply tree_names_distinct_prune_subtree'; eauto.
    eapply tree_inodes_nodup_delete_from_list' with (top_extras := nil); eauto.
  Qed.

  Lemma incl_app_commr: forall (A: Type) (l: list A) l1 l2,
    incl l (l1++l2) -> incl l (l2++l1).
  Proof.
    unfold incl; intros.
    eapply in_or_app.
    specialize (H _ H0).
    eapply in_app_or in H.
    intuition.
  Qed.

  Lemma incl_app_comml: forall (A: Type) (l: list A) l1 l2,
    incl (l1++l2) l -> incl (l2++l1) l.
  Proof.
    unfold incl; intros.
    apply H.
    eapply in_or_app.
    eapply in_app_or in H0.
    intuition.
  Qed.

  Lemma tree_inodes_incl_delete_from_dir : forall pathname dnum tree_elem name pnum pelem,
    tree_names_distinct (TreeDir dnum tree_elem) ->
    tree_inodes_distinct (TreeDir dnum tree_elem) ->
    find_subtree pathname (TreeDir dnum tree_elem) = Some (TreeDir pnum pelem) ->
    incl (tree_inodes (update_subtree pathname (delete_from_dir name (TreeDir pnum pelem)) (TreeDir dnum tree_elem)))
         (tree_inodes (TreeDir dnum tree_elem)).
  Proof.
    induction pathname; intros; subst.
    - simpl in *. inversion H1; subst.
      eapply incl_cons2.
      eapply tree_inodes_incl_delete_from_list; eauto.
    - induction tree_elem; intros; subst.
      + simpl. eapply incl_refl.
      + destruct a0.
        destruct (string_dec a s); subst.
        * simpl in *.
          destruct (string_dec s s); subst; try congruence.
          repeat rewrite cons_app with (a := dnum) (l := app _ _).
          apply incl_app_commr; apply incl_app_comml.
          repeat rewrite <- app_assoc.
          apply incl_app.
          apply incl_appl.
         -- destruct d.
            destruct pathname; simpl in *; congruence.
            eapply IHpathname; eauto.
         -- apply incl_appr.
            apply incl_app_commr; apply incl_app_comml.
            rewrite update_subtree_notfound. apply incl_refl. inversion H. inversion H5. eauto.
        * simpl in *.
          destruct (string_dec s a); subst; try congruence.
          repeat rewrite cons_app with (a := dnum) (l := app _ _).
          apply incl_app_commr; apply incl_app_comml.
          repeat rewrite <- app_assoc.
          apply incl_app.
          apply incl_appl. apply incl_refl.
          apply incl_appr.
          apply incl_app_commr; apply incl_app_comml.
          eapply IHtree_elem; eauto.
  Qed.

  Theorem rename_ok' : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] * exists snum sents dnum dents subtree pruned tree' ilist' frees',
            [[ find_subtree srcpath tree = Some (TreeDir snum sents) ]] *
            [[ find_dirlist srcname sents = Some subtree ]] *
            [[ pruned = tree_prune snum sents srcpath srcname tree ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dnum dents) ]] *
            [[ tree' = tree_graft dnum dents dstpath dstname subtree pruned ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees')%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum' def', inum' <> snum -> inum' <> dnum ->
               (In inum' (tree_inodes tree') \/ (~ In inum' (tree_inodes tree))) ->
               selN ilist inum' def' = selN ilist' inum' def' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rep.

    (* extract some basic facts *)
    prestep; norm'l.
    assert (tree_inodes_distinct (TreeDir dnum tree_elem)) as HnID.
    eapply rep_tree_inodes_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.
    assert (tree_names_distinct (TreeDir dnum tree_elem)) as HiID.
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.

    (* namei srcpath, isolate root tree file before cancel *)
    subst; simpl in *.
    denote tree_dir_names_pred as Hx; assert (Horig := Hx).
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.  instantiate (tree := TreeDir dnum tree_elem).
    unfold rep; simpl.
    unfold tree_dir_names_pred; cancel.
    all: eauto.

    (* lookup srcname, isolate src directory before cancel *)
    destruct_branch; [ | step ].
    destruct_branch; destruct_branch; [ | step ].
    prestep; norm'l.
    intuition; inv_option_eq; repeat deex; destruct_pairs.
    denote find_name as Htree.
    apply eq_sym in Htree.
    apply find_name_exists in Htree.
    destruct Htree. intuition.

    denote find_subtree as Htree; assert (Hx := Htree).
    apply subtree_extract with (xp := fsxp) in Hx.
    assert (Hsub := Horig); rewrite Hx in Hsub; clear Hx.
    destruct x; simpl in *; subst; try congruence.
    unfold tree_dir_names_pred in Hsub.
    destruct_lift Hsub.
    denote (_ |-> _)%pred as Hsub.

    safecancel. 2: eauto.
    unfold SDIR.rep_macro.
    cancel; eauto.

    (* unlink src *)
    step.

    (* namei for dstpath, find out pruning subtree before step *)
    denote (tree_dir_names_pred' l0 _) as Hx1.
    denote (_ |-> (_, _))%pred as Hx2.
    pose proof (ptsto_subtree_exists _ Hx1 Hx2) as Hx.
    destruct Hx; intuition.

    step.
    eapply subtree_prune_absorb; eauto.
    apply dir_names_pred_delete'; auto.
    rewrite tree_prune_preserve_inum; auto.
    rewrite tree_prune_preserve_isdir; auto.

    (* fold back predicate for the pruned tree in hypothesis as well  *)
    denote (list2nmem flist) as Hinterm.
    apply helper_reorder_sep_star_1 in Hinterm.
    erewrite subtree_prune_absorb in Hinterm; eauto.
    2: apply dir_names_pred_delete'; auto.
    apply helper_reorder_sep_star_2 in Hinterm.
    rename x into mvtree.

    (* lookup dstname *)
    destruct_branch; [ | step ].
    destruct_branch; destruct_branch; [ | step ].
    prestep; norm'l.
    intuition; inv_option_eq; repeat deex; destruct_pairs.

    denote find_name as Hpruned.
    apply eq_sym in Hpruned.
    apply find_name_exists in Hpruned.
    destruct Hpruned. intuition.

    denote find_subtree as Hpruned; assert (Hx := Hpruned).
    apply subtree_extract with (xp := fsxp) in Hx.
    assert (Hdst := Hinterm); rewrite Hx in Hdst; clear Hx.
    destruct x; simpl in *; subst; try congruence; inv_option_eq.
    unfold tree_dir_names_pred in Hdst.
    destruct_lift Hdst.

    safecancel. eauto.

    (* grafting back *)
    destruct_branch.

    (* case 1: dst exists, try delete *)
    prestep.
    norml.
    unfold stars; simpl; clear_norm_goal; inv_option_eq.
    denote (tree_dir_names_pred' _ _) as Hx3.
    denote (_ |-> (_, _))%pred as Hx4.
    pose proof (ptsto_subtree_exists _ Hx3 Hx4) as Hx.
    destruct Hx; intuition.

    (* must unify [find_subtree] in [delete]'s precondition with
       the root tree node.  have to do this manually *)
    unfold rep; norm. cancel. intuition.
    pred_apply; norm. cancel. intuition.
    eassign (tree_prune v_1 l0 srcpath srcname (TreeDir dnum tree_elem)).
    pred_apply' Hinterm; cancel. eauto.

    (* now, get ready for link *)
    destruct_branch; [ | step ]. 
    prestep; norml; inv_option_eq; clear_norm_goal.
    denote mvtree as Hx. assert (Hdel := Hx).
    setoid_rewrite subtree_extract in Hx at 2.
    2: subst; eapply find_update_subtree; eauto.
    simpl in Hx; unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.
    eauto.

    eapply tree_pred_ino_goodSize; eauto.
    pred_apply' Hdel; cancel.

    safestep.
    or_l; cancel.
    or_r; cancel; eauto.
    eapply subtree_graft_absorb_delete; eauto.
    msalloc_eq.
    eapply rename_safe_dest_exists; eauto.

    (* case 1: in the new tree *)
    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    rewrite <- Hsafe1 by auto.

    denote (selN ilist _ _ = selN ilist' _ _) as Hi.
    eapply Hi; eauto.

    eapply prune_graft_preserves_inodes; eauto.

    (* case 2: out of the original tree *)
    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    rewrite <- Hsafe1 by auto.

    eapply H37; eauto.
    right.
    contradict H46.
    unfold tree_prune in *.
    eapply tree_inodes_incl_delete_from_dir in H46; eauto.
    simpl in *; intuition.

    cancel.

    (* dst is None *)
    safestep.
    safestep.
    eapply tree_pred_ino_goodSize; eauto.
    pred_apply' Hinterm; cancel.

    safestep.
    or_l; cancel.
    or_r; cancel; eauto.
    eapply subtree_graft_absorb; eauto.
    msalloc_eq.
    eapply rename_safe_dest_none; eauto.
    eapply notindomain_not_in_dirents; eauto.

    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    apply Hsafe1; auto.

    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    apply Hsafe1; auto.

    cancel.
    cancel; auto.

    cancel.
    cancel; auto.

    Unshelve.
    all: try exact addr; try exact addr_eq_dec; eauto.
  Qed.


  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] *
            exists srcnum srcents dstnum dstents subtree pruned renamed tree' ilist' frees',
            [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
            [[ find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
            [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = update_subtree pathname renamed tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees')%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum' def', inum' <> srcnum -> inum' <> dstnum ->
               selN ilist inum' def' = selN ilist' inum' def' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
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
    eapply dirlist_safe_subtree; eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.



End DIRTREE.
