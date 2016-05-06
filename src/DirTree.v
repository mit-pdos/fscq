Require Import DirName.
Require Import Balloc.
Require Import Prog.
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

  Definition dirtree_safe ilist1 free1 tree1 ilist2 free2 tree2 :=
    incl free2 free1 /\
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
    unfold incl; eauto.
  Qed.

  Theorem dirtree_safe_trans : forall i1 f1 t1 i2 t2 f2 i3 t3 f3,
    dirtree_safe i1 f1 t1 i2 f2 t2 ->
    dirtree_safe i2 f2 t2 i3 f3 t3 ->
    dirtree_safe i1 f1 t1 i3 f3 t3.
  Proof.
    unfold dirtree_safe; intros.
    intuition.
    eapply incl_tran; eauto.
    edestruct H3; eauto.
    - intuition; repeat deex.
      edestruct H2; eauto.
    - right.
      unfold BFILE.block_is_unused in *; eauto.
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

  Lemma update_subtree_notfound : forall name l fnlist subtree,
    ~ In name (map fst l) ->
    map (update_subtree_helper (update_subtree fnlist subtree) name) l = l.
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

  Theorem dirtree_update_safe : forall ilist_newest free_newest tree_newest pathname f tree fsxp F F0 ilist freeblocks v bn inum off m flag,
    find_subtree pathname tree_newest = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist_newest bn inum off ->
    dirtree_safe ilist (BFILE.pick_balloc freeblocks flag) tree ilist_newest free_newest tree_newest ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    exists tree',
    (F0 * rep fsxp F tree' ilist freeblocks)%pred (list2nmem (updN m bn v)) /\
    (tree' = tree \/ tree' = dirtree_update_inode tree inum off v).
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
      2: right; reflexivity.
      eapply dirtree_update_block; eauto.
    - (**
       * The block is now in the free list.
       *)
      eexists; split.
      2: left; reflexivity.
      eapply dirtree_update_free; eauto.
  Qed.

  (**
   * Helpers for proving [dirlist_safe] in postconditions.
   *)
  Theorem dirlist_safe_mkdir : forall ilist freeblocks ilist' freeblocks' flag
                                      dnum tree_elem name inum,
    BFILE.ilist_safe ilist  (BFILE.pick_balloc freeblocks  flag)
                     ilist' (BFILE.pick_balloc freeblocks' flag) ->
    dirtree_safe ilist  (BFILE.pick_balloc freeblocks  flag) (TreeDir dnum tree_elem)
                 ilist' (BFILE.pick_balloc freeblocks' flag) (TreeDir dnum ((name, TreeDir inum []) :: tree_elem)).
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

  Theorem dirlist_safe_mkfile : forall ilist freeblocks ilist' freeblocks' flag
                                      dnum tree_elem name inum,
    BFILE.ilist_safe ilist  (BFILE.pick_balloc freeblocks  flag)
                     ilist' (BFILE.pick_balloc freeblocks' flag) ->
    tree_names_distinct (TreeDir dnum ((name, TreeFile inum BFILE.bfile0) :: tree_elem)) ->
    dirtree_safe ilist  (BFILE.pick_balloc freeblocks  flag) (TreeDir dnum tree_elem)
                 ilist' (BFILE.pick_balloc freeblocks' flag) (TreeDir dnum ((name, TreeFile inum BFILE.bfile0) :: tree_elem)).
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    specialize (H2 _ _ _ H3); destruct H2.
    2: right; intuition.  (* Unused block. *)

    (**
     * Need to determine whether the new file's filename infact corresponds to [inum0].
     **)
    destruct pathname; simpl in *; try congruence.
    destruct (string_dec name s); subst; eauto.

    - (* Same filename; contradiction because the file is empty *)
      exfalso.

      (* Need a contradiction from
         [BFILE.block_belong_to_file ilist' bn inum0 off]
         and some premise saying the file is actually empty..
       *)
      admit.

    - (* Different filename *)
      left; intuition.
      exists (s :: pathname); eexists; simpl in *; eauto.
  Admitted.

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

  Definition namei T fsxp dnum (fnlist : list string) mscs rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, inum, isdir) <- ForEach fn fnrest fnlist
      Hashmap hm
      Ghost [ mbase m F Fm Ftop treetop bflist freeinodes freeinode_pred ilist freeblocks mscs0 ]
      Loopvar [ mscs inum isdir ]
      Continuation lrx
      Invariant
        LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
        exists tree,
        [[ (Fm * BFILE.rep bxp ixp bflist ilist freeblocks *
            IAlloc.rep ibxp freeinodes freeinode_pred)%pred
           (list2nmem m) ]] *
        [[ (Ftop * tree_pred ibxp treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ inum = dirtree_inum tree ]] *
        [[ isdir = dirtree_isdir tree ]] *
        [[ find_name fnlist treetop = find_name fnrest tree ]] *
        [[ isdir = true -> (exists Fsub, 
                   Fsub * tree_pred ibxp tree * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ MSAlloc mscs = MSAlloc mscs0 ]]
      OnCrash
        LOG.intact fsxp.(FSXPLog) F mbase hm
      Begin
        If (bool_dec isdir true) {
          let^ (mscs, r) <- SDIR.lookup lxp ixp inum fn mscs;
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
    {< F mbase m Fm Ftop tree ilist freeblocks,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) hm *
           [[ (Fm * rep fsxp Ftop tree ilist freeblocks)%pred (list2nmem m) ]] *
           [[ dnum = dirtree_inum tree ]] *
           [[ dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') hm' *
           [[ r = find_name fnlist tree ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} namei fsxp dnum fnlist mscs.
  Proof.
    unfold namei.
    step.
    step.

    (* isdir = true *)
    destruct tree0; simpl in *; subst; intuition.
    step.
    denote (tree_dir_names_pred) as Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.

    denote (dirlist_pred) as Hx; assert (Horig := Hx).
    destruct_branch.

    (* dslookup = Some _: extract subtree before [cancel] *)
    prestep.
    norml; unfold stars; simpl; clear_norm_goal; inv_option_eq.
    destruct a2.

    (* subtree is a directory *)
    rewrite tree_dir_extract_subdir in Hx by eauto; destruct_lift Hx.
    cancel. eassign (TreeDir a dummy6). auto. auto.
    erewrite <- find_name_subdir with (xp := fsxp); eauto.
    pred_apply' Horig; cancel.
    pred_apply; cancel.
    cancel.

    (* subtree is a file *)
    rewrite tree_dir_extract_file in Hx by eauto. destruct_lift Hx.
    cancel. eassign (TreeFile a dummy6). auto. auto.
    erewrite <- find_name_file with (xp := fsxp); eauto.
    pred_apply' Horig; cancel.
    pred_apply; cancel.

    (* dslookup = None *)
    step.
    erewrite <- find_name_none; eauto.

    (* rx : isdir = false *)
    step.
    denote (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct tree0; simpl in *; auto; congruence.

    (* rx : isdir = true *)
    step.
    denote (find_name) as Hx; rewrite Hx.
    unfold find_name; destruct tree0; simpl in *; subst; auto.

    Grab Existential Variables.
    all: eauto; try exact Mem.empty_mem; try exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (namei _ _ _ _) _) => apply namei_ok : prog.

  Definition mkfile T fsxp dnum name fms rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, oi) <- IAlloc.alloc lxp ibxp ms;
    let fms := BFILE.mk_memstate al ms in
    match oi with
    | None => rx ^(fms, None)
    | Some inum =>
      let^ (fms, ok) <- SDIR.link lxp bxp ixp dnum name inum false fms;
      If (bool_dec ok true) {
        fms <- BFILE.reset lxp bxp ixp inum fms;
        rx ^(fms, Some (inum : addr))
      } else {
        rx ^(fms, None)
      }
    end.


  Definition mkdir T fsxp dnum name fms rx : prog T :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, oi) <- IAlloc.alloc lxp ibxp ms;
    let fms := BFILE.mk_memstate al ms in
    match oi with
    | None => rx ^(fms, None)
    | Some inum =>
      let^ (fms, ok) <- SDIR.link lxp bxp ixp dnum name inum true fms;
      If (bool_dec ok true) {
        fms <- BFILE.reset lxp bxp ixp inum fms;
        rx ^(fms, Some (inum : addr))
      } else {
        rx ^(fms, None)
      }
    end.

  Theorem mkdir_ok' : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (TreeDir dnum 
                     ((name, TreeDir inum nil) :: tree_elem)))%pred (list2nmem m') ]])
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
    admit. (* goodSize, probably should use an IAlloc equivalent of [BALLOC.bn_valid_goodSize] *)
    step.
    step.
    step.

    denote dirlist_pred as Hx; denote (pimpl dummy1) as Hy;
    rewrite Hy in Hx; destruct_lift Hx.
    step.
    step.
    or_r; cancel.

    unfold tree_dir_names_pred at 1. cancel; eauto.
    unfold tree_dir_names_pred; cancel.
    apply SDIR.bfile0_empty.
    apply emp_empty_mem.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    step.
    Unshelve.
    all: try eauto; exact emp; try exact nil; try exact empty_mem; try exact BFILE.bfile0.
  Admitted.


  Theorem mkdir_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = None ]] \/
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                      ((name, TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2nmem m') ]])
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
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, oi) <- SDIR.lookup lxp ixp dnum name mscs;
    match oi with
    | None => rx ^(mscs, false)
    | Some (inum, isdir) =>
      mscs <- IfRx irx (bool_dec isdir false) {
        irx mscs
      } else {
        let^ (mscs, l) <- SDIR.readdir lxp ixp inum mscs;
        match l with
        | nil => irx mscs
        | _ => rx ^(mscs, false)
        end
      };
      mscs <- BFILE.reset lxp bxp ixp inum mscs;
      let^ (mscs, ok) <- SDIR.unlink lxp ixp dnum name mscs;
      If (bool_dec ok true) {
        mscs <- IAlloc.free lxp ibxp inum mscs;
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


  Theorem delete_ok' : forall fsxp dnum name mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = false ]] \/
            [[ r = true  ]] *
            [[ (Fm * rep fsxp Ftop (delete_from_dir name tree))%pred (list2nmem m') ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} delete fsxp dnum name mscs.
  Proof.
    unfold delete, rep.
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.
    unfold SDIR.rep_macro.
    cancel. eauto.

    step.
    step.

    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := a) in Hx; eauto.
    destruct_lift Hx.
    destruct dummy4; simpl in *; try congruence; subst.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.

    step.
    step.
    step.
    or_r; safecancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    rewrite dir_names_delete; eauto.
    rewrite dirlist_delete_file.
    eassign n; cancel.
    eauto.
    denote ( _ |-> (_, false))%pred as Hc.
    pred_apply' Hc; cancel.

    step.

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

    or_r; cancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    denote (tree_dir_names_pred' _ _) as Hz.
    erewrite (@dlist_is_nil _ _ _ _ _ Hz); eauto.
    denote (tree_dir_names_pred' tree_elem _) as Hy.
    erewrite (@dir_names_delete _ _ _ _ _ _ Hy); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    cancel.

    step.
    cancel; auto.
    cancel; auto.

    Unshelve.
    all: try exact addr_eq_dec.  7: eauto. all: eauto.
  Qed.

  Theorem delete_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = false ]] \/
            [[ r = true ]] * exists tree',
            [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2nmem m') ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
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
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, osrcdir) <- namei fsxp dnum srcpath mscs;
    match osrcdir with
    | None => rx ^(mscs, false)
    | Some (_, false) => rx ^(mscs, false)
    | Some (dsrc, true) =>
      let^ (mscs, osrc) <- SDIR.lookup lxp ixp dsrc srcname mscs;
      match osrc with
      | None => rx ^(mscs, false)
      | Some (inum, inum_isdir) =>
        (* XXX need to look up dst_inum first.. *)
        mscs <- BFILE.reset lxp bxp ixp dst_inum mscs;

        let^ (mscs, _) <- SDIR.unlink lxp ixp dsrc srcname mscs;
        let^ (mscs, odstdir) <- namei fsxp dnum dstpath mscs;
        match odstdir with
        | None => rx ^(mscs, false)
        | Some (_, false) => rx ^(mscs, false)
        | Some (ddst, true) =>
          let^ (mscs, odst) <- SDIR.lookup lxp ixp ddst dstname mscs;
          match odst with
          | None =>
            let^ (mscs, ok) <- SDIR.link lxp bxp ixp ddst dstname inum inum_isdir mscs;
            rx ^(mscs, ok)
          | Some _ =>
            let^ (mscs, ok) <- delete fsxp ddst dstname mscs;
            If (bool_dec ok true) {
              let^ (mscs, ok) <- SDIR.link lxp bxp ixp ddst dstname inum inum_isdir mscs;
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


  Theorem rename_ok' : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = false ]] \/
            [[ r = true  ]] * exists snum sents dnum dents subtree pruned tree',
            [[ find_subtree srcpath tree = Some (TreeDir snum sents) ]] *
            [[ find_dirlist srcname sents = Some subtree ]] *
            [[ pruned = tree_prune snum sents srcpath srcname tree ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dnum dents) ]] *
            [[ tree' = tree_graft dnum dents dstpath dstname subtree pruned ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2nmem m') ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rep.

    (* namei srcpath, isolate root tree file before cancel *)
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.
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
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.

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
    denote (n |-> _)%pred as Hsub.

    cancel.
    unfold SDIR.rep_macro.
    cancel; eauto.

    (* unlink src *)
    step.

    (* namei for dstpath, find out pruning subtree before step *)
    denote (tree_dir_names_pred' l _) as Hx1.
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
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.

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

    cancel.
    unfold SDIR.rep_macro; cancel. eauto.

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
    eassign (tree_prune n l srcpath srcname (TreeDir dnum tree_elem)).
    pred_apply' Hinterm; cancel. eauto.

    (* now, get ready for link *)
    step; try solve [ step ].
    denote mvtree as Hx. assert (Hdel := Hx).
    setoid_rewrite subtree_extract in Hx at 2.
    2: subst; eapply find_update_subtree; eauto.
    simpl in Hx; unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.

    admit. (* goodSize *)

    safestep.
    or_l; cancel.
    or_r; cancel; eauto.
    eapply subtree_graft_absorb_delete; eauto.

    cancel.

    (* dst is None *)
    safestep.
    admit. (* goodSize *)

    safestep.
    or_l; cancel.
    or_r; cancel; eauto.
    eapply subtree_graft_absorb; eauto.

    cancel.
    cancel; auto.

    cancel.
    cancel; auto.

    Unshelve.
    all: try exact addr; try exact addr_eq_dec; eauto.
  Admitted.


  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = false ]] \/
            [[ r = true  ]] * exists srcnum srcents dstnum dstents subtree pruned renamed tree',
            [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
            [[ find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
            [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = update_subtree pathname renamed tree ]] *
            [[ (Fm * rep fsxp Ftop tree')%pred (list2nmem m') ]])
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
  Qed.

  Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.

  Definition read T fsxp inum off mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.read (FSXPLog fsxp) (FSXPInode fsxp) inum off mscs;
    rx ^(mscs, v).

  Definition write T fsxp inum off v mscs rx : prog T :=
    mscs <- BFILE.write (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    rx mscs.

  Definition dwrite T fsxp inum off v mscs rx : prog T :=
    mscs <- BFILE.dwrite (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    rx mscs.

  Definition datasync T fsxp inum mscs rx : prog T :=
    mscs <- BFILE.datasync (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx mscs.

  Definition sync T fsxp mscs rx : prog T :=
    mscs <- BFILE.sync (FSXPLog fsxp) (FSXPInode fsxp) mscs;
    rx mscs.

  Definition truncate T fsxp inum nblocks mscs rx : prog T :=
    let^ (mscs, ok) <- BFILE.truncate (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                     inum nblocks mscs;
    rx ^(mscs, ok).

  Definition getlen T fsxp inum mscs rx : prog T :=
    let^ (mscs, len) <- BFILE.getlen (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, len).

  Definition getattr T fsxp inum mscs rx : prog T :=
    let^ (mscs, attr) <- BFILE.getattrs (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, attr).

  Definition setattr T fsxp inum attr mscs rx : prog T :=
    mscs <- BFILE.setattrs (FSXPLog fsxp) (FSXPInode fsxp) inum attr mscs;
    rx mscs.

  Definition updattr T fsxp inum kv mscs rx : prog T :=
    mscs <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum kv mscs;
    rx mscs.

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
    {< F mbase m pathname Fm Ftop tree f B v,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST:hm' RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm' *
           [[ r = fst v ]]
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
    {< F ds pathname Fm Ftop tree f B v0,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds ds!!) mscs hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (B * off |-> v0) ]]]
    POST:hm' RET:mscs
           exists d tree' f',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn (d, nil) d) mscs hm' *
           [[[ d ::: Fm * rep fsxp Ftop tree' ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[[ (BFILE.BFData f') ::: (B * off |-> (v, vsmerge v0)) ]]] *
           [[ f' = BFILE.mk_bfile (updN (BFILE.BFData f) off (v, vsmerge v0)) (BFILE.BFAttr f) ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm' \/
           exists d tree' f', LOG.intact fsxp.(FSXPLog) F (d, nil) hm' *
           [[[ d ::: Fm * rep fsxp Ftop tree' ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[[ (BFILE.BFData f') ::: (B * off |-> (v, vsmerge v0)) ]]] *
           [[ f' = BFILE.mk_bfile (updN (BFILE.BFData f) off (v, vsmerge v0)) (BFILE.BFAttr f) ]]
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
    cancel.
    eapply pimpl_trans.
    2: eapply H1.
    cancel.
    eapply pimpl_trans.
    eapply H.
    apply PredCrash.crash_xform_pimpl.
    cancel.
    or_r.
    cancel.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.
    simpl.
    eauto.
  Qed.

 Theorem datasync_ok : forall fsxp inum mscs,
    {< F ds pathname Fm Ftop tree f,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds ds!!) mscs hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:mscs
           exists d tree',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn (d,nil) d) mscs hm' *
           [[[ d ::: Fm * rep fsxp Ftop tree' ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum (BFILE.synced_file f)) tree ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
    >} datasync fsxp inum mscs.
  Proof.
    unfold datasync, rep.
    safestep.
    rewrite subtree_extract; eauto. cancel.
    step.
    rewrite <- subtree_absorb; eauto. cancel.
    eapply find_subtree_inum_valid; eauto.
  Qed.

  Theorem sync_ok : forall fsxp mscs,
    {< F ds Fm Ftop tree,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) mscs hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ]]]
    POST:hm' RET:mscs
           LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn (ds!!, nil)) mscs hm'
     XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
     >} sync fsxp mscs.
  Proof.
    unfold sync, rep.
    hoare.
  Qed.

  Theorem truncate_ok : forall fsxp inum nblocks mscs,
    {< F ds d pathname Fm Ftop tree f,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) mscs hm *
           [[[ d ::: Fm * rep fsxp Ftop tree ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs, ok)
           exists d',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d') mscs hm' *
          ([[ ok = false ]] \/
           [[ ok = true ]] *
           exists tree' f',
           [[[ d' ::: Fm * rep fsxp Ftop tree' ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) nblocks ($0, nil)) (BFILE.BFAttr f) ]])
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
  Qed.

  Theorem getlen_ok : forall fsxp inum mscs,
    {< F mbase m pathname Fm Ftop tree f,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm' *
           [[ r = length (BFILE.BFData f) ]]
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
    {< F ds d pathname Fm Ftop tree f,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) mscs hm *
           [[[ d ::: Fm * rep fsxp Ftop tree ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs,r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) mscs hm' *
           [[ r = BFILE.BFAttr f ]]
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
    {< F mbase m pathname Fm Ftop tree f,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:mscs
           exists m' tree' f',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           [[ (Fm * rep fsxp Ftop tree')%pred (list2nmem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]]
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
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (datasync _ _ _) _) => apply datasync_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_}} progseq (truncate _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} progseq (getlen _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} progseq (getattr _ _ _) _) => apply getattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (setattr _ _ _ _) _) => apply setattr_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


  Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase m pathname Fm Ftop tree tree_elem,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) mscs hm *
           [[ (Fm * rep fsxp Ftop tree)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,r)
           (* We always modify the memory, because we might allocate the file,
            * but then fail to link it into the directory..  When we return
            * None, the overall transaction should be aborted.
            *)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') mscs hm' *
           ([[ r = None ]] \/
            exists inum, [[ r = Some inum ]] *
            [[ (Fm * rep fsxp Ftop (tree_graft dnum tree_elem pathname name 
                         (TreeFile inum BFILE.bfile0) tree))%pred (list2nmem m') ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase hm'
    >} mkfile fsxp dnum name mscs.
  Proof.
    unfold mkfile, rep.
    step. 
    subst; simpl in *.

    rewrite subtree_extract in H6; eauto.
    simpl in *.

    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    step.
    unfold SDIR.rep_macro.
    admit. (* goodSize *)

    step.
    step.
    step.

    denote dirlist_pred as Hx; denote (pimpl dummy1) as Hy.
    rewrite Hy in Hx; destruct_lift Hx.
    step.
    step.

    or_r; cancel.
    rewrite <- subtree_graft_absorb; eauto. cancel.
    step.

    Unshelve.
    all: eauto.
  Admitted.

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

  Theorem find_subtree_tree_graft_ne : forall prefix name name' tree dnum tree_elem subtree,
    name <> name' ->
    find_subtree prefix tree = Some (TreeDir dnum tree_elem) ->
    find_subtree (prefix++[name]) (tree_graft dnum tree_elem prefix name' subtree tree) =
      find_subtree (prefix++[name]) tree.
  Proof.
    admit.
  Admitted.

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

  Lemma map_update_subtree_helper_notfound : forall f name l,
    ~ In name (map fst l) ->
    map (update_subtree_helper f name) l = l.
  Proof.
   induction l; simpl; intros; auto.
    rewrite IHl by intuition.
    unfold update_subtree_helper.
    destruct a.
    destruct (string_dec s name); subst; simpl; auto.
    firstorder.
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
      rewrite map_update_subtree_helper_notfound.
      reflexivity.
      erewrite <- tree_names_distinct_head_name'.
      eapply tree_names_distinct_head_name.
      simpl in H.
      destruct (string_dec name name); try congruence.
      apply H.
      destruct (string_dec s name); try congruence.
      simpl in H.
      apply tree_name_distinct_rest in H.
      Check IHtree_elem.
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


  Theorem update_subtree_tree_graft: forall prefix name tree dnum tree_elem subtree subtree' F Ftop m fsxp,
    (F * rep fsxp Ftop (update_subtree (prefix++[name]) subtree' (tree_graft dnum tree_elem prefix name subtree tree)))%pred m -> 
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


End DIRTREE.
