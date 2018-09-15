Require Import Bool.
Require Import Word.
Require Import Bytes Rec.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import BFile Inode.
Require Import DirTreePath.

Import ListNotations.

Set Implicit Arguments.

(** 
 * The base definitions to model directories in specifications 
 *)

  Definition attrtype := INODE.iattrin.
  Definition datatype := valuset.

  Record dirfile := mk_dirfile {
    DFData : list datatype;
    DFAttr : attrtype;
    DFOwner: tag
  }.

  Definition dirfile0 := mk_dirfile nil INODE.iattr0 Public.

  Inductive dirtree :=
  | TreeFile : addr -> dirfile -> dirtree
  | TreeDir  : addr -> list (string * dirtree) -> dirtree.

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
    | TreeDir  _ _ => dirfile0
    end.

  Definition synced_dirfile f := mk_dirfile (Array.synced_list (map fst (DFData f))) (DFAttr f) (DFOwner f).

  Definition dirfile_to_bfile f c := BFILE.mk_bfile (DFData f) (DFAttr f) (DFOwner f) c.


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


  Fixpoint find_dirlist name (l : list (string * dirtree)) :=
    match l with
    | nil => None
    | (n, sub) :: rest =>
        if string_dec n name then Some sub else find_dirlist name rest
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

  Lemma update_subtree_notfound : forall name l f,
    ~ In name (map fst l) ->
    map (update_subtree_helper f name) l = l.
  Proof.
    induction l; simpl; intros; eauto.
    destruct a; simpl in *.
    destruct (string_dec s name); intuition.
    rewrite IHl; eauto.
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


  Lemma find_subtree_nil: forall pn n,
    pn <> nil ->
    find_subtree pn (TreeDir n []) = None.
  Proof.
    intros.
    induction pn; simpl in *; subst; try congruence.
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

  Lemma find_subtree_update_subtree_oob_general : forall base pn tree subtree subtree',
    (~ exists suffix, pn = base ++ suffix) ->
    find_subtree pn (update_subtree base subtree tree) = Some subtree' ->
    exists subtree'',
      find_subtree pn tree = Some subtree'' /\
      dirtree_inum subtree'' = dirtree_inum subtree' /\
      dirtree_isdir subtree'' = dirtree_isdir subtree'.
  Proof.
    induction base; simpl; intros.
    contradict H; eauto.

    destruct pn; simpl in *.
    - eexists; intuition eauto.
      destruct tree; destruct subtree'; simpl in *; try congruence.
      destruct tree; destruct subtree'; simpl in *; try congruence.

    - destruct tree; simpl in *; try congruence.
      induction l; simpl in  *; try congruence.

      destruct a0; simpl in *.
      destruct (string_dec s0 a); destruct (string_dec s0 s); subst; simpl in *.
      + destruct (string_dec s s); try congruence.
        eapply IHbase; eauto.
        intro H'. apply H. deex. eauto.
      + destruct (string_dec a s); try congruence. eauto.
      + destruct (string_dec s s); try congruence. eauto.
      + destruct (string_dec s0 s); try congruence. eauto.
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


  (**
   * Helpers for higher levels that need to reason about updated trees.
   *)


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

  Lemma find_name_exists : forall path tree inum isdir,
    find_name path tree = Some (inum, isdir)
    -> exists subtree, find_subtree path tree = Some subtree
        /\ dirtree_inum subtree = inum /\ dirtree_isdir subtree = isdir.
  Proof.
    unfold find_name; intros.
    destruct (find_subtree path tree); try destruct d;
      inversion H; subst; eauto.
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

  Lemma update_subtree_preserve_name : forall l fnlist s subtree,
    map fst (map (update_subtree_helper (update_subtree fnlist subtree) s) l) = map fst l.
  Proof.
    induction l; simpl; intros; auto.
    unfold update_subtree_helper at 1.
    destruct a. destruct (string_dec s0 s); subst; auto.
    rewrite IHl. f_equal.
    rewrite IHl; auto.
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


  Lemma find_subtree_head_pn: forall pn s n d l,
    pathname_prefix [s] pn ->
    find_subtree pn (TreeDir n ((s, d) :: l)) =
    find_subtree pn (TreeDir n [(s, d)]).
  Proof.
    intros.
    destruct pn.
    - unfold pathname_prefix in H.
      deex. exfalso. simpl in H. try congruence.
    - unfold pathname_prefix in H.
      deex.
      inversion H; subst.
      simpl.
      destruct (string_dec s0 s0); try congruence.
  Qed.

  Lemma find_subtree_head_ne_pn: forall pn s n d l,
    pn <> [] ->
    ~pathname_prefix [s] pn ->
    find_subtree pn (TreeDir n ((s, d) :: l)) =
    find_subtree pn (TreeDir n l).
  Proof.
    intros.
    destruct pn; try congruence.
    unfold pathname_prefix in H0.
    destruct (string_dec s s0); subst; try congruence.
    - exfalso. apply H0. exists pn. rewrite cons_app with (l := pn).
      reflexivity.
    - simpl. destruct (string_dec s s0); try congruence.
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

  Lemma find_subtree_file_dir_exfalso: forall pn n f d e,
    find_subtree pn (TreeFile n f) = Some (TreeDir d e) ->
    False.
  Proof.
    intros.
    destruct pn.
    simpl in *; try congruence.
    rewrite find_subtree_file_none in H.
    try congruence.
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
    fold_right (find_subtree_helper f name) (@None T) tree_elem = Some elem
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


