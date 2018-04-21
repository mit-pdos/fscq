Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DirName.
Require Import DirTreeDef.
Require Import DirTreePath.
Require Import DirTreePred.
Require Import DirTreeRep.
Require Import SepAuto.

Import ListNotations.
Set Implicit Arguments.

  (**
   * Names in a directory are unique.
   *)

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

  Lemma rep_tree_names_distinct : forall tree F fsxp Ftop m ilist frees ms sm,
    (F * rep fsxp Ftop tree ilist frees ms sm)%pred m ->
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


  Theorem tree_names_distinct_head : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct (TreeDir n ([(a, d)])).
  Proof.
    intros.
    constructor.
    inversion H. 
    simpl in *.
    inversion H2.
    constructor; eauto.
    constructor.
    unfold not; intros Hin; inversion Hin.
    constructor.
  Qed.

  Theorem tree_names_distinct_child : forall n a d l,
    tree_names_distinct (TreeDir n ((a, d) :: l)) ->
    tree_names_distinct d.
  Proof.
    intros.
    inversion H; simpl in *.
    inversion H2; eauto.
  Qed.

  Hint Resolve tree_names_distinct_child.

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


  Hint Resolve tree_names_distinct_next.

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

 Lemma tree_names_distinct_head_name : forall inum name subtree rest,
    tree_names_distinct (TreeDir inum ((name, subtree) :: rest)) ->
    ~ In name (map fst rest).
  Proof.
    inversion 1.
    simpl in *.
    inversion H3; auto.
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


 Lemma tree_names_distinct_nodup : forall dnum ents,
    tree_names_distinct (TreeDir dnum ents) ->
    NoDup (map fst ents).
  Proof.
    intros; inversion H; auto.
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
    find_subtree p1 (update_subtree p2 subtree tree) = find_subtree p1 tree.
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

 Theorem update_subtree_tree_graft: 
    forall prefix name tree dnum tree_elem subtree subtree' F Ftop m fsxp ilist frees ms sm,
    (F * rep fsxp Ftop (update_subtree (prefix++[name]) subtree' 
                        (tree_graft dnum tree_elem prefix name subtree tree)) ilist frees ms sm)%pred m -> 
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


