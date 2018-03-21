Require Import Bool.
Require Import Word.
Require Import PermBalloc.
Require Import PermBFile Bytes Rec PermInode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import PermAsyncDisk.
Require Import PermDirCache.
Require Import DirTreeDef.
Require Import FSLayout.
Require Import PermGenSepN.
Require Import PermSepAuto.
Require Import DirTreePred.


Import ListNotations.

Set Implicit Arguments.

  (**
   *
   * The dirtree representation invariant 
   *
   * [F] represents the other parts of the file system above [tree],
   * in cases where [tree] is a subdirectory somewhere in the tree.
   *)

Fixpoint inode_tags_public flist tree :=
  match tree with
  | TreeDir inum tdl =>
    ([[ BFILE.BFOwner (selN flist inum BFILE.bfile0) = Public ]] *
    dirlist_pred (inode_tags_public flist) tdl)%pred
  | _ => [[ True ]]%pred
  end.

  Definition rep fsxp F tree ilist frees ms sm :=
    (exists bflist freeinodes freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) sm fsxp.(FSXPInode) bflist ilist frees
        (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) *
     IAlloc.rep BFILE.freepred fsxp freeinodes freeinode_pred (IAlloc.Alloc.mk_memstate (BFILE.MSLL ms) (BFILE.MSIAllocC ms)) *
     [[ (F * tree_pred fsxp tree * freeinode_pred * inode_tags_public bflist tree)%pred (list2nmem bflist) ]]
    )%pred.

  Theorem rep_length : forall fsxp F tree ilist frees ms sm,
    rep fsxp F tree ilist frees ms sm =p=>
    (rep fsxp F tree ilist frees ms sm *
     [[ length ilist = ((INODE.IRecSig.RALen (FSXPInode fsxp)) * INODE.IRecSig.items_per_val)%nat ]])%pred.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite BFILE.rep_length_pimpl at 1.
    cancel.
  Qed.

  Theorem dirtree_update_free : forall tree fsxp F F0 ilist freeblocks ms sm v bn m flag,
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    BFILE.block_is_unused (BFILE.pick_balloc freeblocks flag) bn ->
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem (updN m bn v)).
  Proof.
    intros.
    unfold rep in *.
    destruct_lift H.
    eapply pimpl_apply; [ | eapply BFILE.rep_safe_unused; eauto; pred_apply; cancel ].
    2: eassign (IAlloc.rep BFILE.freepred fsxp dummy0 dummy1
               {|
                 IAlloc.Alloc.MSLog := SDIR.MSLL ms;
                 IAlloc.Alloc.MSCache := SDIR.MSIAllocC ms |} * F0)%pred; cancel.
    cancel.
  Qed.

  Theorem dirtree_rep_used_block_eq : forall pathname F0 tree fsxp F ilist freeblocks ms inum off bn m sm f,
    (F0 * rep fsxp F tree ilist freeblocks ms sm)%pred (list2nmem m) ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    selN (DFData f) off valuset0 = selN m bn valuset0.
  Proof.
    intros.

    unfold rep in *.
    destruct_lift H.

    erewrite <- BFILE.rep_used_block_eq with (m := m).
    2:  eassign (IAlloc.rep BFILE.freepred fsxp dummy0 dummy1
               {|
                 IAlloc.Alloc.MSLog := SDIR.MSLL ms;
                 IAlloc.Alloc.MSCache := SDIR.MSIAllocC ms |} * F0)%pred; pred_apply; cancel.
    2: eauto.
    f_equal.
    f_equal.

    rewrite subtree_extract in * by eassumption.
    simpl in *.
    apply eq_sym.
    eapply BFILE.rep_used_block_eq_Some_helper.

    destruct_lifts.
    assert (inum < Datatypes.length dummy) as Hlt by ( eapply list2nmem_inbound; pred_apply; cancel ).

    pose proof (list2nmem_sel_inb dummy BFILE.bfile0 Hlt) as Hx.
    eapply pimpl_trans in H2; [ | apply pimpl_refl | ].
    eapply ptsto_valid in H2.
    rewrite Hx in H2; clear Hx.
    2: cancel.
    inversion H2; clear H2.
    rewrite H4; simpl.
    auto.    
  Qed.

  Lemma tree_pred_ino_goodSize : forall F Fm xp tree m d frees prd allocc,
    (Fm * (IAlloc.rep BFILE.freepred xp frees prd allocc))%pred m ->
    (F * tree_pred xp tree)%pred d ->
    goodSize addrlen (dirtree_inum tree).
  Proof.
    induction tree using dirtree_ind2; simpl; intros.
    destruct_lift H0.
    eapply IAlloc.ino_valid_goodSize; eauto.
    unfold tree_dir_names_pred in H1; destruct_lift H1.
    eapply IAlloc.ino_valid_goodSize; eauto.
  Qed.

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

  Theorem mscs_same_except_log_rep' : forall mscs1 mscs2 fsxp F tree ilist frees sm,
    BFILE.mscs_same_except_log mscs1 mscs2 ->
    rep fsxp F tree ilist frees mscs1 sm =p=> rep fsxp F tree ilist frees mscs2 sm.
  Proof.
    unfold BFILE.mscs_same_except_log; unfold rep; intros.
    intuition msalloc_eq.
    apply pimpl_refl.
  Qed.

  Theorem mscs_same_except_log_rep : forall mscs1 mscs2 fsxp F tree ilist frees sm,
    BFILE.mscs_same_except_log mscs1 mscs2 ->
    rep fsxp F tree ilist frees mscs1 sm <=p=> rep fsxp F tree ilist frees mscs2 sm.
  Proof.
    split; eapply mscs_same_except_log_rep'; eauto.
    unfold BFILE.mscs_same_except_log in *; intuition eauto.
  Qed.

    Lemma find_subtree_helper_in:
      forall l a x,
        fold_right (find_subtree_helper (fun tree : dirtree => Some tree) a) None l = Some x ->
        exists l1 l2, l = l1 ++ (a, x)::l2.
    Proof.
      induction l; simpl; intros; try congruence.
      unfold find_subtree_helper at 1 in H.
      destruct a.
      destruct (string_dec s a0); cleanup.
      exists nil, l. simpl; auto.
      apply IHl in H; cleanup.
      exists ((s, d) :: x0), x1; eauto.
    Qed.

    
    Lemma treelist_inode_public:
      forall path l l0 n n0 flist F m,
        find_subtree path (TreeDir n l) = Some (TreeDir n0 l0) ->
        (F ✶ dirlist_pred (inode_tags_public flist) l)%pred m ->
        BFILE.BFOwner (selN flist n BFILE.bfile0) = Public ->
        BFILE.BFOwner (selN flist n0 BFILE.bfile0) = Public.
    Proof.
      induction path; intros.
      simpl in *; cleanup; auto.
      destruct l. simpl in *; try congruence.
      apply lookup_firstelem_path in H.
      cleanup.
      destruct p; simpl in *.
      destruct (string_dec s a); subst.
      cleanup.
      destruct x; simpl in *.
      destruct path; simpl in *; congruence.
      destruct_lift H0.
      eapply IHpath; eauto.
      pred_apply' H; cancel.
      apply find_subtree_helper_in in H; cleanup.
      rewrite dirlist_pred_split in H0; simpl in *.
      destruct x; simpl in *.
      destruct path; simpl in *; congruence.
      destruct_lift H0.
      eapply IHpath; eauto.
      pred_apply' H; cancel.
    Qed.

    Lemma treedir_inode_public:
      forall tree path n l m flist F,
        (F * inode_tags_public flist tree)%pred m ->
        find_subtree path tree = Some (TreeDir n l) ->
        BFILE.BFOwner (selN flist n BFILE.bfile0) = Public.
    Proof.
      induction tree; intros; simpl in *.
      destruct path; inversion H0; congruence.
      destruct_lift H.
      eapply treelist_inode_public; eauto.
    Qed.
(*
    Lemma inode_tags_public_ilist_trans:
    forall d inum flist flist',
      BFILE.BFOwner (selN flist' inum BFILE.bfile0) = Public ->
      BFILE.treeseq_ilist_safe inum ilist ilist' ->
      inode_tags_public flist d
      =p=> inode_tags_public flist' d.
  Proof.
    intros.
    generalize d; apply dirtree_ind2; intros.
    simpl; cancel.
    simpl; cancel.
    generalize dependent tree_ents.
    induction tree_ents.
    intros; simpl; cancel.
    intros; simpl.
    inversion H1; subst.
    destruct a; simpl in *.
    rewrite H5, IHtree_ents; auto.
    destruct(Nat.eq_dec inum inum0); subst; eauto.
    unfold BFILE.treeseq_ilist_safe in *; cleanup.
    rewrite <- H2; auto.
  Qed.

  Lemma dirlist_pred_inode_tags_public_ilist_trans:
    forall tree_elem ilist ilist' dnum,
      INODE.IOwner (selN ilist' dnum INODE.inode0) = Public ->
      BFILE.treeseq_ilist_safe dnum ilist ilist' ->
      dirlist_pred (inode_tags_public ilist) tree_elem
      =p=> dirlist_pred (inode_tags_public ilist') tree_elem.
  Proof.
    induction tree_elem; simpl; intros.
    cancel.
    destruct a.
    erewrite inode_tags_public_ilist_trans, IHtree_elem; eauto.
  Qed.

  Lemma bfile0_tag_public:
      forall F Fm bxps sm ixp flist ilist frees cms mscache icache dblocks n m,
      (Fm * BFILE.rep bxps sm ixp flist
          ilist frees cms mscache icache dblocks)%pred (list2nmem m) ->
      (F * n|-> BFILE.bfile0)%pred (list2nmem flist) ->
      INODE.IOwner (selN ilist n INODE.inode0) = Public.
    Proof.
      unfold BFILE.rep, BFILE.bfile0, BFILE.attr0, INODE.iattr0; intros.
      destruct_lift H.
      rewrite listmatch_extract with (i:=n) in H.
      unfold BFILE.file_match at 2 in H.
      destruct_lift H.
      erewrite <- list2nmem_sel with (l:=flist) in *; eauto; simpl in *.
      unfold INODE.IOwner, INODE.AOwner.
      rewrite <- H13; simpl.
      setoid_rewrite <- encode_public.
      apply encode_decode.
      eapply list2nmem_inbound; eauto.
      Unshelve.
      exact BFILE.bfile0.
    Qed. 

    Lemma inode_tags_public_pimpl_emp:
      forall tree ilist,
        inode_tags_public ilist tree
        =p=> emp.
    Proof.
      intros. generalize tree. apply dirtree_ind2; intros.
      cancel.
      generalize dependent tree_ents.
      induction tree_ents; simpl; intros.
      cancel.
      inversion H; subst.
      destruct a; simpl in *.
      rewrite H2.
      rewrite <- emp_star.
      specialize (IHtree_ents H3); auto.
    Qed.

    Lemma dirlist_pred_inode_tags_public_pimpl_emp:
      forall elem ilist,
        dirlist_pred (inode_tags_public ilist) elem =p=> emp.
    Proof.
      intros.
      pose proof (inode_tags_public_pimpl_emp (TreeDir (length ilist) elem) ilist).
      simpl in H.
      rewrite selN_oob in H; auto.
      intros m Hm; apply H; pred_apply; cancel.
      unfold INODE.IOwner, INODE.inode0,
      INODE.AOwner, INODE.iattr0.
      simpl.
      setoid_rewrite <- encode_public; apply encode_decode.
    Qed.
    
    Lemma inode_tags_public_subtree':
      forall pathname tree d ilist,
      find_subtree pathname tree = Some d ->
      inode_tags_public ilist tree
        =p=> inode_tags_public ilist d.
    Proof.
      induction pathname; intros.
      - simpl in *; inversion H; cancel.
      - replace (a::pathname) with ([a]++pathname) in H.
        apply find_subtree_app' in H.
        cleanup.
        simpl in *.
        destruct tree; try congruence.
        simpl.
        apply find_subtree_helper_in in H. cleanup.
        rewrite dirlist_pred_split.
        simpl.
        erewrite IHpathname; eauto.
        repeat rewrite dirlist_pred_inode_tags_public_pimpl_emp; cancel.
        simpl; auto.
    Qed.

    Lemma sep_reorg_helper: forall AT AEQ V (a b c: @pred AT AEQ V), a * (b * c) =p=> b * (a * c).
    Proof. intros; cancel. Qed.

     Lemma inode_tags_public_double:
      forall tree ilist,
      inode_tags_public ilist tree
        =p=> inode_tags_public ilist tree * inode_tags_public ilist tree.
     Proof.
       intros. generalize tree; apply dirtree_ind2; intros.
       simpl; cancel.
       generalize dependent tree_ents.
       induction tree_ents; intros.
       simpl; cancel.
       destruct a; simpl in *.
       inversion H; subst.
       rewrite sep_reorg_helper at 1.
       rewrite H2 at 1.
       rewrite IHtree_ents at 1; auto.
       cancel.
     Qed.
       

    Lemma inode_tags_public_subtree:
      forall pathname tree d ilist,
      find_subtree pathname tree = Some d ->
      inode_tags_public ilist tree
        =p=> inode_tags_public ilist tree * inode_tags_public ilist d.
    Proof.
      intros.
      rewrite inode_tags_public_double at 1; cancel.
      eapply inode_tags_public_subtree'; eauto.
    Qed.



    Lemma inode_tags_public_link:
      forall pathname tree dnum tree_elem ilist n name,
        find_subtree pathname tree = Some (TreeDir dnum tree_elem) ->
        INODE.IOwner (selN ilist n INODE.inode0) = Public ->
        tree_names_distinct tree ->
      inode_tags_public ilist tree
      =p=> inode_tags_public ilist
          (update_subtree pathname (TreeDir dnum ((name, TreeDir n []) :: tree_elem)) tree).
    Proof.
      induction pathname; intros.
      inversion H; simpl; cancel.

      replace (a::pathname) with ([a]++pathname) in H; [|simpl; auto].
      apply find_subtree_app' in H.
      cleanup.
      simpl in *.
      destruct tree; try congruence.
      simpl.
      apply find_subtree_helper_in in H. cleanup.
      rewrite map_app; simpl.
      destruct (string_dec a a); try congruence.
      repeat rewrite dirlist_pred_split.
      simpl.
      inversion H1; subst.
      rewrite map_app in *; simpl in *.
      erewrite IHpathname; eauto.
      repeat rewrite update_subtree_notfound. cancel.
      apply NoDup_app_r in H5; inversion H5; auto.
      apply NoDup_app_comm in H5; inversion H5; subst.
      intros Hi; apply H6; apply in_or_app; eauto.
      apply forall_app_l in H4; inversion H4; auto.
    Qed.

    Lemma inode_tags_public_update:
      forall pathname tree subtree ilist,
        inode_tags_public ilist tree * inode_tags_public ilist subtree
        =p=> inode_tags_public ilist (update_subtree pathname subtree tree).
    Proof.
      induction pathname; intros.
      simpl in *; subst; cancel.
      apply inode_tags_public_pimpl_emp.
      destruct tree. simpl; cancel.
      apply inode_tags_public_pimpl_emp.
      simpl; cancel.
      induction l.
      simpl; cancel; apply inode_tags_public_pimpl_emp.
      destruct a0.      
      simpl in *; destruct (string_dec s a); subst.
      rewrite inode_tags_public_double with (tree:=subtree).
      rewrite <- IHpathname, <- IHl; cancel.
      rewrite <- IHl; cancel.
    Qed.

    Lemma inode_tags_public_ilist_trans_not_in:
      forall inum ilist ilist',
      BFILE.treeseq_ilist_safe inum ilist ilist' ->
      forall d, [[ ~In inum (tree_inodes d) ]] * inode_tags_public ilist d
      =p=> inode_tags_public ilist' d.
    Proof.
      unfold BFILE.treeseq_ilist_safe; intros.
      generalize d; apply dirtree_ind2; intros.
      cancel.
      cleanup.
      norml.
      simpl; rewrite <- H1.
      cancel.
      generalize dependent inum0.
      generalize dependent tree_ents. induction tree_ents; intros.
      cancel.
      simpl in *.
      destruct a.
      inversion H0; subst.
      rewrite <- H7, IHtree_ents.
      cancel.
      all: eauto; intuition.
    Qed.

    Lemma dirlist_pred_inode_tags_public_ilist_trans_not_in:
      forall elems dnum inum ilist ilist',
      BFILE.treeseq_ilist_safe inum ilist ilist' ->
      ~In inum (tree_inodes (TreeDir dnum elems)) ->
      dirlist_pred (inode_tags_public ilist) elems
      =p=> dirlist_pred (inode_tags_public ilist') elems.
    Proof.
      unfold BFILE.treeseq_ilist_safe; induction elems; intros.
      cancel.
      simpl in *.
      destruct a.
      erewrite <- inode_tags_public_ilist_trans_not_in with (ilist':= ilist')(d:= d); eauto.
      cancel.
      eapply IHelems; eauto; intuition.
      apply H; eauto.
    Qed.

    Lemma dirlist_combine_app:
      forall T l1 l2 f,
        @dirlist_combine T f (l1 ++ l2) =
        dirlist_combine f l1 ++ dirlist_combine f l2.
    Proof.
      induction l1; intros.
      simpl; auto.
      simpl.
      destruct a.
      rewrite IHl1.
      rewrite app_assoc; auto.
    Qed.

        
 Lemma inode_tags_public_ilist_trans_file:
      forall path d inum ilist ilist' file,
      find_subtree path d = Some (TreeFile inum file) ->
      BFILE.treeseq_ilist_safe inum ilist ilist' ->
      tree_names_distinct d ->
      tree_inodes_distinct d ->
      inode_tags_public ilist d
      =p=> inode_tags_public ilist' d.
  Proof.
    induction path; intros.
    inversion H; cancel.
    replace (a::path) with ([a]++path) in H.
    apply find_subtree_app' in H.
    cleanup.
    destruct d; try congruence.
    simpl in H; inversion H.
    destruct (Nat.eq_dec n inum); subst.
    simpl in H.
    apply find_subtree_helper_in in H. cleanup.
    inversion H2; subst.
    
    exfalso; apply H5.
    replace inum with (dirtree_inum (TreeFile inum file)) by auto.
    eapply leaf_in_inodes_parent; eauto.
    eassign a; simpl.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec a a); try congruence.
    apply find_subtree_ents_not_in.
    inversion H1; subst.
    rewrite map_app in H8; simpl in *.
    apply NoDup_app_comm in H8.
    inversion H8; subst.
    intuition.
    simpl in H.
    apply find_subtree_helper_in in H. cleanup.
    simpl; 
    repeat rewrite dirlist_pred_split.
    simpl.
    erewrite IHpath; eauto.
    erewrite dirlist_pred_inode_tags_public_ilist_trans_not_in; eauto.
    erewrite dirlist_pred_inode_tags_public_ilist_trans_not_in with (elems := x1); eauto.
    unfold BFILE.treeseq_ilist_safe in *; cleanup.
    rewrite H0; auto.
    eassign n; simpl.
    inversion H2; subst.
    intuition.
    
    rewrite dirlist_combine_app in *; simpl in *.
    apply find_subtree_inum_present in H3; simpl in *.
    apply NoDup_app_r in H6.
    eapply not_In_NoDup_app.
    apply H3. eauto.
    auto.
    
    eassign n; simpl.
    inversion H2; subst.
    intuition.
    rewrite dirlist_combine_app in *; simpl in *.
    apply find_subtree_inum_present in H3; simpl in *.
    eapply not_In_NoDup_app.
    apply H4. eauto.
    intuition.

    eapply tree_names_distinct_subtree; eauto.
    eassign [a]; simpl.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec a a); try congruence.
    apply find_subtree_ents_not_in.
    inversion H1; subst.
    rewrite map_app in H6; simpl in *.
    apply NoDup_app_comm in H6.
    inversion H6; subst.
    intuition.

    eapply tree_inodes_distinct_subtree; eauto.
    eassign [a]; simpl.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec a a); try congruence.
    apply find_subtree_ents_not_in.
    inversion H1; subst.
    rewrite map_app in H6; simpl in *.
    apply NoDup_app_comm in H6.
    inversion H6; subst.
    intuition.
    simpl; auto.
  Qed.


  Lemma dirlist_pred_inode_tags_public_delete_from_list:
      forall tree_elem ilist name,
     dirlist_pred (inode_tags_public ilist) tree_elem
     =p=> dirlist_pred (inode_tags_public ilist) (delete_from_list name tree_elem).
    Proof.
      induction tree_elem; intros.
      cancel.
      simpl in *.
      destruct a.
      destruct (string_dec s name); subst.
      cancel.
      apply inode_tags_public_pimpl_emp.
      simpl.
      cancel.
      eauto.
    Qed.

    Lemma inode_tags_public_ilist_trans_not_in_weak:
      forall inum ilist ilist',
      (forall (inum' : addr) (def' : INODE.inode),
        (inum' = inum -> False) -> selN ilist inum' def' = selN ilist' inum' def') ->
      forall d, [[ ~In inum (tree_inodes d) ]] * inode_tags_public ilist d
      =p=> inode_tags_public ilist' d.
    Proof.
      intros.
      generalize d; apply dirtree_ind2; intros.
      cancel.
      cleanup.
      norml.
      simpl; rewrite <- H.
      cancel.
      generalize dependent inum0.
      generalize dependent tree_ents. induction tree_ents; intros.
      cancel.
      simpl in *.
      destruct a.
      inversion H0; subst.
      rewrite <- H6, IHtree_ents.
      cancel.
      all: eauto; intuition.
    Qed.

    Lemma dirlist_pred_inode_tags_public_ilist_trans_not_in_weak:
      forall elems dnum inum ilist ilist',
      (forall (inum' : addr) (def' : INODE.inode),
        (inum' = inum -> False) -> selN ilist inum' def' = selN ilist' inum' def') ->
      ~In inum (tree_inodes (TreeDir dnum elems)) ->
      dirlist_pred (inode_tags_public ilist) elems
      =p=> dirlist_pred (inode_tags_public ilist') elems.
    Proof.
      induction elems; intros.
      cancel.
      simpl in *.
      destruct a.
      erewrite <- inode_tags_public_ilist_trans_not_in_weak with (ilist':= ilist')(d:= d); eauto.
      cancel.
      eapply IHelems; eauto; intuition.
      apply H1; eauto.
    Qed.

    
    Lemma inode_tags_public_ilist_trans_file_weak:
      forall path d inum ilist ilist' file,
      find_subtree path d = Some (TreeFile inum file) ->
      (forall (inum' : addr) (def' : INODE.inode),
        (inum' = inum -> False) -> selN ilist inum' def' = selN ilist' inum' def') ->
      tree_names_distinct d ->
      tree_inodes_distinct d ->
      inode_tags_public ilist d
      =p=> inode_tags_public ilist' d.
  Proof.
    induction path; intros.
    inversion H; cancel.
    replace (a::path) with ([a]++path) in H.
    apply find_subtree_app' in H.
    cleanup.
    destruct d; try congruence.
    simpl in H; inversion H.
    destruct (Nat.eq_dec n inum); subst.
    simpl in H.
    apply find_subtree_helper_in in H. cleanup.
    inversion H2; subst.
    
    exfalso; apply H5.
    replace inum with (dirtree_inum (TreeFile inum file)) by auto.
    eapply leaf_in_inodes_parent; eauto.
    eassign a; simpl.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec a a); try congruence.
    apply find_subtree_ents_not_in.
    inversion H1; subst.
    rewrite map_app in H8; simpl in *.
    apply NoDup_app_comm in H8.
    inversion H8; subst.
    intuition.
    simpl in H.
    apply find_subtree_helper_in in H. cleanup.
    simpl; 
    repeat rewrite dirlist_pred_split.
    simpl.
    erewrite IHpath; eauto.
    erewrite dirlist_pred_inode_tags_public_ilist_trans_not_in_weak; eauto.
    erewrite dirlist_pred_inode_tags_public_ilist_trans_not_in_weak with (elems := x1); eauto.
    rewrite H0; auto.
    
    eassign n; simpl.
    inversion H2; subst.
    intuition.
    rewrite dirlist_combine_app in *; simpl in *.
    apply find_subtree_inum_present in H3; simpl in *.
    apply NoDup_app_r in H6.
    eapply not_In_NoDup_app.
    apply H3. eauto.
    auto.
    
    eassign n; simpl.
    inversion H2; subst.
    intuition.
    rewrite dirlist_combine_app in *; simpl in *.
    apply find_subtree_inum_present in H3; simpl in *.
    eapply not_In_NoDup_app.
    apply H4. eauto.
    intuition.

    eapply tree_names_distinct_subtree; eauto.
    eassign [a]; simpl.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec a a); try congruence.
    apply find_subtree_ents_not_in.
    inversion H1; subst.
    rewrite map_app in H6; simpl in *.
    apply NoDup_app_comm in H6.
    inversion H6; subst.
    intuition.

    eapply tree_inodes_distinct_subtree; eauto.
    eassign [a]; simpl.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec a a); try congruence.
    apply find_subtree_ents_not_in.
    inversion H1; subst.
    rewrite map_app in H6; simpl in *.
    apply NoDup_app_comm in H6.
    inversion H6; subst.
    intuition.
    simpl; auto.
  Qed.

   Lemma inode_tags_public_ilist_trans_weak:
    forall d inum ilist ilist',
      INODE.IOwner (selN ilist' inum INODE.inode0) = Public ->
      (forall (inum' : addr) (def' : INODE.inode),
        (inum' = inum -> False) -> selN ilist inum' def' = selN ilist' inum' def') ->
      inode_tags_public ilist d
      =p=> inode_tags_public ilist' d.
  Proof.
    intros.
    generalize d; apply dirtree_ind2; intros.
    simpl; cancel.
    simpl; cancel.
    generalize dependent tree_ents.
    induction tree_ents.
    intros; simpl; cancel.
    intros; simpl.
    inversion H1; subst.
    destruct a; simpl in *.
    rewrite H5, IHtree_ents; auto.
    destruct(Nat.eq_dec inum inum0); subst; eauto.
    unfold BFILE.treeseq_ilist_safe in *; cleanup.
    rewrite <- H0; auto.
  Qed.

  Lemma dirlist_pred_inode_tags_public_ilist_trans_weak:
    forall tree_elem ilist ilist' dnum,
      INODE.IOwner (selN ilist' dnum INODE.inode0) = Public ->
      (forall (inum' : addr) (def' : INODE.inode),
        (inum' = dnum -> False) -> selN ilist inum' def' = selN ilist' inum' def') ->
      dirlist_pred (inode_tags_public ilist) tree_elem
      =p=> dirlist_pred (inode_tags_public ilist') tree_elem.
  Proof.
    induction tree_elem; simpl; intros.
    cancel.
    destruct a.
    erewrite inode_tags_public_ilist_trans_weak, IHtree_elem; eauto.
  Qed.
    

  Lemma inode_tags_public_prune:
  forall tree path name inum ilist l,
    find_subtree path tree = Some (TreeDir inum l) ->
   inode_tags_public ilist tree
   =p=> inode_tags_public ilist (tree_prune inum l path name tree).
  Proof.
    intros.
    unfold tree_prune.
    rewrite <- inode_tags_public_update.
    simpl.                                                                                      
    rewrite <- dirlist_pred_inode_tags_public_delete_from_list.
    erewrite inode_tags_public_subtree at 1; eauto.
    simpl; cancel.
  Qed.  

  Lemma inode_tags_public_ilist_trans_listmatch:
      forall AT AEQ V d ilist ilist' (m: @Mem.mem AT AEQ V),
     listmatch (fun i i' : INODE.inode =>
             [[ INODE.IOwner i = INODE.IOwner i' ]]%pred) ilist ilist' m ->
      inode_tags_public ilist d
      =p=> inode_tags_public ilist' d.
  Proof.
    intros.
    generalize d; apply dirtree_ind2; intros.
    simpl; cancel.
    simpl; cancel.
    generalize dependent tree_ents.
    induction tree_ents.
    intros; simpl; cancel.
    intros; simpl.
    inversion H0; subst.
    destruct a; simpl in *.
    rewrite H4, IHtree_ents; auto.
    destruct(lt_dec inum (length ilist')); subst; eauto.
    eapply listmatch_extract with (i:=inum) in H.
    destruct_lift H; eauto.
    rewrite <- H4; eauto.
    apply listmatch_length_pimpl in H.
    destruct_lift H; eauto.
    rewrite H4; eauto.
    apply Nat.nlt_ge in n.
    rewrite selN_oob by auto.
    unfold INODE.IOwner, INODE.inode0,
    INODE.AOwner, INODE.iattr0; simpl.
    setoid_rewrite <- encode_public; apply encode_decode.
  Qed.*)