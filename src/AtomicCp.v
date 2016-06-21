Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import SuperBlock.
Require Import DiskSet.
Require Import AsyncFS.
Require Import String.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.


Import ListNotations.

Set Implicit Arguments.

(**
 * Atomic copy: create a copy of file [src_fn] in the root directory [the_dnum],
 * with the new file name [dst_fn].
 *
 *)


Module ATOMICCP.

  Parameter the_dnum : addr.
  Parameter cachesize : nat.
  Axiom cachesize_ok : cachesize <> 0.
  Hint Resolve cachesize_ok.


  Definition temp_fn := ".temp"%string.
  
  (** Programs **)

  (* copy an existing src into an existing, empty dst. *)

  Definition copydata fsxp src_inum dst_inum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, b) <- AFS.read_fblock fsxp src_inum 0 mscs;
    let^ (mscs) <- AFS.update_fblock_d fsxp dst_inum 0 b mscs;
    let^ (mscs) <- AFS.file_sync fsxp dst_inum mscs;   (* sync blocks *)
    let^ (mscs, ok) <- AFS.file_set_attr fsxp dst_inum attr mscs;
    Ret ^(mscs, ok).

  Definition copy2temp fsxp src_inum dst_inum mscs :=
    let^ (mscs, ok) <- AFS.file_truncate fsxp dst_inum 1 mscs;  (* XXX type error when passing sz *)
    If (bool_dec ok true) {
      let^ (mscs, ok) <- copydata fsxp src_inum dst_inum mscs;
      Ret ^(mscs, ok)
    } else {
      Ret ^(mscs, ok)
    }.

  Definition copy_and_rename fsxp src_inum dst_inum dst_fn mscs :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum dst_inum mscs;
    match ok with
      | false =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        (* Just for a simpler spec: the state is always (d, nil) after this function *)
        Ret ^(mscs, false)
      | true =>
        let^ (mscs, ok1) <- AFS.rename fsxp the_dnum [] temp_fn [] dst_fn mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        Ret ^(mscs, ok1)
    end.

  Definition atomic_cp fsxp src_inum dst_fn mscs :=
    let^ (mscs, maybe_dst_inum) <- AFS.create fsxp the_dnum temp_fn mscs;
    match maybe_dst_inum with
      | None => Ret ^(mscs, false)
      | Some dst_inum =>
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum dst_inum dst_fn mscs;
        Ret ^(mscs, ok)
    end.

  (** recovery programs **)

  (* atomic_cp recovery: if temp_fn exists, delete it *)
  Definition cleanup fsxp mscs :=
    let^ (mscs, maybe_src_inum) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
    match maybe_src_inum with
    | None => Ret mscs
    | Some (src_inum, isdir) =>
      let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
      let^ (mscs) <- AFS.tree_sync fsxp mscs;
      Ret mscs
    end.

  (* top-level recovery function: call AFS recover and then atomic_cp's recovery *)
  Definition recover :=
    let^ (mscs, fsxp) <- AFS.recover cachesize;
    let^ (mscs, maybe_src_inum) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
    match maybe_src_inum with
    | None => Ret ^(mscs, fsxp)
    | Some (src_inum, isdir) =>
      let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
      let^ (mscs) <- AFS.tree_sync fsxp mscs;
      Ret ^(mscs, fsxp)
    end.

  (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.

  Ltac xcrash_norm :=  repeat (xform_norm; cancel).
  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Definition temp_treeseqpred Ftree tmppath inum (to : treeseq_one) :=
    exists f,
      (Ftree * tmppath |-> (inum, f))%pred  (dir2flatmem [] (TStree to)).

  Theorem copydata_ok : forall fsxp src_inum tmppath tinum mscs,
    {< ds ts Fm Ftop Ftree Ftmp srcpath file tfile v0 t0,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (temp_treeseqpred Ftmp tmppath tinum) ts ]] *
      [[ (Ftree * srcpath |-> (src_inum, file) * tmppath |-> (tinum, tfile))%pred
            (dir2flatmem [] (TStree ts!!)) ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]] *
      [[[ BFILE.BFData tfile ::: (0 |-> t0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
       [[ treeseq_pred (temp_treeseqpred Ftmp tmppath tinum) ts' ]] *
        (([[ r = false ]] *
          exists tfile',
            [[ (Ftree * srcpath |-> (src_inum, file) * tmppath |-> (tinum, tfile'))%pred (dir2flatmem [] (TStree ts'!!)) ]])
         \/ ([[ r = true ]] *
            [[ (Ftree * srcpath |-> (src_inum, file) * tmppath |-> (tinum, (BFILE.synced_file file)))%pred (dir2flatmem [] (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' ts',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
      [[ treeseq_pred (temp_treeseqpred Ftmp tmppath tinum) ts' ]]
     >} copydata fsxp src_inum tinum mscs.
  Proof.
    unfold copydata; intros.
    
    prestep.
    norml; unfold stars; simpl.
    safecancel.
    eassumption.
    eassumption.
    prestep.
    norml; unfold stars; simpl.
    safecancel.
    (* s = mscs, H15 *)
    admit.
    eassumption.
    instantiate (Fd := emp).
    admit.

    prestep.
    norml; unfold stars; simpl.
    safecancel.
    admit.
    admit.
    admit.

  Admitted.





  Lemma diskset_pred_sync: forall V (p: @pred _ _ V) ds,
    diskset_pred p ds ->
    diskset_pred p (ds!!, []).
  Proof.
    intros.
    unfold diskset_pred in *.
    intros.
    apply H.
    apply d_in_In in H0; inversion H0; subst.
    apply latest_in_ds.
    inversion H1.
  Qed.

  Lemma diskset_pred_pushd: forall V (p: @pred _ _ V) ds d,
    diskset_pred p ds ->
    p (list2nmem d) ->
    diskset_pred p (pushd d ds).
  Proof.
    intros.
    unfold diskset_pred in *.
    intros.
    apply d_in_pushd in H1. intuition; subst.
    eassumption.
  Qed.

  (* each tree has a temp file with inode timum. furthermore, there is a dirtree_safe
   * transition from tree to newest tree. *)
  Definition temp_tree_pred Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum :=
    (exists tree tfile ilist freelist,
      Fm * DIRTREE.rep fsxp Ftop tree ilist freelist *
      [[ DIRTREE.find_subtree [temp_fn] tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ DIRTREE.dirtree_safe ilist (BFILE.pick_balloc freelist (MSAlloc mscs)) tree
                               newest_ilist  (BFILE.pick_balloc newest_free  (MSAlloc mscs)) newest_tree ]]
    )%pred.

  Definition temp_tree_pred_ds Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum ds :=
    exists ts,
    treeseq_in_ds Fm Ftop fsxp mscs ts ds /\
    latest ts = mk_tree newest_tree newest_ilist newest_free /\
    NEforall (temp_treeseqpred newest_tree tinum) ts.


  Lemma temp_tree_pred_dupdate_eq: forall Fm Ftop fsxp newest_ilist newest_free newest_tree mscs d tinum bn off v f,
    BFILE.block_belong_to_file newest_ilist bn tinum off ->
    DIRTREE.find_subtree [temp_fn] newest_tree = Some (DIRTREE.TreeFile tinum f) ->
    temp_tree_pred Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum (list2nmem d) ->
    temp_tree_pred Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum (list2nmem d ⟦ bn := v ⟧).
  Proof.
    intros.
    unfold temp_tree_pred in *.
    repeat (destruct H1).
    edestruct DIRTREE.dirtree_update_safe_pathname_pred.
    eapply pimpl_apply; try eassumption. cancel.
    2: eassumption.
    2: eassumption.
    eapply sep_star_lift_apply in H1.
    intuition.
    eassumption.
    eexists x.
    eexists x0.
    eexists x1.
    eexists x2.
    eapply pimpl_apply; try eassumption. cancel.
    destruct_lift H1; eauto.
    destruct_lift H1; eauto.
    destruct H2.
    destruct H2.
    remember {|
        BFILE.BFData := (BFILE.BFData x4) ⟦ off := v ⟧;
        BFILE.BFAttr := BFILE.BFAttr x4|} as f'.
    eexists (DIRTREE.update_subtree x3 (DIRTREE.TreeFile tinum f') x).
    eexists f'.
    eexists x1.
    eexists x2.
    (* prove that x3 = temp_fn and x4 = x0 *)
    destruct_lift H1.
    destruct_lift H2.
    assert (x3 = [temp_fn]) as Hpn.
    eapply find_subtree_inode_pathname_unique.
    instantiate (1 := x).
    distinct_inodes.
    distinct_names.
    eauto.
    eassumption.
    eauto.
    rewrite Hpn.
    rewrite Hpn in H3.
    rewrite H3 in H6.
    inversion H6.
    subst.
    pred_apply.
    cancel.
    eapply DIRTREE.dirtree_safe_update_subtree.
    eassumption.
    eauto.
  Qed.


  Lemma temp_tree_pred_vssync_eq: forall Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum d f al,
    Forall
     (fun bn0 : addr =>
      exists off0 : addr, BFILE.block_belong_to_file newest_ilist bn0 tinum off0) al ->
    DIRTREE.find_subtree [temp_fn] newest_tree = Some (DIRTREE.TreeFile tinum f) ->
    temp_tree_pred Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum (list2nmem d) ->
    temp_tree_pred Fm Ftop fsxp newest_ilist newest_free newest_tree mscs tinum (list2nmem (vssync_vecs d al)).
  Proof.
    intros.
    unfold temp_tree_pred in *.
    repeat (destruct H1).
    edestruct dirtree_update_safe_pathname_vssync_vecs_pred; eauto.
    eapply pimpl_apply; try eassumption. cancel.
    destruct_lift H1.
    eassumption.
    eexists x.
    eexists x0.
    eexists x1.
    eexists x2.
    eapply pimpl_apply; try eassumption. cancel.
    destruct_lift H1; eauto.
    destruct_lift H1; eauto.
    repeat (destruct H2).
    remember {|
            BFILE.BFData := x5;
            BFILE.BFAttr := BFILE.BFAttr x4 |} as f'.
    eexists (DIRTREE.update_subtree x3 (DIRTREE.TreeFile tinum f') x).
    eexists f'.
    eexists x1.
    eexists x2.
    destruct_lift H1.
    destruct_lift H2.
    assert (x3 = [temp_fn]) as Hpn.
    eapply find_subtree_inode_pathname_unique.
    instantiate (1 := x).
    distinct_inodes.
    distinct_names.
    eauto.
    eassumption.
    eauto.
    rewrite Hpn.
    rewrite Hpn in H3.
    rewrite H3 in H6.
    inversion H6.
    subst.
    pred_apply.
    cancel.
    eapply DIRTREE.dirtree_safe_update_subtree.
    eassumption.
    eauto.
  Qed.

  Hint Resolve DIRTREE.dirtree_safe_trans : dirtree_safe.
  Hint Resolve DIRTREE.dirtree_safe_refl : dirtree_safe.

  Lemma temp_tree_pred_safe_trans: forall Fm Ftop fsxp ilist free tree ilist' free' tree' mscs tinum,
    DIRTREE.dirtree_safe ilist (BFILE.pick_balloc free (MSAlloc mscs)) tree ilist' (BFILE.pick_balloc free' (MSAlloc mscs)) tree' ->
    temp_tree_pred Fm Ftop fsxp ilist free tree mscs tinum =p=> temp_tree_pred Fm Ftop fsxp ilist' free' tree' mscs tinum.
  Proof.
    intros.
    unfold temp_tree_pred in *.
    cancel.
    eauto.
    eauto with dirtree_safe.
  Qed.

  Ltac diskset_pred_solve := 
    repeat match goal with
      | [ |- diskset_pred _ (dssync_vecs (dsupd _ _ _) _) ] 
          => idtac "diskset_pred dssync";  eapply diskset_pred_d_map
      | [ |- diskset_pred _ (dsupd _ _ _)] 
          => idtac "diskset_pred"; eapply diskset_pred_d_map; eauto
      | [ |- diskset_pred _ (_ !!, []) ] => idtac "sync"; eapply diskset_pred_sync; eauto
      | [ |- diskset_pred _ (pushd _ _)] => idtac "pushd"; eapply diskset_pred_pushd
      | [ |- temp_tree_pred _ _ _ _ _ _ _ _ (list2nmem ?d) ]
          => idtac "temp_tree_pred apply"; pred_apply; unfold temp_tree_pred; cancel; eauto
      | [ |- temp_tree_pred _ _ _ _ _ _ _ _ (list2nmem (vssync_vecs _ _)) ]
          => idtac "temp_tree_pred_vssync"; eapply temp_tree_pred_vssync_eq; eauto
      | [ |- forall _ : _, temp_tree_pred _ _ _ _ _ _ _ _ _ -> _ (list2nmem _ ⟦ _ := _ ⟧)] 
          => idtac "forall"; intros; eapply temp_tree_pred_dupdate_eq; eauto
      | [ |- forall _ : _, temp_tree_pred _ _ _ ?ilist _ _ _ _ _ -> temp_tree_pred _ _ _ ?ilist _ _ _ _ _ ] 
          => idtac "forall2"; intros; eapply temp_tree_pred_vssync_eq; eauto
      | [ |- forall _ : _, temp_tree_pred _ _ _ ?ilist _ _ _ _ _ -> temp_tree_pred _ _ _ ?ilist' _ _ _ _ _ ] 
          => idtac "forall3"; intros; eapply temp_tree_pred_safe_trans; eauto
      | [ |- Forall _ _ ] => eapply Forall_forall; intros ? Hin
      | [ Hin: In _ _ |- _ ] => idtac "Hin";  eapply in_selN_exists in Hin; destruct Hin as [? Hin]; destruct Hin as [? Hin1]
      | [ Hin1: _ |- exists _: _, BFILE.block_belong_to_file _ _ _ _] 
        => idtac "Hin1"; rewrite <- Hin1; clear Hin1; eauto 
      | [ H: MSAlloc _ = MSAlloc _ |- DIRTREE.dirtree_safe _ _ _ _ _ _ ]
        => idtac "rewrite" H; rewrite H in *; clear H
      | [ H: BFILE.diskset_was _ _ |- diskset_pred _ _ ] => 
         idtac "subset"; unfold BFILE.diskset_was in H; intuition; subst; clear H  
     end; eauto with dirtree_safe.

  Theorem copydata_ok : forall fsxp src_inum tinum mscs,
    {< ds Fm Ftop temp_tree src_fn file tfile ilist freelist v0 t0,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ temp_tree_pred_ds Fm Ftop fsxp ilist freelist temp_tree mscs tinum ds ]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]] *
      [[[ BFILE.BFData tfile ::: (0 |-> t0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
      exists tree' ilist' freelist',
        [[ temp_tree_pred_ds Fm Ftop fsxp ilist' freelist' tree' mscs tinum ds' ]] *
        (([[ r = false ]] *
          exists tfile',
          [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree ]])
      \/ ([[ r = true ]] * 
          [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum (BFILE.synced_file file)) temp_tree ]]))
    XCRASH:hm'
      exists ds',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      exists tfile' ilist' freelist',
      let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree in
      [[ temp_tree_pred_ds Fm Ftop fsxp ilist' freelist' tree' mscs tinum ds' ]]
     >} copydata fsxp src_inum tinum mscs.
  Proof.
    unfold copydata; intros.

    prestep.
    norml; unfold stars; simpl.

    unfold temp_tree_pred_ds in H9.
    deex.
    unfold treeseq_in_ds in H3; intuition.
    unfold tree_rep in H9.
    rewrite H0 in *; clear H0.
    cancel.
    eauto.

    step.
    step.
    step.
    step.
    step.

    diskset_pred_solve.

    or_r. cancel.
    erewrite update_update_subtree_eq; eauto.
    erewrite update_update_subtree_eq; eauto.
    unfold BFILE.synced_file.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (BFILE.BFData file)) by eauto.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (BFILE.BFData f')) by eauto.
    eauto.
    distinct_names.
    constructor.
    distinct_names.
    constructor.

    diskset_pred_solve.

    (* Handle crash cases *)
    xcrash.
    repeat (xform_deex_r).
    xform_norm; cancel. 

    diskset_pred_solve.

    xcrash.
    repeat (xform_deex_r).
    xform_norm; cancel.

    diskset_pred_solve.

    xcrash.
    repeat (xform_deex_r).
    xform_norm; cancel.

    repeat (xform_deex_r).
    xform_norm; cancel.
    instantiate (2 := ilist).
    instantiate (1 := (freelist_1, freelist_2)).
    instantiate (1 := (DIRTREE.dirtree_update_inode temp_tree tinum 0 (fst v0, vsmerge t0))).
    rewrite dsupd_latest.
    eapply DIRTREE.dirtree_update_block; eauto.
    diskset_pred_solve.

    erewrite DIRTREE.dirtree_update_inode_update_subtree with (pathname := [temp_fn]).
    erewrite DIRTREE.find_update_subtree; eauto.
    distinct_inodes.
    distinct_names.
    eauto.
    eapply list2nmem_inbound; eauto.
    pred_apply.
    cancel.

    erewrite DIRTREE.dirtree_update_inode_update_subtree with (pathname := [temp_fn]).
    eapply dirtree_safe_dupdate; eauto.
    distinct_inodes.
    distinct_names.
    eauto.
    eapply list2nmem_inbound; eauto.
    pred_apply.
    cancel.

    xcrash.
    repeat (xform_deex_r).
    xform_norm; cancel.

    xcrash.
    repeat (xform_deex_r).
    xform_norm; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (copydata _ _ _ _) _) => apply copydata_ok : prog.

  Theorem copy2temp_ok : forall fsxp src_inum tinum mscs,
    {< d Fm Ftop temp_tree src_fn file tfile v0 ilist freeblocks,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm * 
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree ilist freeblocks) ]]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
      [[ forall d, d_in d ds' -> exists tfile' ilist' freelist',
         let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree in
         (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freelist')%pred (list2nmem d) ]] *
      ([[ r = false ]] \/
       [[ r = true ]] *
       exists ilist' freelist',
       let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum (BFILE.synced_file file)) temp_tree in
       [[[ ds'!! ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freelist') ]]])
    XCRASH:hm'
      exists ds',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ forall d, d_in d ds' -> exists tfile' ilist' freelist',
         let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree in
         (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freelist')%pred (list2nmem d) ]]
     >} copy2temp fsxp src_inum tinum mscs.
  Proof.
    unfold copy2temp; intros.
    step.
    step.
    step.
    step.
    denote d_in as Hdin. inversion Hdin; simpl in *; subst; [ | exfalso; eauto ].
    repeat eexists. pred_apply. 
    rewrite update_subtree_same.
    cancel.
    distinct_names.
    eauto.
    step.
    denote d_in as Hdin. inversion Hdin; clear Hdin; simpl in *; subst.
    do 3 eexists.
    repeat erewrite update_update_subtree_eq; eauto.
    split.
    eapply DIRTREE.dirtree_safe_update_subtree; eauto.
    pred_apply. cancel.
    erewrite update_subtree_same. cancel.

    eapply dirtree_isdir_true_find_subtree in H6 as Hdir.
    distinct_names.
    eauto.
    distinct_names.
    constructor.

    intuition; subst. (* the other part of [d_in] *)
    do 3 eexists.
    repeat erewrite update_update_subtree_eq; eauto.
    split.
    apply DIRTREE.dirtree_safe_refl.
    pred_apply. cancel.
    distinct_names.
    constructor.
    rewrite find_subtree_update_subtree_ne. eauto. eauto. eauto.

    apply setlen_singleton_ptsto.
    step.
    denote (d_in _ _ -> _) as Hdpred.
    edestruct Hdpred; eauto. repeat deex.
    repeat eexists. pred_apply.
    erewrite update_update_subtree_eq; eauto. distinct_names. constructor.
    or_r. cancel.
    erewrite update_update_subtree_eq; eauto. distinct_names. constructor.
    denote (d_in _ _ -> _) as Hdpred.
    edestruct Hdpred. eauto. repeat deex.
    repeat eexists. pred_apply.
    erewrite update_update_subtree_eq; eauto. distinct_names. constructor.

    AFS.xcrash_solve. xform_norm; cancel. xform_norm; safecancel.
    denote (d_in _ _ -> _) as Hdpred.
    edestruct Hdpred; eauto. repeat deex.
    repeat eexists. pred_apply.
    erewrite update_update_subtree_eq; eauto. distinct_names. constructor.

    step.

    AFS.xcrash_solve; xform_norm; cancel; xform_norm; safecancel.
    denote d_in as Hdin. inversion Hdin; simpl in *; subst; [ | exfalso; eauto ].
    repeat eexists. pred_apply.
    erewrite update_subtree_same. cancel. distinct_names. eauto.

    denote d_in as Hdin. inversion Hdin; simpl in *; subst.
    repeat eexists. pred_apply.
    erewrite update_subtree_same. cancel. distinct_names. eauto.

    intuition; subst.
    repeat eexists. pred_apply.
    cancel.
    Unshelve. all: try exact unit.  all:eauto.  all: try exact tt.  all: try exact (tt, nil).
  Qed.


  Hint Extern 1 ({{_}} progseq (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Theorem copy_rename_ok : forall  fsxp src_inum tinum dst_fn mscs,
    {< d Fm Ftop temp_tree tree_elem src_fn file tfile v0 ilist freeblocks,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm * 
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree ilist freeblocks) ]]] *
      [[ temp_tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[ dst_fn <> temp_fn ]] *
      [[ dst_fn <> src_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists d tree' ilist' freeblocks' dstents,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freeblocks') ]]] *
      (([[r = false ]] *
        (exists f',
        [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum f') temp_tree ]])) \/
       ([[r = true ]] *
        let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
        let pruned := DIRTREE.tree_prune the_dnum tree_elem [] temp_fn temp_tree in
        [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
        [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]]))
    XCRASH:hm'
      exists ds_temps,
      [[ forall d, d_in d ds_temps -> exists tfile' ilist' freelist',
         let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree in
         (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freelist')%pred (list2nmem d) ]] *
     (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds_temps hm' \/
      exists d' tree' ilist' frees' dstents,
      [[[ d' ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d' ds_temps) hm' *
      let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
      let pruned := DIRTREE.tree_prune the_dnum tree_elem [] temp_fn temp_tree in
      [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
      [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]])
     >} copy_and_rename fsxp src_inum tinum dst_fn mscs.
  Proof.
    unfold copy_and_rename, AFS.rename_rep; intros.
    step.
    destruct a0.

    (* copy succeeded *)
    step.
    instantiate (cwd0 := []).
    f_equal.
    rewrite find_subtree_root.
    rewrite (DIRTREE.dirtree_dir_parts (DIRTREE.update_subtree _ _ _)).
    f_equal. f_equal. eauto. 
    unfold AFS.rename_rep.
    step. (* tree_sync *)
    step. (* return false, rename failed? *)
    AFS.xcrash_solve.
    cancel.
    repeat xform_dist.
    cancel.

    step. (* return true, rename succeeded *)
    or_r.
    cancel.
    rewrite (DIRTREE.dirtree_dir_parts (DIRTREE.tree_prune _ _ _ _ _)).
    f_equal.
    rewrite find_subtree_root in H25.
    inversion H25.
    rewrite <- H16 in *.
    rewrite dirtree_isdir_prune; auto.
    rewrite update_subtree_root.
    rewrite find_subtree_root in H25.
    inversion H25.
    rewrite <- H16 in *.
    rewrite find_subtree_root in H22.
    rewrite (DIRTREE.dirtree_dir_parts (DIRTREE.tree_prune _ _ _ _ _)) in H22.
    inversion H22.
    rewrite <- H20 in *.
    f_equal.


    AFS.xcrash_solve.
    (* crashed with completing rename, but not sync *)
    cancel.
    repeat xform_dist.  (* do manually so that we can do or_r *)
    norm.
    or_r.
    safecancel.
    xcrash_norm.

    eapply dirtree_isdir_true_find_subtree in H9 as Hdir.
    eapply DIRTREE.dirtree_dir_parts in Hdir. rewrite H10 in Hdir.
    rewrite Hdir. f_equal.
    admit.  (* some dents *)
    admit. (* prune *)
    rewrite update_subtree_root.
    admit. (* graft as above *)
    intuition.
    
    AFS.xcrash_solve.
    xcrash_norm.

    (* step manually to get evars *)
    prestep. norm'l.
    edestruct H16.
    eapply latest_in_ds.
    repeat deex.
    cancel.

    step.  (* return in false case *)

    AFS.xcrash_solve.
    xcrash_norm.
    AFS.xcrash_solve.
    xcrash_norm.

    Unshelve. all: eauto.  all: try exact [].
  Admitted.

  Hint Extern 1 ({{_}} progseq (copy_and_rename _ _ _ _ _) _) => apply copy_rename_ok : prog.

  (* specs for copy_and_rename_cleanup and atomic_cp *)

  Theorem atomic_cp_recover_ok :
    {< fsxp cs ds base_tree temp_dents src_fn src_inum dst_fn file tinum old_tfile,
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ base_tree = DIRTREE.TreeDir the_dnum temp_dents ]] *
      [[ DIRTREE.find_subtree [temp_fn] base_tree = Some (DIRTREE.TreeFile tinum old_tfile) ]] *
      [[ DIRTREE.find_subtree [src_fn] base_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ forall d, d_in d ds ->
         exists Fm Ftop ilist frees tree dstents subtree dst_inum base_tree' temp_dents',
         (base_tree' = DIRTREE.TreeDir the_dnum temp_dents') /\
         (base_tree' = base_tree \/ DTCrash.tree_crash base_tree base_tree') /\
         let dst_subtree := DIRTREE.TreeFile dst_inum (BFILE.synced_file file) in
         let tree_temp  := DIRTREE.update_subtree [temp_fn] subtree base_tree' in
         let tree_prune := DIRTREE.tree_prune the_dnum temp_dents' [] temp_fn base_tree' in
         let tree_dst   := DIRTREE.tree_graft the_dnum dstents [] dst_fn dst_subtree tree_prune in
         tree_prune = DIRTREE.TreeDir the_dnum dstents /\
         (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) /\
         (tree = tree_temp \/ tree = tree_prune \/ tree = tree_dst) ]]%type
    POST:hm' RET:^(ms, fsxp')
      [[ fsxp' = fsxp ]] *
      exists d tree_after_crash temp_dents_after_crash dstents tree' Fm' Ftop' ilist' frees',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) hm' *
      [[ DTCrash.tree_crash base_tree tree_after_crash ]] *
      [[ tree_after_crash = DIRTREE.TreeDir the_dnum temp_dents_after_crash ]] *
      let tree'prune := DIRTREE.tree_prune the_dnum temp_dents_after_crash [] temp_fn tree_after_crash in
      let dst_subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
      let tree'dst := DIRTREE.tree_graft the_dnum dstents [] dst_fn dst_subtree tree'prune in
      [[ tree'prune = DIRTREE.TreeDir the_dnum dstents ]] *
      [[[ d ::: Fm' * DIRTREE.rep fsxp Ftop' tree' ilist' frees' ]]] *
      [[ tree' = tree'prune \/ tree' = tree'dst ]]
    XCRASH:hm'
      exists ds',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ forall d, d_in d ds' ->
         exists Fm Ftop ilist frees tree dstents f' dst_inum base_tree' temp_dents',
         (base_tree' = DIRTREE.TreeDir the_dnum temp_dents') /\
         (base_tree' = base_tree \/ DTCrash.tree_crash base_tree base_tree') /\
         let dst_subtree := DIRTREE.TreeFile dst_inum (BFILE.synced_file file) in
         let tree_temp  := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum f') base_tree' in
         let tree_prune := DIRTREE.tree_prune the_dnum temp_dents' [] temp_fn base_tree' in
         let tree_dst   := DIRTREE.tree_graft the_dnum dstents [] dst_fn dst_subtree tree_prune in
         tree_prune = DIRTREE.TreeDir the_dnum dstents /\
         (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) /\
         (tree = tree_temp \/ tree = tree_prune \/ tree = tree_dst) ]]%type
    >} recover.
  Proof.
    unfold recover; intros.
    step.
    prestep. norml; unfold stars; simpl.
    denote! (forall _, d_in _ _ -> _) as Hdin.
    edestruct Hdin as [? Hdin'].
    eapply nthd_in_ds.
    do 13 destruct Hdin' as [? Hdin'].
    denote! (crash_xform _ _) as Hcrashd.
    denote! (_ \/ DTCrash.tree_crash _ _) as Hcrash_or_not.
    destruct Hcrash_or_not.   (* the two-way or in the precondition. *)
    - (* why is [setoid_rewrite] not doing the right thing? *)
      eapply crash_xform_pimpl_proper in Hcrashd; [ | apply diskIs_pred; eassumption ].
      apply crash_xform_sep_star_dist in Hcrashd.
      rewrite DTCrash.xform_tree_rep in Hcrashd.
      destruct_lift Hcrashd.
      denote DTCrash.tree_crash as Htc.
      intuition; subst.  (* 3 cases from the precondition.. *)
      + (* temp file is there *)
        apply DTCrash.tree_crash_update_subtree in Htc as Htc'; repeat deex; intuition.
        denote (DTCrash.tree_crash _ tree_crashed) as Htc_base; inversion Htc_base; subst.
        cancel.
        safestep.
        rewrite find_subtree_root.
        match goal with
        | [ |- Some ?t' = _ ] =>
          erewrite DIRTREE.dirtree_dir_parts with (t := t') by ( apply dirtree_isdir_update_subtree; auto );
          reflexivity
        end.

        (* our [delete_ok] should never fail.. *)
        destruct a2.
        2: admit.  (* need to eventually fix [delete_ok].. *)
        step.
        safestep.
        denote (DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ temp_dents) as H'; inversion H'; subst.
        eassumption.
        reflexivity.

        match goal with
        | [ |- ?t' = _ ] =>
          erewrite DIRTREE.dirtree_dir_parts with (t := t')
        end.
        rewrite DIRTREE.tree_prune_preserve_inum by reflexivity. reflexivity.
        rewrite DIRTREE.tree_prune_preserve_isdir by reflexivity. reflexivity.
        rewrite update_subtree_root.
        left.   (* dst not created yet *)
        unfold DIRTREE.tree_prune. rewrite update_subtree_root.

      (*
DIRTREE.delete_from_dir temp_fn
  (DIRTREE.TreeDir the_dnum
     (DIRTREE.dirtree_dirents
        (DIRTREE.update_subtree [temp_fn] subtree_crashed (DIRTREE.TreeDir the_dnum st')))) =
DIRTREE.delete_from_dir temp_fn (DIRTREE.TreeDir the_dnum st')
      *)
        admit.

        admit.

        AFS.xcrash_solve.
        admit. (* hash subset *)
        cancel. repeat xform_dist. cancel.

        denote! (d_in d1 _) as Hdin'. inversion Hdin'; subst; simpl in *.
        repeat eexists. 3: pred_apply; cancel.
        3: left; reflexivity.  (* temp file still exists. *)
        right.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        admit.  (* prune ents *)

        intuition; subst.
        repeat eexists. 3: pred_apply; cancel.
        3: right; left.  (* temp file is gone *)
        3: rewrite update_subtree_root.
        right.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        admit.  (* prune ents *)
        admit.  (* prune is delete *)

        AFS.xcrash_solve.
        admit.  (* hash subset *)
        xform_deex_r. repeat xform_dist. cancel.
        denote! (d_in d0 _) as Hdin'. inversion Hdin'; subst; simpl in *; intuition.
        repeat eexists. 3: pred_apply; cancel.
        3: left; reflexivity.  (* temp file still exists. *)
        right.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        admit.  (* prune ents *)

        exfalso.
        edestruct DTCrash.tree_crash_find_name; intuition.
        3: eapply find_name_update_subtree_impossible; eassumption.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        eauto.

        exfalso.
        edestruct DTCrash.tree_crash_find_name; intuition.
        3: eapply find_name_update_subtree_impossible; eassumption.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        eauto.

        exfalso.
        edestruct DTCrash.tree_crash_find_name; intuition.
        3: eapply find_name_update_subtree_impossible; eassumption.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        eauto.

        exfalso.
        edestruct DTCrash.tree_crash_find_name; intuition.
        3: eapply find_name_update_subtree_impossible; eassumption.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        eauto.

        AFS.xcrash_solve.
        xform_deex_r. repeat xform_dist. cancel.
        denote! (d_in _ _) as Hdin''. inversion Hdin''; simpl in *; subst; intuition.
        repeat eexists. 3: pred_apply; cancel.
        3: left; reflexivity.  (* temp file still exists. *)
        right.
        repeat match goal with
        | [ H: DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _ |- _ ] => inversion H; clear H; subst
        end. eauto.
        admit.  (* prune ents *)

      + admit.
      + admit.

    - (* why is [setoid_rewrite] not doing the right thing? *)
      eapply crash_xform_pimpl_proper in Hcrashd; [ | apply diskIs_pred; eassumption ].
      apply crash_xform_sep_star_dist in Hcrashd.
      rewrite DTCrash.xform_tree_rep in Hcrashd.
      destruct_lift Hcrashd.
      denote DTCrash.tree_crash as Htc.
      intuition; subst.  (* 3 cases from the precondition.. *)
      + (* temp file is there *)
        apply DTCrash.tree_crash_update_subtree in Htc as Htc'; repeat deex; intuition.
        denote (DTCrash.tree_crash _ tree_crashed) as Htc_base; inversion Htc_base; subst.
        cancel.
        safestep.
        rewrite find_subtree_root.
        match goal with
        | [ |- Some ?t' = _ ] =>
          erewrite DIRTREE.dirtree_dir_parts with (t := t') by ( apply dirtree_isdir_update_subtree; auto );
          reflexivity
        end.

        (* our [delete_ok] should never fail.. *)
        destruct a2.
        2: admit.  (* need to eventually fix [delete_ok].. *)
        step.
        safestep.
        eapply DTCrash.tree_crash_trans; eauto.
        reflexivity.

        match goal with
        | [ |- ?t' = _ ] =>
          erewrite DIRTREE.dirtree_dir_parts with (t := t')
        end.
        rewrite DIRTREE.tree_prune_preserve_inum by reflexivity. reflexivity.
        rewrite DIRTREE.tree_prune_preserve_isdir by reflexivity. reflexivity.
        rewrite update_subtree_root.
        left.   (* dst not created yet *)
        unfold DIRTREE.tree_prune. rewrite update_subtree_root.

      (*
DIRTREE.delete_from_dir temp_fn
  (DIRTREE.TreeDir the_dnum
     (DIRTREE.dirtree_dirents
        (DIRTREE.update_subtree [temp_fn] subtree_crashed (DIRTREE.TreeDir the_dnum st')))) =
DIRTREE.delete_from_dir temp_fn (DIRTREE.TreeDir the_dnum st')
      *)
        admit.

        admit.

        AFS.xcrash_solve.
        admit. (* hash subset *)
        cancel. repeat xform_dist. cancel.

        denote! (d_in d1 _) as Hdin'. inversion Hdin'; subst; simpl in *.
        repeat eexists. 3: pred_apply; cancel.
        3: left; reflexivity.  (* temp file still exists. *)
        right.
        eapply DTCrash.tree_crash_trans; eauto.
        admit.  (* prune ents *)

        intuition; subst.
        repeat eexists. 3: pred_apply; cancel.
        3: right; left.  (* temp file is gone *)
        3: rewrite update_subtree_root.
        right.
        eapply DTCrash.tree_crash_trans; eauto.
        admit.  (* prune ents *)
        admit.  (* prune is delete *)

        AFS.xcrash_solve.
        admit.  (* hash subset *)
        xform_deex_r. repeat xform_dist. cancel.
        denote! (d_in d0 _) as Hdin'. inversion Hdin'; subst; simpl in *; intuition.
        repeat eexists. 3: pred_apply; cancel.
        3: left; reflexivity.  (* temp file still exists. *)
        right.
        eapply DTCrash.tree_crash_trans; eauto.
        admit.  (* prune ents *)

        exfalso.
        edestruct DTCrash.tree_crash_find_name as [sub1 ?]; intuition.
        3: edestruct DTCrash.tree_crash_find_name as [sub2 ?]; intuition.
        5: eapply find_name_update_subtree_impossible with (sub0 := sub2); eassumption.
        3: eauto.
        3: eassign sub1; eauto.
        eauto. eauto.

        exfalso.
        edestruct DTCrash.tree_crash_find_name as [sub1 ?]; intuition.
        3: edestruct DTCrash.tree_crash_find_name as [sub2 ?]; intuition.
        5: eapply find_name_update_subtree_impossible with (sub0 := sub2); eassumption.
        3: eauto.
        3: eassign sub1; eauto.
        eauto. eauto.

        exfalso.
        edestruct DTCrash.tree_crash_find_name as [sub1 ?]; intuition.
        3: edestruct DTCrash.tree_crash_find_name as [sub2 ?]; intuition.
        5: eapply find_name_update_subtree_impossible with (sub0 := sub2); eassumption.
        3: eauto.
        3: eassign sub1; eauto.
        eauto. eauto.

        exfalso.
        edestruct DTCrash.tree_crash_find_name as [sub1 ?]; intuition.
        3: edestruct DTCrash.tree_crash_find_name as [sub2 ?]; intuition.
        5: eapply find_name_update_subtree_impossible with (sub0 := sub2); eassumption.
        3: eauto.
        3: eassign sub1; eauto.
        eauto. eauto.

        AFS.xcrash_solve.
        xform_deex_r. repeat xform_dist. cancel.
        denote! (d_in _ _) as Hdin''. inversion Hdin''; simpl in *; subst; intuition.
        repeat eexists. 3: pred_apply; cancel.
        3: left; reflexivity.  (* temp file still exists. *)
        right.
        eapply DTCrash.tree_crash_trans; eauto.
        admit.  (* prune ents *)
      + admit.
      + admit.
    - AFS.xcrash_solve.
      cancel. repeat xform_dist. cancel.
      apply crash_xform_pimpl.
      apply LOG.before_crash_idempred.
      eauto.
  Admitted.



 (* USELESS STUFF...

        safestep.
        safestep.

        erewrite update_update_subtree_eq; eauto. admit. constructor.

        xform_deex_r.
        rewrite LOG.idempred_idem.
        norml; unfold stars; simpl.
        rewrite SB.crash_xform_rep.



      unfold LOG.after_crash.
      cancel.



      rewrite dirtree_inum_update_subtree.
      apply DTCrash.tree_crash_update_subtree in Htc; repeat deex; intuition.
      rewrite dirtree_isdir_update_subtree. denote (DTCrash.tree_crash _ tree_crashed) as H'; inversion H'; auto.
      


    cancel.
    step.
    rewrite find_subtree_root. eauto.
    step.
    prestep. safecancel.

    

    instantiate (2 := nil). simpl.

    step.
*)

  Hint Extern 1 ({{_}} progseq (recover) _) => apply atomic_cp_recover_ok : prog.


  Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
    (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.
  Proof.
    reflexivity.
  Qed.


  Theorem atomic_cp_with_recover_ok : forall fsxp src_inum tinum dst_fn mscs,
    {<< d Fm Ftop temp_tree src_fn file tfile v0 ilist freeblocks tree_elem,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm * 
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree ilist freeblocks) ]]] *
      [[ temp_tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
      [[ DIRTREE.dirtree_inum temp_tree = the_dnum ]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[ dst_fn <> temp_fn ]] *
      [[ dst_fn <> src_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists d tree' ilist' freeblocks' dstents,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freeblocks') ]]] *
      (([[r = false ]] *
        (exists f',
        [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum f') temp_tree ]])) \/
       ([[r = true ]] *
        let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
        let pruned := DIRTREE.tree_prune the_dnum tree_elem [] temp_fn temp_tree in
        [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
        [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]]))
    REC:hm' RET:^(mscs',fsxp')
      [[ fsxp' = fsxp ]] *
      exists d Fm' Ftop' tree' ilist' freeblocks' temp_tree_crash temp_dents dstents,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[[ d ::: (Fm' * DIRTREE.rep fsxp Ftop' tree' ilist' freeblocks') ]]] *
      [[ DTCrash.tree_crash temp_tree temp_tree_crash ]] *
      [[ temp_tree_crash = DIRTREE.TreeDir the_dnum temp_dents ]] *
      let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
      let pruned := DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree_crash in
      ([[ tree' = pruned ]] \/
       [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
       [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]])
    >>} copy_and_rename fsxp src_inum tinum dst_fn mscs >> recover.
  Proof.
    AFS.recover_ro_ok.
    cancel.
    eauto. 
    eauto.
    eauto.
    congruence.
    eauto.

    step.
    apply instantiate_crash.
    reflexivity.

    cancel.
    match goal with
    | [ H : crash_xform ?realcrash =p=> crash_xform ?body |- ?realcrash =p=> (_ hm') ] =>
      let t := eval pattern hm' in body in
      match eval pattern hm' in body with
      | ?bodyf hm' =>
        instantiate (1 := (fun hm' => (exists p, p * [[ crash_xform p =p=> crash_xform (bodyf hm') ]])%pred))
      end
    end.
    cancel.

    (**
     * Need to fish out the [p] which is really [realcrash] from above.
     *)
    simpl.
    repeat xform_dist.
    xform_deex_l.
    norml. unfold stars; simpl.
    repeat xform_dist.
    norml. unfold stars; simpl.
    rewrite H16.

    (**
     * We now have 2 OR cases on the left-hand side.  We need to break them up into
     * separate subgoals before instantiating the evars for the right-hand side, because
     * the evars will be different in each OR case.
     *)
    xform_deex_l.
    norml; unfold stars; simpl.
    repeat xform_dist.
    norml; unfold stars; simpl.
    2: xform_deex_l.
    2: norml; unfold stars; simpl.
    2: xform_deex_l.
    2: norml; unfold stars; simpl.
    2: xform_deex_l.
    2: norml; unfold stars; simpl.
    2: xform_deex_l.
    2: norml; unfold stars; simpl.
    2: xform_deex_l.
    2: norml; unfold stars; simpl.
    2: xform_deex_l.
    2: norml; unfold stars; simpl.
    2: repeat xform_dist.
    2: norml; unfold stars; simpl.

    - AFS.recover_ro_ok.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.

      cancel.
      eauto.
      eassign (v3); eauto.  (* src_fn *)

      denote (forall _, d_in _ _ -> _) as Hd. edestruct Hd; repeat deex. destruct x1; eauto.
      repeat eexists.
      3: pred_apply; cancel.
      left; reflexivity.  (* going into recovery, we have a non-crashed tree *)
      match goal with
      | [ |- ?t' = _ ] =>
        erewrite DIRTREE.dirtree_dir_parts with (t := t')
      end.
      rewrite DIRTREE.tree_prune_preserve_inum by reflexivity. reflexivity.
      rewrite DIRTREE.tree_prune_preserve_isdir by reflexivity. reflexivity.

      left; reflexivity.  (* temp file still exists, and no dst; first of 3 cases in recover's pre *)

      prestep.
      norml; unfold stars; simpl.
      intuition.
      (* consider two cases from [recover]'s postcondition: either [dst] exists, or it doesn't *)
      + norm; unfold stars; simpl.
        cancel.
        or_l; cancel.
        intuition.
        pred_apply; cancel.
        eauto.

        norm; unfold stars; simpl.
        cancel.
        auto.

      + norm; unfold stars; simpl.
        cancel.
        or_r; cancel.
        2: intuition.
        3: eauto.
        2: pred_apply; cancel.
        eauto.

        norm; unfold stars; simpl.
        cancel.
        auto.

      + norm; unfold stars; simpl.
        cancel.
        (* [intuition] should solve, but it's too slow *)  admit.

    - AFS.recover_ro_ok.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.

      cancel.
      eauto.
      eassign (v3); eauto.  (* src_fn *)

      (* Consider two cases: either we managed to flush the txn with [dst] in place,
       * or we didn't. *)
      denote! (d_in _ _) as Hdin.
      edestruct (d_in_pushd Hdin); subst.

      (* case 1: the rename made it to disk *)
      repeat eexists.
      3: pred_apply; cancel.
      left; reflexivity.
      eauto.
      right; right; reflexivity.

      (* case 2: the rename didn't make it to disk *)
      denote! (forall _, d_in _ _ -> _) as Hd. edestruct Hd; repeat deex. eassumption.
      repeat eexists.
      3: pred_apply; cancel.
      left; reflexivity.  (* going into recovery, we have a non-crashed tree *)
      match goal with
      | [ |- ?t' = _ ] =>
        erewrite DIRTREE.dirtree_dir_parts with (t := t')
      end.
      rewrite DIRTREE.tree_prune_preserve_inum by reflexivity. reflexivity.
      rewrite DIRTREE.tree_prune_preserve_isdir by reflexivity. reflexivity.

      left; reflexivity.  (* temp file still exists, and no dst; first of 3 cases in recover's pre *)

      prestep.
      norml; unfold stars; simpl.
      intuition.
      (* consider two cases from [recover]'s postcondition: either [dst] exists, or it doesn't *)
      + norm; unfold stars; simpl.
        cancel.
        or_l; cancel.
        intuition.
        pred_apply; cancel.
        eauto.

        norm; unfold stars; simpl.
        cancel.
        auto.

      + norm; unfold stars; simpl.
        cancel.
        or_r; cancel.
        2: intuition.
        3: eauto.
        2: pred_apply; cancel.
        eauto.

        norm; unfold stars; simpl.
        cancel.
        auto.

      + norm; unfold stars; simpl.
        cancel.
        split. auto. split. auto.
        rewrite H0.
        xform_norm. xform_normr. cancel.
        xform_normr. cancel.

        denote! (forall _, d_in _ x -> _) as Hds; edestruct Hds; eauto; repeat deex.
        all: try match goal with 
              | [ H : DIRTREE.TreeDir _ _ = DIRTREE.TreeDir _ _  |- _ ] => inversion H; subst
             end.
        all: repeat eexists.
        all: pred_apply; cancel.

        Search subtree.

        
  Admitted.

(*
      destruct v.
      prestep.
      norml; unfold stars; simpl.

      (**
       * We need to consider two cases: that [d_from_ds] from [atomic_cp_recover_ok]'s crash condition
       * (as instantiated based on the first OR of [copy_rename_ok]'s crash condition) falls in the
       * [dlist] portion, or if it falls in the [ds] portion..
       *)
      rewrite pushdlist_app in *.
      edestruct d_in_app.
      eassumption.

      + (**
         * This is the case when the post-crash disk state fell in the [dlist] portion of
         * [copy_rename_ok]'s crash condition.
         *)

        (**
         * First, we need to destruct the [exists] from the postcondition of [recover],
         * which is hidden under a [forall].  But to satisfy the premise of the [forall],
         * we need to destruct some more existentials under the [Forall] about the [dlist]
         * from [atomic_cp_recover_ok]'s crash condition..
         *)
        rewrite Forall_forall in *.
        rewrite <- in_rev in *.
        specialize (H12 _ H13).
        repeat deex.

        edestruct H19; repeat deex.
        eauto.

        (*
          DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') v2 =
          DIRTREE.TreeDir ?the_dnum ?temp_dents
         *)
        admit.

        safecancel.
        or_l. cancel.
        apply latest_in_ds.
        eauto.

        (* v2 = DIRTREE.TreeDir the_dnum ?temp_dents *)
        admit.

        (*
          DIRTREE.tree_prune ?the_dnum ?temp_dents [] temp_fn
            (DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') v2) =
          DIRTREE.tree_prune the_dnum ?temp_dents [] temp_fn v2
         *)
        admit.

        norml; unfold stars; simpl.
        safecancel.

      + (**
         * This is the case when the post-crash disk state fell in the [ds] portion of
         * [copy_rename_ok]'s crash condition.
         *)

        (**
         * First, we need to destruct the [exists] from the postcondition of [recover],
         * which is hidden under a [forall].
         *)
        edestruct H19; repeat deex.

        (* XXX need a precondition that all disks in [ds] look like a tree! *)
        (* (?Fm ✶ DIRTREE.rep fsxp ?Ftop ?tree)%pred (list2nmem d_from_ds) *)
        admit.

        reflexivity.

        safecancel.
        or_l. cancel.
        eauto.

        (* XXX again, [ds] disks must look like a tree *)
        (* (?Fm ✶ DIRTREE.rep fsxp ?Ftop ?tree)%pred (list2nmem d_from_ds) *)
        admit.

        reflexivity.
        reflexivity.

        norml; unfold stars; simpl.
        safecancel.

      + (* idempotence *)
        destruct v. rewrite pushdlist_app.
        norm.
        cancel.
        intuition idtac.
        apply crash_xform_pimpl.
        rewrite LOG.after_crash_idempred.
        norm; unfold stars; simpl.
        rewrite pushdlist_app.
        cancel.
        eauto.

    - (* This is the second [or] from [copy_and_rename]'s crash condition,
       * where we crashed after a flush and possibly more temp file writes.
       *)
      AFS.recover_ro_ok.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

      prestep.
      norml; unfold stars; simpl.

      (* To prove our recovery condition is satisfies, we must construct a tree.
       * This comes from the [forall] that came out of [recover]'s postcondition.
       * And for that, we need to show that the disk we got from [copy_and_rename]'s
       * crash condition also looked like a tree.  That disk was part of [dlist],
       * and that fact is inside a [Forall] from [copy_and_rename]'s crash condition.
       * Fish them out in the reverse order, to properly instantiate evars later..
       *)
      rewrite Forall_forall in *.
      edestruct H12; repeat deex.
      apply d_in_In; eassumption.

      edestruct H19; repeat deex.
      eassumption.

      (*
        DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') v2 =
        DIRTREE.TreeDir ?the_dnum0 ?temp_dents2
       *)
      admit.

      cancel.
      or_l. cancel.

      (*
        DIRTREE.tree_prune ?the_dnum0 ?temp_dents2 [] temp_fn
          (DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') v2) =
        DIRTREE.tree_prune the_dnum ?temp_dents1 [] temp_fn (DIRTREE.TreeDir the_dnum ?temp_dents1)
       *)
      admit.

      apply latest_in_ds.
      pred_apply.

      (*
        v0 ✶ DIRTREE.rep fsxp v1 v2 ⇨⇨
        ?Fm'0 ✶ DIRTREE.rep fsxp ?Ftop'1 (DIRTREE.TreeDir the_dnum ?temp_dents1)
       *)
      admit.

      norml; unfold stars; simpl.
      safecancel.

      (* idempotence *)
      norm.
      cancel.
      intuition idtac.
      apply crash_xform_pimpl.
      rewrite LOG.after_crash_idempred.
      cancel.

    - (* This is the third [or] from [copy_and_rename]'s crash condition,
       * where we actually wrote the destination file (but maybe didn't sync yet).
       *)
      AFS.recover_ro_ok.
      rewrite LOG.intact_idempred.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

      prestep.
      norml; unfold stars; simpl.

      (**
       * We have to consider two cases.  Either we crashed in the final disk,
       * where the [rename] succeeded, or we crashed before that, where we're
       * still in the [dlist] portion.
       *)
      apply d_in_In in H22.
      destruct H22; subst.

      + (* This is the case where [rename] succeeded. *)
        edestruct H21; repeat deex.
        eassumption.

        (*
          DIRTREE.tree_graft the_dnum x8 [] dst_fn (DIRTREE.TreeFile v5 (BFILE.synced_file v4))
            (DIRTREE.tree_prune the_dnum x7 [] temp_fn (DIRTREE.TreeDir the_dnum x7)) =
          DIRTREE.TreeDir ?the_dnum1 ?temp_dents3
         *)
        admit.

        cancel.
        or_r. cancel.

        (*
          DIRTREE.tree_prune ?the_dnum1 ?temp_dents3 [] temp_fn
            (DIRTREE.tree_graft the_dnum x8 [] dst_fn (DIRTREE.TreeFile v5 (BFILE.synced_file v4))
               (DIRTREE.tree_prune the_dnum x7 [] temp_fn (DIRTREE.TreeDir the_dnum x7))) =
          DIRTREE.tree_graft the_dnum ?dstents [] dst_fn (DIRTREE.TreeFile v5 (BFILE.synced_file v4))
            (DIRTREE.tree_prune the_dnum ?temp_dents2 [] temp_fn (DIRTREE.TreeDir the_dnum ?temp_dents2))
         *)
        admit.

        (*
          DIRTREE.tree_prune the_dnum ?temp_dents2 [] temp_fn (DIRTREE.TreeDir the_dnum ?temp_dents2) =
          DIRTREE.TreeDir the_dnum ?dstents
         *)
        admit.

        apply latest_in_ds.
        pred_apply. cancel.

        norml; unfold stars; simpl.
        safecancel.

      + (* This is the case where [rename] did not succeed. *)
        rewrite Forall_forall in H12.
        specialize (H12 _ H14).
        repeat deex.

        edestruct H21; repeat deex.
        eauto.

        (*
          DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') (DIRTREE.TreeDir the_dnum x7) =
          DIRTREE.TreeDir ?the_dnum2 ?temp_dents4
         *)
        admit.

        cancel.
        or_l. cancel.

        (*
          DIRTREE.tree_prune ?the_dnum2 ?temp_dents4 [] temp_fn
            (DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') (DIRTREE.TreeDir the_dnum x7)) =
          DIRTREE.tree_prune the_dnum ?temp_dents2 [] temp_fn (DIRTREE.TreeDir the_dnum ?temp_dents2)
         *)
        f_equal.
        (*
          DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile v5 tfile') (DIRTREE.TreeDir the_dnum x7) =
          DIRTREE.TreeDir the_dnum ?temp_dents4
         *)
        admit.

        apply latest_in_ds.
        pred_apply. cancel.

        norml; unfold stars; simpl.
        safecancel.

      + (* idempotence *)
        norm.
        cancel.
        intuition idtac.
        rewrite LOG.after_crash_idempred.
        xform_deex_r.
        repeat xform_dist.
        norm; unfold stars; simpl.
        2: intuition eauto.
        or_r.
        xform_deex_r.
        norm; unfold stars; simpl.
        xform_deex_r.
        xform_dist.
        or_r.
        repeat xform_deex_r.
        repeat xform_dist.
        cancel.

        all: admit.

  Admitted.
*)

End ATOMICCP.
