Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
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
Require Import DirUtil.
Require Import String.
Require Import TreeCrash.


Import ListNotations.

Set Implicit Arguments.

(**
 * Atomic copy: create a copy of file [src_fn] in the root directory [the_dnum],
 * with the new file name [dst_fn].
 *
 *)



Module ATOMICCP.

  Parameter the_dnum : addr.

  Definition temp_fn := ".temp"%string.
  
  (** Programs **)

  (* copy an existing src into an existing, empty dst. *)

  Definition copydata T fsxp src_inum dst_inum mscs rx : prog T :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, b) <- AFS.read_fblock fsxp src_inum 0 mscs;
    let^ (mscs) <- AFS.update_fblock_d fsxp dst_inum 0 b mscs;
    let^ (mscs, ok) <- AFS.file_set_attr fsxp dst_inum attr mscs;
    let^ (mscs) <- AFS.file_sync fsxp dst_inum mscs;
    rx ^(mscs, ok).

  Definition copy2temp T fsxp src_inum dst_inum mscs rx : prog T :=
    let^ (mscs, ok) <- AFS.file_truncate fsxp dst_inum 1 mscs;  (* XXX type error when passing sz *)
    If (bool_dec ok true) {
      let^ (mscs, ok) <- copydata fsxp src_inum dst_inum mscs;
      rx ^(mscs, ok)
    } else {
      rx ^(mscs, ok)
    }.

  Definition copy_and_rename T fsxp src_inum dst_inum dst_fn mscs rx : prog T :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum dst_inum mscs;
    match ok with
      | false =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        (* Just for a simpler spec: the state is always (d, nil) after this function *)
        rx ^(mscs, false)
      | true =>
        let^ (mscs, ok1) <- AFS.rename fsxp the_dnum [] temp_fn [] dst_fn mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        rx ^(mscs, ok1)
    end.

  Definition atomic_cp T fsxp src_inum dst_fn mscs rx : prog T :=
    let^ (mscs, maybe_dst_inum) <- AFS.create fsxp the_dnum temp_fn mscs;
    match maybe_dst_inum with
      | None => rx ^(mscs, false)
      | Some dst_inum =>
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum dst_inum dst_fn mscs;
        rx ^(mscs, ok)
    end.

  (** recovery programs **)

  (* atomic_cp recovery: if temp_fn exists, delete it *)
  Definition cleanup {T} fsxp mscs rx : prog T :=
    let^ (mscs, maybe_src_inum) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
    match maybe_src_inum with
    | None => rx mscs
    | Some (src_inum, isdir) =>
      let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
      let^ (mscs) <- AFS.tree_sync fsxp mscs;
      rx mscs
    end.

  (* top-level recovery function: call AFS recover and then atomic_cp's recovery *)
  Definition recover {T} rx : prog T :=
    let^ (mscs, fsxp) <- AFS.recover;
    let^ (mscs, maybe_src_inum) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
    match maybe_src_inum with
    | None => rx ^(mscs, fsxp)
    | Some (src_inum, isdir) =>
      let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
      let^ (mscs) <- AFS.tree_sync fsxp mscs;
      rx ^(mscs, fsxp)
    end.

  (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.

  Lemma arrayN_one: forall V (v:V),
      0 |-> v <=p=> arrayN 0 [v].
  Proof.
    split; cancel.
  Qed.

  Lemma arrayN_ex_one: forall V (l : list V),
      List.length l = 1 ->
      arrayN_ex l 0 <=p=> emp.
  Proof.
    destruct l.
    simpl; intros.
    congruence.
    destruct l.
    simpl. intros.
    unfold arrayN_ex.
    simpl.
    split; cancel.
    simpl. intros.
    congruence.
  Qed.

  Ltac xcrash_norm :=  repeat (xform_norm; cancel).
  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Theorem copydata_ok : forall fsxp src_inum tinum mscs,
    {< ds Fm Ftop temp_tree src_fn file tfile v0 t0 ilist freelist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree ilist freelist) ]]] *
      [[ forall d, d_in d ds -> exists tfile' ilist' freelist',
         let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree in
         (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freelist')%pred (list2nmem d) ]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]] *
      [[[ BFILE.BFData tfile ::: (0 |-> t0) ]]]
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
     >} copydata fsxp src_inum tinum mscs.
  Proof.
    unfold copydata; intros.
    step.
    2: AFS.xcrash_solve; xform_norm; cancel; xform_norm; safecancel.
    step.
    2: AFS.xcrash_solve; xform_norm; cancel; xform_norm; safecancel.
    step.

    Focus 2.  (* update_fblock_d crash condition *)
    AFS.xcrash_solve.
    xform_norm; cancel; xform_norm; safecancel.
    xform_norm; cancel; xform_norm; safecancel.

    inversion H12; subst; simpl in *; try intuition.
    edestruct DIRTREE.dirtree_update_safe.
    2: eauto.
    4: intuition; subst.
    4: repeat eexists; eauto.
    4: repeat eexists.
    4: erewrite DIRTREE.dirtree_update_inode_update_subtree in H16.
    4: erewrite update_update_subtree_eq in H16.
    4: eauto.
    4: admit.
    4: eauto.
    4: constructor.
    4: admit.
    4: admit.
    4: erewrite DIRTREE.find_update_subtree; eauto.
    4: admit.
    3: admit.  (* update_subtree putting back what was already there.. *)
    2: apply DIRTREE.dirtree_safe_refl.
    erewrite DIRTREE.find_update_subtree; eauto.

    (* XXX crash_xform oldest *)
    xform_norm; cancel; xform_norm; safecancel.
    inversion H12; subst; simpl in *; try intuition.
    edestruct DIRTREE.dirtree_update_safe.
    2: eauto.
    4: intuition; subst.
    4: repeat eexists; eauto.
    4: repeat eexists.
    4: erewrite DIRTREE.dirtree_update_inode_update_subtree in H16.
    4: erewrite update_update_subtree_eq in H16.
    4: eauto.
    4: admit.
    4: eauto.
    4: constructor.
    4: admit.
    4: admit.
    4: erewrite DIRTREE.find_update_subtree; eauto.
    4: admit.
    (* XXX 3 is broken!  we need a different file in (fst ds)... *)
    3: admit.
    2: apply DIRTREE.dirtree_safe_refl.
    erewrite DIRTREE.find_update_subtree; eauto.

    step.
    2: AFS.xcrash_solve; xform_norm; cancel; xform_norm; safecancel.
    2: admit.   (* we can't reuse the big [forall], because instead of [ds], we have [dsupd ... ds] *)

    step.
    step.

    admit. (* crash condition *)

    step.

    admit. (* crash condition *)
  Admitted.

(*
    simpl; eauto.
    admit.

    intuition.
    xcrash_norm.
    instantiate (x := nil).
    or_l.
    simpl.
    cancel.
    apply Forall_nil.
    xcrash_norm.  (* right branch of or *)
    or_r.
    xcrash_norm.
    eapply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply.
    cancel.
    apply Forall_nil.

    step.  (* setattr *)

    Focus 2.  (* setattr failed crash condition*)
    AFS.xcrash_solve.
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply.
    cancel.
    apply Forall_nil.
   
    step. (* file_sync *)
    step. (* return *)
    
    (* postcondition, setattr failed *)
    or_l.
    cancel.
    erewrite update_update_subtree_eq.
    f_equal.

    (* setattr success crash condition: two cases *)
    (* left or case *)
    AFS.xcrash_solve.
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply.
    cancel.
    apply Forall_nil.
    (* right or case *)
    AFS.xcrash_solve.
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply.
    erewrite update_update_subtree_eq.
    cancel.
    apply Forall_nil.

    (* postcondition, success *)
    step.
    or_r.
    safecancel.
    erewrite update_update_subtree_eq.
    erewrite update_update_subtree_eq.
    f_equal.
    apply arrayN_one in H5.
    apply list2nmem_array_eq in H5.
    apply arrayN_one in H16.
    apply list2nmem_array_eq in H16.
    destruct file.
    rewrite H16.
    simpl in H5.
    rewrite H5.
    f_equal.

    AFS.xcrash_solve.  (* crash condition file_sync *)
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    simpl.
    pred_apply.
    cancel.
    simpl.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply.
    erewrite update_update_subtree_eq.
    cancel.
    apply Forall_nil.

    AFS.xcrash_solve. (* crash condition file_sync or right *)
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply.
    cancel.
    erewrite update_update_subtree_eq.
    erewrite update_update_subtree_eq.
    cancel.
    apply Forall_nil.
    
    AFS.xcrash_solve.  (* crash condition read_fblock *)
    repeat (xform_norm; cancel).
    or_l.
    instantiate (x := []); simpl.
    cancel.
    apply Forall_nil.

    AFS.xcrash_solve.  (* crash condition file_get_attr *)
    repeat (xform_norm; cancel).
    or_l.
    instantiate (x := nil); simpl.
    cancel.
    apply Forall_nil.
    
    Unshelve. all: eauto.
  Qed.
*)

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
    repeat eexists. pred_apply. cancel.
    rewrite update_subtree_same. cancel. admit. eauto.
    step.
    denote d_in as Hdin. inversion Hdin; clear Hdin; simpl in *; subst.
    repeat eexists. pred_apply. cancel.
    erewrite update_update_subtree_eq; eauto.
    erewrite update_subtree_same. cancel. admit. eauto. admit. constructor.
    intuition; subst. (* the other part of [d_in] *)
    repeat eexists. pred_apply. cancel.
    erewrite update_update_subtree_eq; eauto.
    admit. constructor.
    rewrite find_subtree_update_subtree_ne. eauto. eauto. eauto.

    apply setlen_singleton_ptsto.
    step.
    denote (d_in _ _ -> _) as Hdpred.
    edestruct Hdpred; eauto. repeat deex.
    repeat eexists. pred_apply.
    erewrite update_update_subtree_eq; eauto. admit. constructor.
    or_r. cancel.
    erewrite update_update_subtree_eq; eauto. admit. constructor.
    denote (d_in _ _ -> _) as Hdpred.
    edestruct Hdpred; eauto. repeat deex.
    repeat eexists. pred_apply.
    erewrite update_update_subtree_eq; eauto. admit. constructor.

    AFS.xcrash_solve. xform_norm; cancel. xform_norm; safecancel.
    denote (d_in _ _ -> _) as Hdpred.
    edestruct Hdpred; eauto. repeat deex.
    repeat eexists. pred_apply.
    erewrite update_update_subtree_eq; eauto. admit. constructor.

    step.

    AFS.xcrash_solve; xform_norm; cancel; xform_norm; safecancel.
    denote d_in as Hdin. inversion Hdin; simpl in *; subst; [ | exfalso; eauto ].
    repeat eexists. pred_apply.
    erewrite update_subtree_same. cancel. admit. eauto.

    denote d_in as Hdin. inversion Hdin; simpl in *; subst.
    repeat eexists. pred_apply.
    erewrite update_subtree_same. cancel. admit. eauto.

    intuition; subst.
    repeat eexists. pred_apply.
    cancel.
  Admitted.

  Hint Extern 1 ({{_}} progseq (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Theorem copy_rename_ok : forall  fsxp src_inum tinum dst_fn mscs,
    {< d Fm Ftop temp_tree src_fn file tfile v0 ilist freeblocks,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm * 
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree ilist freeblocks) ]]] *
      [[ DIRTREE.dirtree_inum temp_tree = the_dnum ]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[ dst_fn <> temp_fn ]] *
      [[ dst_fn <> src_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists d tree' ilist' freeblocks' temp_dents dstents,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freeblocks') ]]] *
      (([[r = false ]] *
        (exists f',
        [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum f') temp_tree ]])) \/
       ([[r = true ]] *
        [[ temp_tree = DIRTREE.TreeDir the_dnum temp_dents ]] *
        let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
        let pruned := DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree in
        [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
        [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]]))
    XCRASH:hm'
      exists ds_temps,
      [[ forall d, d_in d ds_temps -> exists tfile' ilist' freelist',
         let tree' := DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum tfile') temp_tree in
         (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freelist')%pred (list2nmem d) ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds_temps hm' \/
      exists d' tree' ilist' frees' temp_dents dstents,
      [[[ d' ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d' ds_temps) hm' *
      [[ temp_tree = DIRTREE.TreeDir the_dnum temp_dents ]] *
      let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
      let pruned := DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree in
      [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
      [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]]
     >} copy_and_rename fsxp src_inum tinum dst_fn mscs.
  Proof.
    unfold copy_and_rename, AFS.rename_rep; intros.
    step.
    step.

    rewrite find_subtree_nil.
    rewrite (DIRTREE.dirtree_dir_parts (DIRTREE.update_subtree _ _ _)).
    f_equal. f_equal. eauto. eauto.

    unfold AFS.rename_rep.
    safestep.
    step.
    AFS.xcrash_solve.
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists.
    eexists.
    intuition.
    pred_apply. cancel.
    apply Forall_nil.
    step.
    or_r.
    cancel.
    admit.
    admit.
    admit.
    
    AFS.xcrash_solve.
    xcrash_norm.
    or_r.
    xcrash_norm.
    simpl.
    constructor.
    eexists. eexists. intuition.
    eassumption.
    constructor.
    eexists. eexists. intuition.
    pred_apply. cancel.
    admit.
    apply Forall_nil.
    
    AFS.xcrash_solve.
    xcrash_norm.
    or_r.
    xcrash_norm.
    apply Forall_cons.
    eexists. eexists. intuition.
    pred_apply. cancel.
    apply Forall_nil.

    AFS.xcrash_solve.
    xcrash_norm.
    xcrash_norm.
    or_r.
    xcrash_norm.
    eauto.
    Unshelve. all: eauto.
  Admitted.

  Hint Extern 1 ({{_}} progseq (copy_and_rename _ _ _ _ _) _) => apply copy_rename_ok : prog.

  (* specs for copy_and_rename_cleanup and atomic_cp *)

  Theorem atomic_cp_recover_ok :
    {< fsxp cs ds base_tree temp_dents src_fn src_inum dst_fn file old_temp,
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ base_tree = DIRTREE.TreeDir the_dnum temp_dents ]] *
      [[ DIRTREE.find_subtree [temp_fn] base_tree = Some old_temp ]] *
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
      exists d tree_after_crash temp_dents_after_crash dstents tree' Fm' Ftop' ilist' frees' dst_inum,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) hm' *
      [[ DTCrash.tree_crash base_tree tree_after_crash ]] *
      [[ tree_after_crash = DIRTREE.TreeDir the_dnum temp_dents_after_crash ]] *
      let tree'prune := DIRTREE.tree_prune the_dnum temp_dents_after_crash [] temp_fn tree_after_crash in
      let dst_subtree := DIRTREE.TreeFile dst_inum (BFILE.synced_file file) in
      let tree'dst := DIRTREE.tree_graft the_dnum dstents [] dst_fn dst_subtree tree' in
      [[ tree'prune = DIRTREE.TreeDir the_dnum dstents ]] *
      [[[ d ::: Fm' * DIRTREE.rep fsxp Ftop' tree' ilist' frees' ]]] *
      [[ tree' = tree'prune \/ tree' = tree'dst ]]
    XCRASH:hm'
      exists ds',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ forall d, d_in d ds' ->
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

Transparent DIRTREE.find_name.
Lemma find_name_update_subtree_impossible : forall fn sub inum ents sub0,
  None = DIRTREE.find_name [fn] (DIRTREE.update_subtree [fn] sub (DIRTREE.TreeDir inum ents)) ->
  DIRTREE.find_subtree [fn] (DIRTREE.TreeDir inum ents) = Some sub0 ->
  False.
Proof.
  unfold DIRTREE.find_name; intros.
  erewrite DIRTREE.find_update_subtree in *.
  destruct sub; congruence.
  eauto.
  admit.  (* unnecessary premise, see [find_update_subtree] *)
Admitted.

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

  Admitted.

  Hint Extern 1 ({{_}} progseq (recover) _) => apply atomic_cp_recover_ok : prog.

  Theorem atomic_cp_with_recover_ok : forall fsxp src_inum dst_fn mscs,
    {<< d Fm Ftop temp_tree src_fn file tfile v0 ilist freeblocks tinum,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm * 
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree ilist freeblocks) ]]] *
      [[ DIRTREE.dirtree_inum temp_tree = the_dnum ]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]] *
      [[ src_fn <> temp_fn ]] *
      [[ dst_fn <> temp_fn ]] *
      [[ dst_fn <> src_fn ]] *
      [[[ BFILE.BFData file ::: (0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists d tree' ilist' freeblocks' temp_dents dstents,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' freeblocks') ]]] *
      (([[ r = false ]] *
        (exists f',
        [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum f') temp_tree ]])) \/
       ([[ r = true ]] *
        [[ temp_tree = DIRTREE.TreeDir the_dnum temp_dents ]] *
        let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
        let pruned := DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree in
        [[ pruned = DIRTREE.TreeDir the_dnum dstents ]] *
        [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]]))
    REC:hm' RET:^(mscs',fsxp')
      [[ fsxp' = fsxp ]] *
      exists d Fm' Ftop' tree' ilist' freeblocks' temp_dents dstents,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[[ d ::: (Fm' * DIRTREE.rep fsxp Ftop' tree' ilist' freeblocks') ]]] *
      [[ temp_tree = DIRTREE.TreeDir the_dnum temp_dents ]] *
      let subtree := DIRTREE.TreeFile tinum (BFILE.synced_file file) in
      let pruned := DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree in
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
    congruence.
    step.
    apply AFS.instantiate_crash.
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
    rewrite H15.

    (**
     * We now have 3 OR cases on the left-hand side.  We need to break them up into
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
    2: repeat xform_dist.
    2: norml; unfold stars; simpl.
    3: xform_deex_l.
    3: norml; unfold stars; simpl.
    3: xform_deex_l.
    3: norml; unfold stars; simpl.
    3: xform_deex_l.
    3: norml; unfold stars; simpl.
    3: xform_deex_l.
    3: norml; unfold stars; simpl.
    3: xform_deex_l.
    3: norml; unfold stars; simpl.
    3: repeat xform_dist.
    3: norml; unfold stars; simpl.

    - AFS.recover_ro_ok.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

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

End ATOMICCP.
