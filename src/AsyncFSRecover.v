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
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import AsyncFS.

Set Implicit Arguments.
Import ListNotations.


Module AFS_RECOVER.

  Import AFS.
  Import DirTree.
  Import DirTreeDef.

  Parameter cachesize : nat.
  Axiom cachesize_ok : cachesize <> 0.
  Hint Resolve cachesize_ok.

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.


  Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {X<< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[ r = DFAttr f ]]
  REC:hm' RET:r exists mscs fsxp,
         exists d sm' n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
  >>X} file_get_attr fsxp inum mscs >> recover cachesize.
  Proof.
    unfold forall_helper.
    recover_ro_ok.
    destruct v.
    cancel.
    eauto.
    step.

    norm'l. unfold stars; simpl.
    cancel.
    eassign_idempred.

    simpl_idempred_l.
    xform_norml;
      rewrite SB.crash_xform_rep;
      (rewrite LOG.notxn_after_crash_diskIs || rewrite LOG.rollbacktxn_after_crash_diskIs);
      try eassumption.
    cancel.

    safestep; subst. 2: eauto.
    simpl_idempred_r.
    eauto.
    simpl_idempred_r.
    rewrite <- LOG.before_crash_idempred.
    cancel. auto.

    cancel.
    safestep; subst. 2:eauto.
    simpl_idempred_r.
    eauto.
    simpl_idempred_r.
    rewrite <- LOG.before_crash_idempred.
    cancel. auto.
  Qed.


  Theorem read_fblock_recover_ok : forall fsxp inum off mscs,
    {X<< ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm)]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep  fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[ r = fst vs ]]
    REC:hm' RET:r exists mscs fsxp,
         exists d sm' n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    >>X} read_fblock fsxp inum off mscs >> recover cachesize.
  Proof.
    unfold forall_helper.
    recover_ro_ok.
    destruct v.
    cancel.
    eauto.
    eauto.
    step.

    eassign_idempred.

    simpl_idempred_l.
    xform_norml;
      rewrite SB.crash_xform_rep;
      (rewrite LOG.notxn_after_crash_diskIs || rewrite LOG.rollbacktxn_after_crash_diskIs);
      try eassumption.
    cancel.
    safestep; subst.
    simpl_idempred_r.
    eauto.
    eauto.
    simpl_idempred_r.
    cancel.
    SepAuto.xcrash_rewrite.
    cancel.
    rewrite LOG.before_crash_idempred.
    cancel.

    simpl_idempred_r; auto.
    safestep; subst.
    simpl_idempred_r.
    cancel.
    SepAuto.xcrash_rewrite.
    rewrite LOG.before_crash_idempred.
    cancel.
  Qed.


  Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
    (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.
  Proof.
    reflexivity.
  Qed.

(* 
  Theorem file_truncate_recover_ok : forall fsxp inum sz mscs,
    {<< ds sm Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs', r)
      [[ isError r ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' \/
      [[ r = OK tt ]] * exists d tree' f' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[[ d ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]]
    REC:hm' RET:r exists mscs fsxp,
      (exists d sm' n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]) \/
      (exists d dnew n sm' ds' tree' f' ilist' frees',
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
         [[ n <= length (snd ds') ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds'))) ]]] *
         [[ ds' = pushd dnew ds ]] *
         [[[ dnew ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees' mscs sm')]]] *
         [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
         [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]])
     >>} file_truncate fsxp inum sz mscs >> recover cachesize.
  Proof.
    unfold forall_helper; intros.
    (* workaround an evar tracking bug by destructing before instantiating;
     otherwise proof goes through but at Qed time the variable d, produced from
     v, cannot be found. *)
    destruct v.
    eexists; intros.
    recover_ro_ok.
    cancel.
    eauto.
    safestep.  (* crucial to use safe version *)
    or_l.
    cancel. cancel.

    apply instantiate_crash.
    cancel.
    cancel.

    cancel.

    eassign_idempred.
    cancel.

    simpl.
    repeat xform_dist.
    repeat xform_deex_l.
    xform_dist.
    rewrite crash_xform_lift_empty.
    norml. unfold stars; simpl. rewrite H9.

    denote! (crash_xform F_ =p=> F_) as HFidem. rewrite HFidem.
    xform_dist. norml; unfold stars; simpl.
    - rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

      prestep. norm. cancel.
      or_l. norm. cancel. intuition eassumption.

      intuition eauto.
      apply sep_star_lift_l; intros; apply pimpl_refl.

      apply sep_star_lift_l; intros.
      norm; unfold stars; simpl.
      cancel.

      split. constructor.
      split. constructor.
      denote! (crash_xform realcrash =p=> crash_xform _) as Hcr.
      rewrite Hcr; clear Hcr.

      rewrite <- LOG.before_crash_idempred. xform_dist. cancel.

    - xform_norm.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

      prestep. norm. cancel.
      or_r. norm. cancel. intuition idtac. 2: eauto. eauto. eauto.
(*
      pred_apply; cancel.

      intuition eauto.
      apply sep_star_lift_l; intros; apply pimpl_refl.

      apply sep_star_lift_l; intros.
      norm; unfold stars; simpl.
      cancel.

      split. constructor.
      split. constructor.
      denote! (crash_xform realcrash =p=> crash_xform _) as Hcr.
      rewrite Hcr; clear Hcr.

      xform_dist. or_r.
      repeat ( progress xform_norm; cancel ).
      rewrite <- LOG.before_crash_idempred.
      unfold pushd; simpl; cancel.

      pred_apply; cancel.
*)
  Grab Existential Variables.
    all: try exact emp.
  Qed. *)

(*   Theorem update_fblock_d_recover_ok : forall fsxp inum off v mscs,
    {<< ds sm Fm Ftop tree pathname f Fd vs frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists tree' f' ds' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[[ ds'!! ::: (Fm  * DirTreeRep.rep fsxp Ftop tree' ilist frees mscs' sm') ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]]
    REC:hm' RET:r exists mscs fsxp,
      exists d sm', LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
      ((exists n, 
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] ) \/
       (exists tree' f' v' ilist' frees',
        [[[ d ::: (crash_xform Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees' mscs sm)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[[ (DFData f') ::: (crash_xform Fd * off |=> v') ]]] *
        [[ DFAttr f' = DFAttr f ]] *
        [[ In v' (v :: vsmerge vs) ]]))
   >>} update_fblock_d fsxp inum off v mscs >> recover cachesize.
  Proof.
    recover_ro_ok. 
(*
    cancel.
    instantiate (pathname := v4); eauto.
    eauto.
    step.
    apply pimpl_refl.
*)
    (* follows one of the earlier recover proofs but isn't used by atomiccp. *)
  Abort.
 *)
 
  Hint Extern 0 (okToUnify (DirTreePred.tree_pred _ _) (DirTreePred.tree_pred _ _)) => constructor : okToUnify.

(*   Theorem file_sync_recover_ok : forall fsxp inum mscs,
    {<< ds sm Fm Ftop tree pathname f frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs')
      exists ds' sm' tree' al,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
        [[ ds' = dssync_vecs ds al ]] *
        [[[ ds'!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist frees mscs' sm')]]] *
        [[ tree' = update_subtree pathname (TreeFile inum (synced_dirfile f)) tree ]]
    REC:hm' RET:r exists mscs fsxp,
      exists d sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) sm' hm' *
       ((exists n,  [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]) \/
         exists flist' F',
         [[[ d ::: (F' * BFILE.rep (FSXPBlockAlloc fsxp) sm' (FSXPInode fsxp) flist' ilist frees
                                   (BFILE.MSAllocC mscs) (BFILE.MSCache mscs) (BFILE.MSICache mscs) (BFILE.MSDBlocks mscs)) ]]] *
         [[[ flist' ::: (arrayN_ex (@ptsto _ addr_eq_dec _) flist' inum *
                         exists c, inum |-> BFILE.synced_file (dirfile_to_bfile f c)) ]]]
       )
   >>} file_sync fsxp inum mscs >> recover cachesize.
  Proof.
    intros.
    recover_ro_ok.
    cancel. eauto.
    remember
    ( (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform
         (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v hm
      \/ (exists d tree',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, []) hm *
           [[[ d ::: v1 ✶ DirTreeRep.rep fsxp v2 tree' v7 (v6_1, v6_2) a v0 ]]] *
           [[ tree' = update_subtree v4 (TreeFile inum (synced_dirfile v5)) v3 ]])) ]]))%pred) as x.
    step.
    
    remember
    ( (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform
         (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v hm
      \/ (exists d tree',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, []) hm *
           [[[ d ::: v1 ✶ DirTreeRep.rep fsxp v2 tree' v7 (v6_1, v6_2) a v0 ]]] *
           [[ tree' = update_subtree v4 (TreeFile inum (synced_dirfile v5)) v3 ]])) ]]))%pred) as x.
    
    
    (* build a new idemcrash predicate that carries the XCRASH facts *)
    instantiate (1 :=  (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform
         (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v hm
      \/ (exists d tree',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, []) hm *
           [[[ d ::: v1 ✶ DirTreeRep.rep fsxp v2 tree' v7 (v6_1, v6_2) a v0 ]]] *
           [[ tree' = update_subtree v4 (TreeFile inum (synced_dirfile v5)) v3 ]])) ]]))%pred).
    apply pimpl_refl.
    cancel. xform_dist. cancel.
    simpl.
    repeat xform_dist.
    repeat xform_deex_l.
    xform_dist.
    rewrite crash_xform_lift_empty.
    norml. unfold stars; simpl. rewrite H9.
    xform_dist. xform_deex_l.

    - rewrite LOG.idempred_idem; xform_deex_l;
      rewrite SB.crash_xform_rep.
      cancel.

      prestep. norm. cancel.
      recover_ro_ok.
      cancel.
      instantiate (mscs0 := ms).
      cancel.
      or_l; cancel.
      setoid_rewrite <- surjective_pairing.
      cancel.

      intuition.
      cancel.

      simpl_idempred_r.
      or_l; cancel.
      rewrite <- LOG.before_crash_idempred.
      auto.

    - repeat xform_deex_l.
      repeat xform_dist.
      rewrite LOG.idempred_idem; xform_deex_l;
      rewrite SB.crash_xform_rep.
      cancel.

      step.
      denote crash_xform as Hx.
      replace n with 0 in Hx by omega; rewrite nthd_0 in Hx; simpl in Hx.
      denote! (_ (list2nmem x1)) as Hy.
      apply (crash_xform_diskIs_pred _ Hy) in Hx.
      apply crash_xform_sep_star_dist in Hx.

      (* unfold DirTreeRep.rep in Hx to extract the file list *)
      unfold DirTreeRep.rep in Hx; apply sep_star_comm in Hx.
      repeat (rewrite crash_xform_exists_comm in Hx;
        apply pimpl_exists_r_star_r in Hx;
        destruct Hx as [ ? Hx ]).
      repeat rewrite crash_xform_sep_star_dist in Hx.
      repeat rewrite crash_xform_lift_empty in Hx.
      rewrite BFILE.xform_rep, IAlloc.xform_rep in Hx.
      destruct_lift Hx.
      recover_ro_ok. cancel.
      instantiate (mscs0 := BFILE.mk_memstate _ (MSLL ms) _ _ _ _ _). cancel.
      or_r; cancel.

      eapply pimpl_apply; [| eapply DirTreePred.flist_crash_synced_file; eauto].
      cancel.
      pred_apply; cancel.

      simpl_idempred_r.
      or_r; cancel.
      do 3 (xform_norm; cancel).
      rewrite <- LOG.before_crash_idempred.
      eauto.

    Unshelve.
      all: eauto.
      all: solve [do 5 econstructor].
  Qed.
 *)
(*
  Theorem lookup_recover_ok : forall fsxp dnum fnlist mscs,
    {<< ds Fm Ftop tree ilist frees,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.dirtree_inum tree = dnum]] *
      [[ DIRTREE.dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs',r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ r = DIRTREE.find_name fnlist tree ]]
    REC:hm' RET:^(mscs, fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
       [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} lookup fsxp dnum fnlist mscs >> recover cachesize.
  Proof.
    recover_ro_ok.
    cancel.
    eauto.
    step.
    instantiate (1 := (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred).
    cancel; cancel.
    cancel.
    or_l.
    cancel.
    xform_norm.
    recover_ro_ok.
    rewrite LOG.crash_xform_intact.
    xform_norm.
    rewrite SB.crash_xform_rep.

    cancel.
    rewrite LOG.notxn_after_crash_diskIs. cancel.
    rewrite nthd_0; eauto. omega.

    safestep; subst.
    eassign d0; eauto.
    pred_apply; instantiate (1 := nil).
    replace n with 0 in *.
    rewrite nthd_0; simpl; auto.
    simpl in *; omega.

    cancel; cancel.
    rewrite LOG.after_crash_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    cancel; cancel.
  Qed.
*)

(*
  Theorem create_recover_ok : forall fsxp dnum name mscs,
    {<< ds pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
       [[ r = None ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm'
      \/ exists inum,
       [[ r = Some inum ]] * exists d tree' ilist' frees',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
       [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (TreeFile inum BFILE.bfile0) tree ]] *
       [[[ d ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees') ]]]
    REC:hm' RET:^(mscs,fsxp)
      exists d,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} create fsxp dnum name mscs >> recover cachesize.
  Proof.
    recover_ro_ok.
    cancel.
    eauto.
    safestep.
    or_l.
    cancel.
    subst.
    apply pimpl_refl.
    or_r.
    cancel.
    subst.
    apply pimpl_refl.

    (* if CRASH is LOG.idempred, we must manually instantiate idemcrash to include
       the after_crash case *)
    eassign ( LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    cancel; cancel.
    xform_norm; recover_ro_ok.

    - rewrite LOG.crash_xform_intact.
      xform_norm.
      rewrite SB.crash_xform_rep.
      rewrite LOG.notxn_after_crash_diskIs with (n := 0) (ds := (fst v, nil)); auto.
      cancel.
      safestep.
      cancel.
      pred_apply; subst.
      replace n with 0 by omega.
      rewrite nthd_0; eauto.
      cancel; cancel.

    - rewrite LOG.after_crash_idem.
      xform_norm.
      rewrite SB.crash_xform_rep.
      cancel.
      step.
      cancel; cancel.
  Qed.
*)

(*
  Theorem rename_recover_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {<< ds Fm Ftop tree cwd tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * DirTreeRep.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',ok)
      [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' \/
      [[ ok = true ]] * 
        rename_rep ds mscs' Fm fsxp Ftop tree ilist frees cwd dnum srcpath srcname dstpath dstname hm'
    REC:hm' RET:^(mscs,fsxp)
      exists d,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
        [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} rename fsxp dnum srcpath srcname dstpath dstname mscs >> recover cachesize.
  Proof.
    recover_ro_ok.
    cancel.
    eauto.
    safestep.
    or_l.
    cancel.
    subst.
    apply pimpl_refl.
    or_r.
    cancel.
    subst.
    apply pimpl_refl.

    (* if CRASH is LOG.idempred, we must manually instantiate idemcrash to include
       the after_crash case *)
    eassign ( LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    cancel; cancel.
    xform_norm; recover_ro_ok.

    - rewrite LOG.crash_xform_intact.
      xform_norm.
      rewrite SB.crash_xform_rep.
      rewrite LOG.notxn_after_crash_diskIs with (n := 0) (ds := (fst v, nil)); auto.
      cancel.
      safestep.
      cancel.
      pred_apply; subst.
      replace n with 0 by omega.
      rewrite nthd_0; eauto.
      cancel; cancel.

    - rewrite LOG.after_crash_idem.
      xform_norm.
      rewrite SB.crash_xform_rep.
      cancel.
      step.
      cancel; cancel.
  Qed.
*)

End AFS_RECOVER.
