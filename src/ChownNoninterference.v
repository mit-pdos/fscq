Require Import Arith.
Require Import Mem Pred.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import Errno.

Require Import GenSepAuto. 
Require Import ListPred.
Require Import Log.
Require Import Balloc.
Require Import FSLayout.
Require Import BlockPtr.
Require Import Inode BFile DirTree.
Require Import DiskSecAttacker PaperTheorems.
Import INODE.



    Opaque IRec.get_array IRec.put_array_if_can_commit.
    Theorem inode_setowner_exec_equivalent_cant_access:
  forall viewer caller d bm hm d' bm' Fr lxp xp bxp Fi Fs IFs ino m0 m ms cache sm Fm ilist inum F d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
   [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
   [[[ ilist ::: (Fi * inum |-> ino) ]]] *
   [[ (Fs * IFs)%pred sm ]] *
   [[ can_access caller (IOwner ino) ]])%pred d ->
  
  exec caller d bm hm (setowner lxp xp inum new_tag cache ms) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  ~can_access viewer new_tag ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (setowner lxp xp inum new_tag cache ms) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm.
    Proof.
       unfold setowner, equivalent_for_principal; intros.
       inv_exec_perm.
       pose proof (@IRec.get_array_ok lxp xp inum cache ms caller) as Hspec.
       specialize (Hspec _ (fun r => Ret r)).
       unfold corr2 in *.
       unfold rep in *; destruct_lift H.
       edestruct Hspec with (d:= d).
       2: repeat econstructor; eauto.
       { (** extract postcondition from LOG.begin **)
         clear Hspec; 
         repeat eexists; pred_apply; cancel.
         denote listmatch as Hm;
           rewrite listmatch_length_pimpl in Hm.
         destruct_lift Hm.
         rewrite combine_length_eq in *; eauto.
         denote (length _ = length _) as Hlen;
           setoid_rewrite <- Hlen.
         eapply list2nmem_inbound; eauto.
        match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem)
                    (r: IRec.Cache_type * (LOG.mstate * cachestate * (IRec.LRA.Defs.item * unit))) =>
                    let cache' := fst r in let ms' := fst (snd r) in let ret := fst (snd (snd r)) in
                    (Fr * [[ hm = hm' ]] *
                    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
                    [[ ((listmatch (inode_match bxp) (combine ilist dummy0) dummy ✶ Fm) *
                        IRec.rep xp dummy cache')%pred (list2nmem m) ]] *
                    [[ ret = selN dummy inum IRec.LRA.Defs.item0 ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
          simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
       }
       simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
       eapply exec_equivalent_for_viewer_finished in H0; eauto; cleanup.
       2: intros; edestruct H1; eauto.
       2: intros; edestruct H1; eauto.
       unfold pair_args_helper in *; simpl in *.

       destruct_lifts.
       inv_exec_perm.
        pose proof (@IRec.put_array_if_can_commit_ok lxp xp inum ^( x1_2_2_1_1,
            ^( ^( x1, x7_1, x7_2_1, x7_2_2_1, x7_2_2_2_1, x7_2_2_2_2_1, x7_2_2_2_2_2_1, x7_2_2_2_2_2_2_1),
            encode_tag new_tag, x8_2_1), x9_1, x9_2_1, x9_2_2_1, x9_2_2_2_1) x1_1 
            (x1_2_1_1, x1_2_1_2) caller) as Hspec.
       specialize (Hspec _ (fun r => Ret r)).
       unfold corr2 in *.
       destruct_lifts.
       edestruct Hspec with (d:= x5).
       2: repeat econstructor; eauto.
       { (** extract postcondition from LOG.begin **)
         clear Hspec; 
           repeat eexists; pred_apply; cancel; eauto.
         irec_wf.
         
         denote listmatch as Hm;
           rewrite listmatch_length_pimpl in Hm.
         destruct_lift Hm.
         rewrite combine_length_eq in *; [ |eauto].
         sepauto.
         match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
           instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem)
                    (r: IRec.Cache_type * (LOG.mstate * cachestate *  unit)) =>
                    let cache' := fst r in let ms' := fst (snd r) in
                    let e := ^( x1_2_2_1_1,
               ^( ^( x1, x7_1, x7_2_1, x7_2_2_1, x7_2_2_2_1, x7_2_2_2_2_1, x7_2_2_2_2_2_1, x7_2_2_2_2_2_2_1),
               encode_tag new_tag, x8_2_1), x9_1, x9_2_1, x9_2_2_1, x9_2_2_2_1) in
                    let items' := dummy ⟦ inum := e ⟧ in
                    exists m',
                    (Fr * [[ x7 = hm' ]] *
                    LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
                    [[[ m' ::: (Fm ✶ listmatch (inode_match bxp) (combine ilist dummy0) dummy)
                        * IRec.rep xp items' cache' ]]] *
                    [[[ items' ::: (arrayN_ex (ptsto (V:=IRec.LRA.Defs.item)) dummy inum) * (inum |-> e) ]]])%pred d) in Hpc
         end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
       }
       simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
       eapply exec_equivalent_for_viewer_finished in H3; eauto; cleanup.
       unfold pair_args_helper in *; simpl in *.

       inv_exec_perm.
       denote ChDom as Hdom; eapply chdom_equivalent_for_viewer in Hdom; eauto.
       2: unfold equivalent_for_principal; intuition eauto.
       simpl in *; cleanup; try congruence.
       inv_exec_perm.
       denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
       do 3 eexists; split; eauto.
       repeat (econstructor; [eauto| simpl]);
         econstructor; eauto.
       split; eauto.
       denote lift_empty as Hemp; destruct_lift Hemp; eauto.
       unfold equivalent_for_principal in *; eauto.

       Unshelve.
       all: try exact addr; try exact nil; try exact IRec.LRA.Defs.item0; eauto.
    Qed.
    
    Theorem inode_setowner_exec_equivalent_same_for_id:
  forall viewer caller d bm hm d' bm' Fr lxp xp bxp Fi Fs IFs ino m0 m ms cache sm Fm ilist inum F d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
   [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
   [[[ ilist ::: (Fi * inum |-> ino) ]]] *
   [[ (Fs * IFs)%pred sm ]] *
   [[ can_access caller (IOwner ino) ]])%pred d ->
  
  exec caller d bm hm (setowner lxp xp inum new_tag cache ms) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  same_for_domainid (S inum) d bm d' bm' ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (setowner lxp xp inum new_tag cache ms) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
    same_for_domainid (S inum) d1 bm1 d2 bm2.
    Proof.
      unfold setowner, equivalent_for_principal; intros.
       inv_exec_perm.
       pose proof (@IRec.get_array_ok lxp xp inum cache ms caller) as Hspec.
       specialize (Hspec _ (fun r => Ret r)).
       unfold corr2 in *.
       unfold rep in *; destruct_lift H.
       edestruct Hspec with (d:= d).
       2: repeat econstructor; eauto.
       { (** extract postcondition from LOG.begin **)
         clear Hspec; 
         repeat eexists; pred_apply; cancel.
         denote listmatch as Hm;
           rewrite listmatch_length_pimpl in Hm.
         destruct_lift Hm.
         rewrite combine_length_eq in *; eauto.
         denote (length _ = length _) as Hlen;
           setoid_rewrite <- Hlen.
         eapply list2nmem_inbound; eauto.
         match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem)
                    (r: IRec.Cache_type * (LOG.mstate * cachestate * (IRec.LRA.Defs.item * unit))) =>
                    let cache' := fst r in let ms' := fst (snd r) in let ret := fst (snd (snd r)) in
                    (Fr * [[ hm = hm' ]] *
                    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
                    [[ ((listmatch (inode_match bxp) (combine ilist dummy0) dummy ✶ Fm) *
                        IRec.rep xp dummy cache')%pred (list2nmem m) ]] *
                    [[ ret = selN dummy inum IRec.LRA.Defs.item0 ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
       }
       simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
       eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H0; eauto; cleanup.
       2: intros; edestruct H1; eauto.
       2: intros; edestruct H1; eauto.
       unfold pair_args_helper in *; simpl in *.
       
       destruct_lifts.
       inv_exec_perm.
        pose proof (@IRec.put_array_ok lxp xp inum ^( x1_2_2_1_1,
            ^( ^( x1, x7_1, x7_2_1, x7_2_2_1, x7_2_2_2_1, x7_2_2_2_2_1, x7_2_2_2_2_2_1, x7_2_2_2_2_2_2_1),
            encode_tag new_tag, x8_2_1), x9_1, x9_2_1, x9_2_2_1, x9_2_2_2_1) x1_1 
            (x1_2_1_1, x1_2_1_2) caller) as Hspec.
       specialize (Hspec _ (fun r => Ret r)).
       unfold corr2 in *.
       destruct_lifts.
       edestruct Hspec with (d:= x5).
       2: repeat econstructor; eauto.
       { (** extract postcondition from LOG.begin **)
         clear Hspec; 
           repeat eexists; pred_apply; cancel; eauto.
         irec_wf.
         
         denote listmatch as Hm;
           rewrite listmatch_length_pimpl in Hm.
         destruct_lift Hm.
         rewrite combine_length_eq in *; [ |eauto].
         sepauto.
         match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
           instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem)
                    (r: IRec.Cache_type * (LOG.mstate * cachestate *  unit)) =>
                    let cache' := fst r in let ms' := fst (snd r) in
                    let e := ^( x1_2_2_1_1,
               ^( ^( x1, x7_1, x7_2_1, x7_2_2_1, x7_2_2_2_1, x7_2_2_2_2_1, x7_2_2_2_2_2_1, x7_2_2_2_2_2_2_1),
               encode_tag new_tag, x8_2_1), x9_1, x9_2_1, x9_2_2_1, x9_2_2_2_1) in
                    let items' := dummy ⟦ inum := e ⟧ in
                    exists m',
                    (Fr * [[ x7 = hm' ]] *
                    LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
                    [[[ m' ::: (Fm ✶ listmatch (inode_match bxp) (combine ilist dummy0) dummy)
                        * IRec.rep xp items' cache' ]]] *
                    [[[ items' ::: (arrayN_ex (ptsto (V:=IRec.LRA.Defs.item)) dummy inum) * (inum |-> e) ]]])%pred d) in Hpc
         end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
       }
       simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
       eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H3; eauto; cleanup.
       unfold pair_args_helper in *; simpl in *.

       inv_exec_perm.
       denote ChDom as Hdom; eapply chdom_equivalent_for_viewer in Hdom; eauto.
       2: unfold equivalent_for_principal; intuition eauto.
       simpl in *; cleanup; try congruence.
       inv_exec_perm.
       denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
       do 3 eexists; split; eauto.
       repeat (econstructor; [eauto| simpl]);
         econstructor; eauto.

       Unshelve.
       all: try exact addr; try exact nil; try exact IRec.LRA.Defs.item0; eauto.
    Qed.


    Import BFILE.
    Theorem bfile_setowner_exec_equivalent_cant_access:
  forall viewer caller d bm hm d' bm' Fr Ff f bxps lxp ixp allocc frees flist m0 m ms sm Fm ilist inum F d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
  LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
  [[[ m ::: (Fm * rep bxps sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms) hm) ]]] *
  [[[ flist ::: (Ff * inum |-> f) ]]] *
  [[ can_access caller (BFOwner f) ]])%pred d ->
  
  exec caller d bm hm (setowner lxp ixp inum new_tag ms) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  ~can_access viewer new_tag ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (setowner lxp ixp inum new_tag ms) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm.
    Proof.
      unfold setowner; intros.
      inv_exec_perm.
      unfold rep in *.
      destruct_lift H.
      eapply inode_setowner_exec_equivalent_cant_access in H0; eauto.
      cleanup.
      unfold pair_args_helper in *; simpl in *.
      inv_exec_perm.
      do 3 eexists; split; eauto.
       repeat (econstructor; [eauto| simpl]);
         econstructor; eauto.
      pred_apply; cancel.
      sepauto.

      denote listmatch as Hx;
        rewrite listmatch_length_pimpl in Hx.
      destruct_lift Hx.
      assert (A:inum < length flist). { eapply list2nmem_inbound; eauto. }
      assert (A0:inum < length ilist). { match goal with [H: length _ = ?x |- _ < ?x ] => rewrite <- H; eauto end. }
      denote listmatch as Hx.
      rewrite listmatch_isolate with (i:=inum) in Hx by auto.
      unfold file_match in Hx; destruct_lift Hx.
      rewrite <- H21; eauto.
      erewrite <- list2nmem_sel; eauto.

      Unshelve.
      exact bfile0.
      Grab Existential Variables.
      exact inode0.
    Qed.


    Theorem bfile_setowner_exec_equivalent_same_for_id:
  forall viewer caller d bm hm d' bm' Fr Ff f bxps lxp ixp allocc frees flist m0 m ms sm Fm ilist inum F d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
  LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
  [[[ m ::: (Fm * rep bxps sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms) hm) ]]] *
  [[[ flist ::: (Ff * inum |-> f) ]]] *
  [[ can_access caller (BFOwner f) ]])%pred d ->
  
  exec caller d bm hm (setowner lxp ixp inum new_tag ms) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  same_for_domainid (S inum) d bm d' bm' ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (setowner lxp ixp inum new_tag ms) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
    same_for_domainid (S inum) d1 bm1 d2 bm2.
    Proof.
      unfold setowner; intros.
      inv_exec_perm.
      unfold rep in *.
      destruct_lift H.
      eapply inode_setowner_exec_equivalent_same_for_id in H0; eauto.
      cleanup.
      unfold pair_args_helper in *; simpl in *.
      inv_exec_perm.
      do 3 eexists; split; eauto.
       repeat (econstructor; [eauto| simpl]);
         econstructor; eauto.
      pred_apply; cancel.
      sepauto.

      denote listmatch as Hx;
        rewrite listmatch_length_pimpl in Hx.
      destruct_lift Hx.
      assert (A:inum < length flist). { eapply list2nmem_inbound; eauto. }
      assert (A0:inum < length ilist). { match goal with [H: length _ = ?x |- _ < ?x ] => rewrite <- H; eauto end. }
      denote listmatch as Hx.
      rewrite listmatch_isolate with (i:=inum) in Hx by auto.
      unfold file_match in Hx; destruct_lift Hx.
      rewrite <- H21; eauto.
      erewrite <- list2nmem_sel; eauto.

      Unshelve.
      exact bfile0.
      Grab Existential Variables.
      exact inode0.
    Qed.

    Require Import DirTreePath.
    Require Import DirTreeDef.
    Require Import DirTreePred.
    Require Import DirTreeRep.
    Require Import DirTreeSafe.
    Require Import DirTreeNames.
    Require Import DirTreeInodes.
    Import DIRTREE.
   
    Theorem dirtree_changeowner_exec_equivalent_cant_access:
  forall viewer caller d bm hm d' bm' Fr f fsxp frees m0 m mscs sm Fm ilist inum F d1 bm1 hm1 r1 tr1 new_tag tree Ftop pathname,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
  LOG.rep (FSXPLog fsxp) F (LOG.ActiveTxn m0 m) (MSLL mscs) sm bm hm *
  [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)%pred (list2nmem m) ]] *
  [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
  [[ can_access caller (DFOwner f) ]])%pred d ->
  
  exec caller d bm hm (changeowner fsxp inum new_tag mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  ~can_access viewer new_tag ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (changeowner fsxp inum new_tag mscs) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm.
    Proof.
       unfold changeowner; intros.
       inv_exec_perm.
      unfold rep in *.
      destruct_lift H.
      rewrite subtree_extract in * by eauto.
      cbn [tree_pred] in *. destruct_lifts.
      
      eapply bfile_setowner_exec_equivalent_cant_access in H0; eauto.
      cleanup.
      unfold pair_args_helper in *; simpl in *.
      inv_exec_perm.
      do 3 eexists; split; eauto.
       repeat (econstructor; [eauto| simpl]);
         econstructor; eauto.
       pred_apply; cancel.
    Qed.


    Theorem dirtree_changeowner_exec_equivalent_same_for_id:
  forall viewer caller d bm hm d' bm' Fr f fsxp frees m0 m mscs sm Fm ilist inum F d1 bm1 hm1 r1 tr1 new_tag tree Ftop pathname,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
  LOG.rep (FSXPLog fsxp) F (LOG.ActiveTxn m0 m) (MSLL mscs) sm bm hm *
  [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)%pred (list2nmem m) ]] *
  [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
  [[ can_access caller (DFOwner f) ]])%pred d ->
  
  exec caller d bm hm (changeowner fsxp inum new_tag mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  same_for_domainid (S inum) d bm d' bm' ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (changeowner fsxp inum new_tag mscs) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
    same_for_domainid (S inum) d1 bm1 d2 bm2.
    Proof.
      unfold changeowner; intros.
      inv_exec_perm.
      unfold rep in *.
      destruct_lift H.
      rewrite subtree_extract in * by eauto.
      cbn [tree_pred] in *. destruct_lifts.
      
      eapply bfile_setowner_exec_equivalent_same_for_id in H0; eauto.
      cleanup.
      unfold pair_args_helper in *; simpl in *.
      inv_exec_perm.
      do 3 eexists; split; eauto.
       repeat (econstructor; [eauto| simpl]);
         econstructor; eauto.
       pred_apply; cancel.
    Qed.

    Require Import SuperBlock AsyncFS.
    Import AFS.

    Import DiskSecDef.

  Fixpoint no_domain_change {T} (p: prog T) :=
    match p with
    | Bind p1 p2 =>  no_domain_change p1 /\ (forall r, no_domain_change (p2 r))
    | ChDom _ _ => False
    | _ => True
    end.

  Lemma no_domain_change_foreach:
           forall (ITEM : Type) (lst : list ITEM) (L : Type) (G : Type) (f : ITEM -> L -> prog L)
                (nocrash : G -> list ITEM -> L -> taggedmem -> domainmem -> rawpred tagged_block)
                (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block) (l : L),
          (forall i l, no_domain_change (f i l)) ->
          no_domain_change (ForEach_ f lst nocrash crashed l).
        Proof.
          induction lst; simpl; eauto.
        Qed.

        Lemma no_domain_change_forn:
           forall n i (L : Type) (G : Type) (f : nat -> L -> prog L)
                (nocrash : G -> nat -> L -> taggedmem -> domainmem -> rawpred tagged_block)
                (crashed : G -> taggedmem -> domainmem -> rawpred tagged_block) (l : L),
          (forall i l, no_domain_change (f i l)) ->
          no_domain_change (ForN_ f i n nocrash crashed l).
        Proof.
          induction n; simpl; eauto.
        Qed.
        
      Ltac delve :=
        match goal with
        | [ |- context [ If (?x) { _ } else { _ }] ] =>
          let D := fresh "D" in
          destruct x eqn:D; try setoid_rewrite D; simpl; repeat split; intros; eauto; clear D; repeat delve
        | [ |- context [ match ?x with | _ =>  _ end ] ] =>
          let D := fresh "D" in
          destruct x eqn:D; try setoid_rewrite D; simpl; repeat split; intros; eauto; clear D; repeat delve
        | [ |- context [ let _ := ?x in _ ] ] =>
          destruct x; simpl; repeat split; intros; eauto; repeat delve
        | [ |- no_domain_change (ForEach_ _ _ _ _ _) ] =>
          eapply no_domain_change_foreach; eauto; intros; simpl; repeat split; intros; eauto; repeat delve
        | [ |- no_domain_change (ForN_ _ _ _ _ _ _) ] =>
          eapply no_domain_change_forn; eauto; intros; simpl; repeat split; intros; eauto; repeat delve
        end.

        
        
      Lemma no_domain_change_commit:
        forall a b,
          no_domain_change (LOG.commit a b).
      Proof.
        intros.
        Transparent LOG.commit.
        unfold LOG.commit, GLog.submit, GLog.flushall_noop,
        GLog.flushall, GLog.flushall_nomerge, pair_args_helper; simpl.
        unfold avail, extend, MLog.flush, MLog.apply, MLog.flush_noapply,
        DiskLogPadded.avail, DiskLogPadded.extend, 
        CacheDef.read, maybe_evict, evict, writeback,
        pair_args_helper; simpl.
        delve.
        all: unfold pair_args_helper; simpl.
        all: intros; try delve. 
        all: unfold CacheDef.read; unfold maybe_evict; unfold evict; unfold writeback; simpl; try delve.
      Qed.
  
  Lemma equivalent_no_domain_change_cant_access:
    forall T (p: prog T) viewer caller d bm d' bm' d1 bm1 hm hm' hm1 i ntg tr1 r1,
      exec caller d bm hm' p (Finished d1 bm1 hm1 r1) tr1 ->
      (forall tag, can_access viewer tag -> equivalent_for tag d d' hm) ->
      (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm bm' hm) ->
      only_public_operations tr1 ->
      ~can_access viewer ntg ->
      hm' = upd hm i ntg ->
      no_domain_change p ->
      exists d2 bm2 tr2,
        exec caller d' bm' hm' p (Finished d2 bm2 hm1 r1) tr2 /\
      (forall tag, can_access viewer tag -> equivalent_for tag d1 d2 hm) /\
      (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm1 bm2 hm) /\
      hm' = hm1.
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [do 3 eexists; split; [econstructor; eauto|
                                     split; eauto ] ].
  { (** Read **)
    destruct bs.
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx r1); intuition; cleanup; try congruence.
    specialize H0 with (1:= can_access_public viewer) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    destruct x0, t0.
    unfold vsmerge in *; simpl in *.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    do 3 eexists; split.
    econstructor; eauto.
    split; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r1); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    intros.
    simpl in *; eauto.
    specialize H0 with (1:= H) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    unfold vsmerge in *; simpl in *.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Write **)
    destruct b, bs, t; simpl in *.
    destruct (hm n0) eqn: D.    
    destruct (can_access_dec viewer t).
    { (** can access **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= c) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** can't access **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public viewer) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      destruct (tag_dec t tag); subst; intuition.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; cleanup; intuition.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** inconsistent **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public viewer) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; congruence.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
  }
  { (** Seal **)
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx r1); intuition; cleanup; try congruence.
    do 3 eexists; split.
    econstructor; eauto.
    split; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r1); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Unseal **)
    intuition.
    destruct b; simpl in *.
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx h); intuition; cleanup; try congruence.
    simpl in *; intuition; subst.
    do 3 eexists; split.
    rewrite H8.
    econstructor; eauto.
    destruct (addr_eq_dec i (fst x0)); subst.
    rewrite upd_eq in *; eauto.
    cleanup; intuition.
    rewrite upd_ne in *; eauto.
    split; eauto.
  }
  { (** Sync **)
    repeat eexists; [econstructor; eauto| |eauto].
    unfold equivalent_for in *; intros.
    specialize H0 with (1:= H) as Hx.
    unfold sync_mem.
    specialize (Hx a); split_ors; cleanup; eauto.
    repeat match goal with
           | [H: ?x = _ |- context [?x] ] => rewrite H
           end; eauto.
    repeat match goal with
           | [H: ?x = _ |- context [?x] ] => rewrite H
           end; eauto.
    destruct x, x0.
    unfold vsmerge in *; simpl in *; eauto.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    right; repeat eexists; simpl; eauto.    
  }
  {
    simpl in *; intuition.
  }
  { (** Bind **)
    apply only_public_operations_app in H3; cleanup.
    destruct H6.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H5)(5:=H4); cleanup.
    edestruct IHp; eauto; cleanup.
    specialize H with (1:=H7)(2:=H10)(3:=H11)(4:=H3)(5:=H4); cleanup.
    edestruct H; eauto; cleanup.
    repeat eexists; [econstructor; eauto| |]; eauto.
  }

  Unshelve.
  all: try exact addr; eauto.
  all: try exact nil.
  all: try exact eq.
Qed.

    Theorem changeowner_exec_cant_access:
  forall viewer caller d bm hm d' bm' Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->

  exec caller d bm hm (changeowner fsxp inum new_tag mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  ~can_access viewer new_tag ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (changeowner fsxp inum new_tag mscs) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1.
Proof.
  unfold changeowner, equivalent_for_principal; intros.
  inv_exec_perm.
  pose proof (@LOG.begin_ok (FSXPLog fsxp) (MSLL mscs) caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= d).
  2: repeat econstructor; eauto.
  { (** extract postcondition from LOG.begin **)
    repeat eexists; pred_apply; cancel.
    match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: LOG.memstate) =>
               (Fr * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) r sm bm' hm' *
               [[ hm = hm' ]] * [[ LOG.readOnly (MSLL mscs) r ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_equivalent_for_viewer_finished in H0; eauto; cleanup.
  2: intros; edestruct H1; eauto.
  2: intros; edestruct H1; eauto.
  unfold pair_args_helper in *; simpl in *.

  denote lift_empty as Hemp; destruct_lift Hemp.
  denote lift_empty as Hemp; destruct_lift Hemp.
  inv_exec_perm.
  pose proof (@DIRTREE.authenticate_ok fsxp inum
            {|
            BFILE.MSAlloc := MSAlloc mscs;
            BFILE.MSLL := (x8_1, x8_2);
            BFILE.MSAllocC := MSAllocC mscs;
            BFILE.MSIAllocC := MSIAllocC mscs;
            BFILE.MSICache := MSICache mscs;
            BFILE.MSCache := SDIR.MSCache mscs;
            BFILE.MSDBlocks := MSDBlocks mscs |} caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= x5).
  2: econstructor; eauto; repeat econstructor.
  { (** extract postcondition from DIRTREE.authenticate **)
    repeat eexists; pred_apply; cancel.
    erewrite mscs_same_except_log_rep'.
    cancel; apply pimpl_refl.
    unfold BFILE.mscs_same_except_log; simpl; intuition.
    eauto.

     match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate * (bool * unit)) =>
               let mscs' := fst r in let ok := fst (snd r) in
               (Fr * [[ x7 = hm' ]] *
                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
                [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm hm') ]]] *
                [[ BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ]] *
                [[ BFILE.MSCache mscs' = BFILE.MSCache mscs ]] *
                [[ MSAllocC mscs' = MSAllocC mscs ]] *
                [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
                (([[ ok = true ]] * [[ can_access caller (DFOwner f) ]]) \/
                 ([[ ok = false ]] * [[ ~can_access caller (DFOwner f) ]])))%pred d) in Hpc
        end.
     destruct_lift Hpc.
     denote Ret as Hret; inv_exec'' Hret.
      do 3 eexists; left; repeat eexists; eauto.
      simpl ;auto.
      pred_apply; cancel.
      or_l; cancel.
      or_r; cancel.
      denote Ret as Hret; inv_exec'' Hret; simpl; auto.
      eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
      intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_equivalent_for_viewer_finished in H3; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.

  denote lift_empty as Hemp; destruct_lift Hemp.
  denote or as Hor;
  apply sep_star_or_distr in Hor; apply pimpl_or_apply in Hor;
    split_ors; denote lift_empty as Hemp; destruct_lift Hemp; cleanup; simpl in *.
  { (* DIRTREE.authenticate returns true *)
    inv_exec_perm.
    pose proof (@DIRTREE.getowner_ok fsxp inum x15_1 caller) as Hspec.
    specialize (Hspec _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hspec with (d:= x0).
    2: econstructor; eauto; repeat econstructor.
    { (** extract postcondition from DIRTREE.getowner **)
      repeat eexists; pred_apply; cancel.
      cancel; apply pimpl_refl.
      eauto.

       match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate * (tag * unit)) =>
               let mscs' := fst r in let r := fst (snd r) in
               (Fr * ⟦⟦ x14 = hm' ⟧⟧ *
                LOG.rep fsxp.(FSXPLog) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
                [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm hm' ]]] *
                [[ BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ]] *
                [[ BFILE.MSCache mscs' = BFILE.MSCache mscs ]] *
                [[ MSAllocC mscs' = MSAllocC mscs ]] *
                [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
                [[ r = DFOwner f ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_equivalent_for_viewer_finished in H9; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.

  denote lift_empty as Hemp; destruct_lift Hemp.
  inv_exec_perm.
  pose proof (@DIRTREE.changeowner_ok fsxp inum new_tag x21_1 caller) as Hspec.
    specialize (Hspec _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hspec with (d:= x8).
    2: econstructor; eauto; repeat econstructor.
    { (** extract postcondition from DIRTREE.getowner **)
      repeat eexists; pred_apply; cancel.
      cancel; apply pimpl_refl.
      eauto.

       match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:=fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate) =>
               let mscs' := r in
               exists m' tree' f' ilist',
                 (Fr *               
           LOG.rep fsxp.(FSXPLog) (SB.rep fsxp) (LOG.ActiveTxn ds m') (MSLL mscs') sm bm' hm' *
           [[ (Fm * rep fsxp Ftop tree' ilist' (frees_1, frees_2) mscs' sm hm')%pred (list2nmem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = mk_dirfile (DFData f) (DFAttr f) new_tag ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ dirtree_safe ilist  (BFILE.pick_balloc (frees_1, frees_2)  (MSAlloc mscs')) tree
                           ilist' (BFILE.pick_balloc (frees_1, frees_2)  (MSAlloc mscs')) tree' ]] *
           [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]] *
           [[ hm' = upd x20 (S inum) new_tag ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
          do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply dirtree_changeowner_exec_equivalent_cant_access in H18; eauto.
  3: unfold equivalent_for_principal; intuition eauto.
  2: {
    pred_apply; safecancel.
    cancel; apply pimpl_refl.
    eauto.
    eauto.
  }
  cleanup.
  
  denote lift_empty as Hemp; destruct_lift Hemp.
  inv_exec_perm.
  pose proof (@LOG.commit_ok (FSXPLog fsxp) (AFS.MSLL x27) caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= x12).
  2: econstructor; eauto; repeat econstructor.
  { (** extract postcondition from LOG.begin **)
    repeat eexists; pred_apply; cancel.
    
     match goal with
       [H: context [ donec = _ ] |- _ ] =>
       rename H into Hpc;
         instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: LOG.memstate * (bool * unit)) =>
           let ms' := fst r in let r := fst (snd r) in
             (Fr * ⟦⟦ (upd x20 (S inum) new_tag) = hm' ⟧⟧ *
              (([[ r = true ]] *  LOG.rep (FSXPLog fsxp) (SB.rep fsxp)  (LOG.NoTxn (pushd x28 ds)) ms' sm bm' hm') \/
               ([[ r = false ]] *
                [[ MapUtils.AddrMap.Map.cardinal (LOG.MSTxn (fst (AFS.MSLL x27))) > (LogLen (FSXPLog fsxp)) ]] *
                LOG.rep (FSXPLog fsxp) (SB.rep fsxp)  (LOG.NoTxn ds) ms' sm bm' hm')))%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
    
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         or_l; cancel.
         or_r; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
   denote lift_empty as Hemp; destruct_lift Hemp.
  denote or as Hor;
  apply sep_star_or_distr in Hor; apply pimpl_or_apply in Hor;
    split_ors; denote lift_empty as Hemp; 
      destruct_lift Hemp; cleanup; simpl in *.
  {
    eapply exec_equivalent_for_viewer_finished in H29; eauto; cleanup.
    2: intros; edestruct H31; eauto.
    2: intros; edestruct H31; eauto.
    unfold pair_args_helper in *; simpl in *.
    inv_exec_perm.
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.

    do 3 eexists; split; eauto.
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; eauto.
  }
  
  {
    eapply equivalent_no_domain_change_cant_access in H29; eauto; cleanup.
    unfold pair_args_helper in *; simpl in *.    
    inv_exec_perm.
    inv_exec_perm.    
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
    inv_exec_perm.
    
    do 3 eexists; split; eauto.
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].  
    econstructor; eauto.
    econstructor; eauto.
    rewrite upd_repeat, upd_nop; eauto.
    unfold rep in H8; destruct_lift H8.
    erewrite owner_match; eauto.
    2: pred_apply' H8; cancel.
    2: pred_apply; cancel.
    denote tree_pred as Htp; erewrite subtree_extract in Htp; eauto.
    unfold tree_pred in Htp; destruct_lift Htp.    
    denote BFILE.rep as Hbf; unfold BFILE.rep in Hbf; destruct_lift Hbf.
    denote listmatch as Hlm;
       erewrite listmatch_length_pimpl in Hlm;
      erewrite listmatch_isolate with (i:=inum) in Hlm.
    unfold file_match in Hlm.
    destruct_lift Hlm.
    denote INODE.rep as Hbf; unfold INODE.rep in Hbf; destruct_lift Hbf.
    rewrite H64; apply H69.
    rewrite <- H62.
    eapply list2nmem_ptsto_bound; eauto; pred_apply; cancel.
    eapply list2nmem_ptsto_bound; eauto; pred_apply; cancel.
    destruct_lift Hlm.
    rewrite <- H62; eapply list2nmem_ptsto_bound; eauto; pred_apply; cancel.
    intros; edestruct H38; eauto.
    intros; edestruct H38; eauto.
    apply no_domain_change_commit.      
  }
  }
  { (** auth returned false **)
    Transparent LOG.abort.
    unfold LOG.abort in *.
    inv_exec_perm.
    inv_exec_perm.    
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
    inv_exec_perm.    
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
    rewrite H18.
    do 3 eexists; split; eauto.
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; eauto.
    rewrite <- H18; econstructor; eauto.
  }

  Unshelve.
  all: try exact addr; eauto.
Qed.




  Theorem changeowner_exec_same_for_id:
  forall viewer caller d bm hm d' bm' Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->

  exec caller d bm hm (changeowner fsxp inum new_tag mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  same_for_domainid (S inum) d bm d' bm' ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (changeowner fsxp inum new_tag mscs) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1.
Proof.
  unfold changeowner, equivalent_for_principal; intros.
  inv_exec_perm.
  pose proof (@LOG.begin_ok (FSXPLog fsxp) (MSLL mscs) caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= d).
  2: repeat econstructor; eauto.
  { (** extract postcondition from LOG.begin **)
    repeat eexists; pred_apply; cancel.
    match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: LOG.memstate) =>
               (Fr * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) r sm bm' hm' *
               [[ hm = hm' ]] * [[ LOG.readOnly (MSLL mscs) r ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H0; eauto; cleanup.
  2: intros; edestruct H1; eauto.
  2: intros; edestruct H1; eauto.
  unfold pair_args_helper in *; simpl in *.

  denote lift_empty as Hemp; destruct_lift Hemp.
  denote lift_empty as Hemp; destruct_lift Hemp.
  inv_exec_perm.
  pose proof (@DIRTREE.authenticate_ok fsxp inum
            {|
            BFILE.MSAlloc := MSAlloc mscs;
            BFILE.MSLL := (x8_1, x8_2);
            BFILE.MSAllocC := MSAllocC mscs;
            BFILE.MSIAllocC := MSIAllocC mscs;
            BFILE.MSICache := MSICache mscs;
            BFILE.MSCache := SDIR.MSCache mscs;
            BFILE.MSDBlocks := MSDBlocks mscs |} caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= x5).
  2: econstructor; eauto; repeat econstructor.
  { (** extract postcondition from DIRTREE.authenticate **)
    repeat eexists; pred_apply; cancel.
    erewrite mscs_same_except_log_rep'.
    cancel; apply pimpl_refl.
    unfold BFILE.mscs_same_except_log; simpl; intuition.
    eauto.

     match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate * (bool * unit)) =>
               let mscs' := fst r in let ok := fst (snd r) in
               (Fr * [[ x7 = hm' ]] *
                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
                [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm hm') ]]] *
                [[ BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ]] *
                [[ BFILE.MSCache mscs' = BFILE.MSCache mscs ]] *
                [[ MSAllocC mscs' = MSAllocC mscs ]] *
                [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
                (([[ ok = true ]] * [[ can_access caller (DFOwner f) ]]) \/
                 ([[ ok = false ]] * [[ ~can_access caller (DFOwner f) ]])))%pred d) in Hpc
        end.
     destruct_lift Hpc.
     denote Ret as Hret; inv_exec'' Hret.
      do 3 eexists; left; repeat eexists; eauto.
      simpl ;auto.
      pred_apply; cancel.
      or_l; cancel.
      or_r; cancel.
      denote Ret as Hret; inv_exec'' Hret; simpl; auto.
      eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
      intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H3; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.

  denote lift_empty as Hemp; destruct_lift Hemp.
  denote or as Hor;
  apply sep_star_or_distr in Hor; apply pimpl_or_apply in Hor;
    split_ors; denote lift_empty as Hemp; destruct_lift Hemp; cleanup; simpl in *.
  { (* DIRTREE.authenticate returns true *)
    inv_exec_perm.
    pose proof (@DIRTREE.getowner_ok fsxp inum x15_1 caller) as Hspec.
    specialize (Hspec _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hspec with (d:= x0).
    2: econstructor; eauto; repeat econstructor.
    { (** extract postcondition from DIRTREE.getowner **)
      repeat eexists; pred_apply; cancel.
      cancel; apply pimpl_refl.
      eauto.

       match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate * (tag * unit)) =>
               let mscs' := fst r in let r := fst (snd r) in
               (Fr * ⟦⟦ x14 = hm' ⟧⟧ *
                LOG.rep fsxp.(FSXPLog) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
                [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm hm' ]]] *
                [[ BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ]] *
                [[ BFILE.MSCache mscs' = BFILE.MSCache mscs ]] *
                [[ MSAllocC mscs' = MSAllocC mscs ]] *
                [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
                [[ r = DFOwner f ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H10; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.

  denote lift_empty as Hemp; destruct_lift Hemp.
  inv_exec_perm.
  pose proof (@DIRTREE.changeowner_ok fsxp inum new_tag x21_1 caller) as Hspec.
    specialize (Hspec _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hspec with (d:= x8).
    2: econstructor; eauto; repeat econstructor.
    { (** extract postcondition from DIRTREE.getowner **)
      repeat eexists; pred_apply; cancel.
      cancel; apply pimpl_refl.
      eauto.

       match goal with
           [H: context [ donec = _ ] |- _ ] =>
           rename H into Hpc;
          instantiate (2:=fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate) =>
               let mscs' := r in
               exists m' tree' f' ilist',
                 (Fr *               
           LOG.rep fsxp.(FSXPLog) (SB.rep fsxp) (LOG.ActiveTxn ds m') (MSLL mscs') sm bm' hm' *
           [[ (Fm * rep fsxp Ftop tree' ilist' (frees_1, frees_2) mscs' sm hm')%pred (list2nmem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = mk_dirfile (DFData f) (DFAttr f) new_tag ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ dirtree_safe ilist  (BFILE.pick_balloc (frees_1, frees_2)  (MSAlloc mscs')) tree
                           ilist' (BFILE.pick_balloc (frees_1, frees_2)  (MSAlloc mscs')) tree' ]] *
           [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]] *
           [[ hm' = upd x20 (S inum) new_tag ]])%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
          do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply dirtree_changeowner_exec_equivalent_same_for_id in H20; eauto.
  3: unfold equivalent_for_principal; intuition eauto.
  2: {
    pred_apply; safecancel.
    cancel; apply pimpl_refl.
    eauto.
    eauto.
  }
  cleanup.
  
  denote lift_empty as Hemp; destruct_lift Hemp.
  inv_exec_perm.
  pose proof (@LOG.commit_ok (FSXPLog fsxp) (AFS.MSLL x27) caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= x12).
  2: econstructor; eauto; repeat econstructor.
  { (** extract postcondition from LOG.begin **)
    repeat eexists; pred_apply; cancel.
    
     match goal with
       [H: context [ donec = _ ] |- _ ] =>
       rename H into Hpc;
         instantiate (2:= fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: LOG.memstate * (bool * unit)) =>
           let ms' := fst r in let r := fst (snd r) in
             (Fr * ⟦⟦ (upd x20 (S inum) new_tag) = hm' ⟧⟧ *
              (([[ r = true ]] *  LOG.rep (FSXPLog fsxp) (SB.rep fsxp)  (LOG.NoTxn (pushd x28 ds)) ms' sm bm' hm') \/
               ([[ r = false ]] *
                [[ MapUtils.AddrMap.Map.cardinal (LOG.MSTxn (fst (AFS.MSLL x27))) > (LogLen (FSXPLog fsxp)) ]] *
                LOG.rep (FSXPLog fsxp) (SB.rep fsxp)  (LOG.NoTxn ds) ms' sm bm' hm')))%pred d) in Hpc
        end.
         destruct_lift Hpc.
         denote Ret as Hret; inv_exec'' Hret.
    
         do 3 eexists; left; repeat eexists; eauto.
         simpl ;auto.
         pred_apply; cancel.
         or_l; cancel.
         or_r; cancel.
         denote Ret as Hret; inv_exec'' Hret; simpl; auto.
         eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
           intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
   denote lift_empty as Hemp; destruct_lift Hemp.
  denote or as Hor;
  apply sep_star_or_distr in Hor; apply pimpl_or_apply in Hor;
    split_ors; denote lift_empty as Hemp; 
      destruct_lift Hemp; cleanup; simpl in *.
  {
    eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H32; eauto; cleanup.
    2: intros; edestruct H34; eauto.
    2: intros; edestruct H34; eauto.
    unfold pair_args_helper in *; simpl in *.
    inv_exec_perm.
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.

    do 3 eexists; split; eauto.
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; eauto.
  }
  
  {
    eapply exec_equivalent_for_viewer_same_for_domain_id_finished in H32; eauto; cleanup.
    2: intros; edestruct H34; eauto.
    2: intros; edestruct H34; eauto.
    unfold pair_args_helper in *; simpl in *.    
    inv_exec_perm.
    eapply chdom_equivalent_for_viewer in H42; eauto.
    cleanup.
    inv_exec_perm.    
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.

    do 3 eexists; split; eauto.
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].  
    econstructor; eauto.
    unfold equivalent_for_principal; intuition eauto.    
  }
  }
  { (** auth returned false **)
    Transparent LOG.abort.
    unfold LOG.abort in *.
    inv_exec_perm.
    inv_exec_perm.    
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
    inv_exec_perm.    
    denote (_ = _) as Heq; inversion Heq; subst; clear Heq.
    rewrite H20.
    do 3 eexists; split; eauto.
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; [eauto| simpl].
    econstructor; eauto.
    rewrite <- H20; econstructor; eauto.
  }

  Unshelve.
  all: try exact addr; eauto.
Qed.

Theorem changeowner_state_invariant:
  forall viewer caller d bm hm d' bm' Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f d1 bm1 hm1 r1 tr1 new_tag,
    
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->

  exec caller d bm hm (changeowner fsxp inum new_tag mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  (same_for_domainid (S inum) d bm d' bm' \/ ~can_access viewer new_tag) ->
  exists d2 bm2 tr2,
    exec caller d' bm' hm (changeowner fsxp inum new_tag mscs) (Finished d2 bm2 hm1 r1) tr2 /\
    equivalent_for_principal viewer d1 bm1 d2 bm2 hm1.
Proof.
  intros.
  split_ors.
  eapply changeowner_exec_same_for_id; eauto.
  eapply changeowner_exec_cant_access; eauto.
Qed.
