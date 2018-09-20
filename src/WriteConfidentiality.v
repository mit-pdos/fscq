Require Import Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import DirCache.
Require Import GenSepN.
Require Import ListPred.
Require Import Inode.
Require Import List ListUtils.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.
Require Import SuperBlock.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import BFile.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Require Import AsyncFS.
Require Import DiskSecDef DiskSecAttacker DiskSecVictim PaperTheorems.
(* Require Import CopyFile. *)
Import AFS.



Theorem write_confidentiality:
forall caller d bm hm Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f Fd vs d1 bm1 hm1 r1 tr1 off data0 data1, 
  (Fr * [[sync_invariant Fr]] * [[ hm 0 = Some Public ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  exec caller d bm hm (update_fblock_d fsxp inum off data0 mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  DFOwner f <> Public ->
  exists d2 bm2 tr2 r2,
    exec caller d bm hm (update_fblock_d fsxp inum off data1 mscs) (Finished d2 bm2 hm1 r2) tr2 /\
  (forall adv, ~can_access adv (DFOwner f) -> equivalent_for_principal adv d1 bm1 d2 bm2 hm1).
Proof.
  unfold update_fblock_d; intros.
  inv_exec_perm.
  pose proof (@update_fblock_d'_ok fsxp inum off mscs caller) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= d).
  Opaque update_fblock_d'.
  2: repeat econstructor; eauto.
  {
    repeat eexists; pred_apply; cancel.
    cancel; eauto.
    eauto.
    eauto.
    destruct_lift H3.
    inv_exec'' H7.
    do 3 eexists; left; repeat eexists; eauto.
    eassign (fun (d:rawdisk) (bm' :taggedmem) (hm': domainmem) (r: BFILE.memstate * (res unit * unit)) =>
               let mscs' := fst r in let ok := fst (snd r) in
                (Fr * [[ sync_invariant Fr ]] * [[ hm' 0 = Some Public ]] *
                 LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
               [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm hm') ]]] *
               [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
               [[[ (DFData f) ::: (Fd * off |-> vs) ]]] *     
               ([[ isError ok ]] \/
                [[ ok = OK tt ]] * [[ can_access caller (DFOwner f) ]]))%pred d); simpl ;auto.
    pred_apply; cancel.
    or_l; cancel.
    eauto.
    or_r; cancel.
    eauto.
    inv_exec'' H7; simpl; auto.
    eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
      intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; cleanup; split_ors; cleanup; try congruence.
  eapply exec_same_except_finished in H0; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.
  apply sep_star_or_distr in H5; apply pimpl_or_apply in H5;
    split_ors; destruct_lift H5; cleanup.
  inversion H9.
  {
    Transparent LOG.commit_ro LOG.abort.
    unfold LOG.abort in *.
    repeat inv_exec_perm.
    do 4 eexists; split.
    econstructor; eauto.
    inversion H20; subst.
    simpl; rewrite <- app_nil_l; repeat econstructor; eauto.
    repeat split; simpl; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply same_except_to_equivalent_for; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply blockmem_same_except_to_equivalent_for; eauto.
  }
  {
    (*inversion H9; subst.*)
    Transparent LOG.commit_ro LOG.abort.
    unfold LOG.commit_ro in *.
    repeat inv_exec_perm.
    inversion H22; subst.
    specialize (H6 x8) as Hx; split_ors; cleanup; try congruence.
    pose proof (@DIRTREE.dwrite_ok fsxp inum off x8 x8_1 caller) as Hspec.
    specialize (Hspec _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hspec with (d:= x9).
    Opaque DIRTREE.dwrite.
    2: repeat econstructor; eauto.
    {
      repeat eexists; pred_apply; norm.
      unfold stars; simpl.
      erewrite LOG.rep_blockmem_subset. cancel.
      eauto.
      intuition eauto.
      apply Mem.upd_eq; eauto.
      simpl; auto.
      destruct_lift H2.
      inv_exec'' H12.
      do 3 eexists; left; repeat eexists; eauto.
      eassign (fun (_:rawdisk) (_:taggedmem) (_: domainmem) (_: BFILE.memstate) => True); simpl ;auto.
      inv_exec'' H12; simpl; auto.
      eassign (fun (_:taggedmem) (_: domainmem) (_:rawdisk) => True); simpl;
        intros mx Hmx; simpl; auto.
    }
    simpl in *; clear H2 Hspec.
    eapply exec_same_except_finished with (bm':=(Mem.upd x2 x8 (S inum, data1))) in H7;
    eauto; cleanup.
    do 4 eexists; split.
    repeat econstructor; eauto.
    simpl; repeat econstructor; eauto.
    repeat split; simpl; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply same_except_to_equivalent_for; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply blockmem_same_except_to_equivalent_for; eauto.
    eapply blockmem_same_except_upd_same; eauto.
    unfold rep in H8; destruct_lift H8.
    erewrite owner_match; eauto.
    2: pred_apply' H2; cancel.
    2: pred_apply; cancel.
    denote tree_pred as Htp; erewrite subtree_extract in Htp; eauto.
    unfold tree_pred in Htp; destruct_lift Htp.    
    denote BFILE.rep as Hbf; unfold BFILE.rep in Hbf; destruct_lift Hbf.
    denote listmatch as Hlm;
       erewrite listmatch_length_pimpl in Hlm;
      erewrite listmatch_isolate with (i:=inum) in Hlm.
    unfold BFILE.file_match in Hlm.
    destruct_lift Hlm.
    denote INODE.rep as Hbf; unfold INODE.rep in Hbf; destruct_lift Hbf.
    rewrite H32; apply H37.
    rewrite <- H30.
    eapply list2nmem_ptsto_bound; eauto; pred_apply; cancel.
    eapply list2nmem_ptsto_bound; eauto; pred_apply; cancel.
    destruct_lift Hlm.
    rewrite <- H30; eapply list2nmem_ptsto_bound; eauto; pred_apply; cancel.
  }
  congruence.
  apply same_except_refl.
  apply blockmem_same_except_refl.
Qed.


