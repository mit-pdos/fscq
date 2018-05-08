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
Require Import DiskSecDef DiskSecAttacker DiskSecVictim.

Set Implicit Arguments.
Import AFS.
Import ListNotations.

Definition copy_file fsxp inum1 inum2 ams :=
  let^ (ams, d) <- read_fblock fsxp inum1 0 ams;;
  match d with
  | OK data =>                
    let^ (ams, ok) <- update_fblock_d fsxp inum2 0 data ams;;
    Ret ^(ams, ok)
  | Err e =>
    Ret ^(ams, Err e)
  end.


Definition sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm:=
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]])%pred.

Lemma read_fblock_post:
   forall Fr Fm Ftop pathname f Fd ds sm tree mscs fsxp ilist frees d bm hm pr off vs inum d' bm' hm' tr' (rx: (BFILE.memstate * (res block * unit))),
     
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  
  exec pr d bm hm (read_fblock fsxp inum off mscs)
       (Finished d' bm' hm' rx) tr' ->
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm' *
   (([[ isError ok ]]) \/
    ([[ ok = OK (snd (fst vs)) ]])))%pred d' /\ trace_secure pr tr'.
  Proof.
    unfold sys_rep, corr2; intros.
    pose proof (@read_fblock_ok fsxp inum off mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2_weak in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H2.
    eassign (fun d0 bm0 hm0 (rx: (BFILE.memstate * (res block * unit))) =>
     let a:= fst rx in let b:= (fst (snd rx)) in
    (Fr ✶ (((LOG.rep (FSXPLog fsxp) (SB.rep fsxp) 
                   (LOG.NoTxn ds) (MSLL a) sm bm0 hm0
                 ✶ 【 ds !!
                   ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】))
               ✶ ([[ isError b ]]
                  \/ [[ b = OK (snd (fst vs)) ]])))%pred d0).
    left; repeat eexists; simpl in *; eauto.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inv_exec_perm.
    cleanup; auto.
    unfold Sec.trace_secure; eauto.
    eassign (fun (_:block_mem) (_:hashmap) (_:rawdisk) => True).
    intros; simpl; auto.
    econstructor; eauto.
    econstructor.
    simpl in *.
    destruct rx, p.
    intuition; cleanup.
    eauto.
    destruct_lift H; subst.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    apply trace_secure_impl; auto.
    inversion H1.
    inversion H1.
  Qed.


Theorem read_fblock_same_except:
forall pr d1 bm1 d2 bm2 hm Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f Fd vs d1' bm1' hm' r tr off, 
  (Fr * [[sync_invariant Fr]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm1 hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]] *
   [[ can_access pr (DFOwner f) ]])%pred d1 ->
  exec pr d1 bm1 hm (read_fblock fsxp inum off mscs) (Finished d1' bm1' hm' r) tr ->
  same_except (DFOwner f) d1 d2 ->
  blockmem_same_except (DFOwner f) bm1 bm2 ->
  DFOwner f <> Public ->
  exists d2' bm2' r2, exec pr d2 bm2 hm (read_fblock fsxp inum off mscs) (Finished d2' bm2' hm' r2) tr /\
    same_except (DFOwner f) d1' d2' /\
    blockmem_same_except (DFOwner f) bm1' bm2' /\
    fst r = fst r2 /\
    ((isError(fst (snd r)) \/ isError(fst (snd r2))) -> r = r2).
Proof.
  unfold read_fblock; intros.
  inv_exec_perm.
  pose proof (@read_fblock'_ok fsxp inum off mscs pr) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= d1).
  Opaque read_fblock'.
  2: repeat econstructor; eauto.
  {
    repeat eexists; pred_apply; cancel.
    eauto.
    eauto.
    destruct_lift H5.
    inv_exec'' H10.
    left; repeat eexists; eauto.
    eassign (fun (_:rawdisk) (_:block_mem) (_: hashmap) (_: BFILE.memstate * (res handle * unit)) => True); simpl ;auto.
    inv_exec'' H10; simpl; auto.
    eassign (fun (_:block_mem) (_: hashmap) (_:rawdisk) => True); simpl;
      intros mx Hmx; simpl; auto.
  }
  simpl in *; clear H5 Hspec.  
  eapply exec_same_except_finished in H0; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.
  destruct (fst (snd x1)) eqn:D.
  {
    repeat inv_exec_perm.
    specialize (H7 h) as Hx; split_ors; cleanup; try congruence. 
    do 3 eexists; split.
    repeat econstructor; eauto.
    rewrite D; repeat econstructor; eauto.
    repeat split; simpl; eauto.
    intros Hc; inversion Hc; inversion H4.
  }
  {
    repeat inv_exec_perm.
    do 3 eexists; split.
    econstructor; eauto.
    rewrite D; repeat econstructor; eauto.
    split; eauto.
  }
  apply only_public_operations_impl; auto.
Qed.

Theorem update_fblock_d_same_except:
forall pr d1 bm1 d2 bm2 hm Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f Fd vs d1' bm1' hm' r tr off v v', 
  (Fr * [[sync_invariant Fr]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm1 hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]] *
   [[ can_access pr (DFOwner f) ]])%pred d1 ->
  exec pr d1 bm1 hm (update_fblock_d fsxp inum off v mscs) (Finished d1' bm1' hm' r) tr ->
  same_except (DFOwner f) d1 d2 ->
  blockmem_same_except (DFOwner f) bm1 bm2 ->
  DFOwner f <> Public ->
  exists d2' bm2', exec pr d2 bm2 hm (update_fblock_d fsxp inum off v' mscs) (Finished d2' bm2' hm' r) tr /\
    same_except (DFOwner f) d1' d2' /\
    blockmem_same_except (DFOwner f) bm1' bm2'.
Proof.
  unfold update_fblock_d; intros.
  inv_exec_perm.
  pose proof (@update_fblock_d'_ok fsxp inum off mscs pr) as Hspec.
  specialize (Hspec _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hspec with (d:= d1).
  Opaque update_fblock_d'.
  2: repeat econstructor; eauto.
  {
    repeat eexists; pred_apply; cancel.
    eauto.
    eauto.
    destruct_lift H5.
    inv_exec'' H10.
    left; repeat eexists; eauto.
    eassign (fun (d:rawdisk) (bm' :block_mem) (hm': hashmap) (r: BFILE.memstate * (res tag * unit)) =>
               let mscs' := fst r in let ok := fst (snd r) in
               (Fr * [[ sync_invariant Fr ]] *LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
               [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm) ]]] *
               [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
               [[[ (DFData f) ::: (Fd * off |-> vs) ]]] *     
               ([[ isError ok ]] \/
                exists t, [[ ok = OK t ]] * [[ t = DFOwner f ]] * [[ can_access pr t ]]))%pred d); simpl ;auto.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inv_exec'' H10; simpl; auto.
    eassign (fun (_:block_mem) (_: hashmap) (_:rawdisk) => True); simpl;
      intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; split_ors; cleanup; try congruence.  
  eapply exec_same_except_finished in H0; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.
  apply sep_star_or_distr in H7; apply pimpl_or_apply in H7;
    split_ors; destruct_lift H7; cleanup.
  inversion H11.
  {
    Transparent LOG.commit_ro LOG.abort.
    unfold LOG.abort in *.
    repeat inv_exec_perm.
    do 2 eexists; split.
    econstructor; eauto.
    inversion H21; subst.
    simpl; rewrite <- app_nil_l; repeat econstructor; eauto.
    repeat split; simpl; eauto.
  }
  {
    inversion H11; subst.
    Transparent LOG.commit_ro LOG.abort.
    unfold LOG.commit_ro in *.
    repeat inv_exec_perm.
    inversion H24; subst.
    specialize (H8 x8) as Hx; split_ors; cleanup; try congruence.
    pose proof (@DIRTREE.dwrite_ok fsxp inum off x8 x8_1 pr) as Hspec.
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
      destruct_lift H4.
      inv_exec'' H11.
      left; repeat eexists; eauto.
      eassign (fun (_:rawdisk) (_:block_mem) (_: hashmap) (_: BFILE.memstate) => True); simpl ;auto.
      inv_exec'' H11; simpl; auto.
      eassign (fun (_:block_mem) (_: hashmap) (_:rawdisk) => True); simpl;
        intros mx Hmx; simpl; auto.
    }
    simpl in *; clear H4 Hspec.
    eapply exec_same_except_finished with (bm':=(Mem.upd x2 x8 (DFOwner f, v')))in H10; eauto; cleanup.
    do 2 eexists; split.
    repeat econstructor; eauto.
    simpl; repeat econstructor; eauto.
    rewrite <- app_nil_l; econstructor; eauto.
    rewrite <- app_nil_l; repeat econstructor; eauto.
    split; eauto.
    eapply blockmem_same_except_upd_same; eauto.
    apply only_public_operations_impl; auto.
  }
  congruence.
  apply only_public_operations_impl; auto.
Qed.


Theorem copy_file_same_except:
forall pr d1 bm1 d2 bm2 hm Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname1 inum1 f1 vs1 pathname2 inum2 f2 vs2 d1' bm1' hm' r tr, 
  (Fr * [[sync_invariant Fr]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm1 hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
   [[ find_subtree pathname1 tree = Some (TreeFile inum1 f1) ]] *
   [[[ (DFData f1) ::: (0 |-> vs1) ]]] *
   [[ find_subtree pathname2 tree = Some (TreeFile inum2 f2) ]] *
   [[[ (DFData f2) ::: (0 |-> vs2) ]]] *
   [[ (DFOwner f1) = (DFOwner f2) ]] *
   [[ can_access pr (DFOwner f1) ]])%pred d1 ->
  exec pr d1 bm1 hm (copy_file fsxp inum1 inum2 mscs) (Finished d1' bm1' hm' r) tr ->
  same_except (DFOwner f1) d1 d2 ->
  blockmem_same_except (DFOwner f1) bm1 bm2 ->
  DFOwner f1 <> Public ->
  exists d2' bm2' r2, exec pr d2 bm2 hm (copy_file fsxp inum1 inum2 mscs) (Finished d2' bm2' hm' r2) tr /\
    same_except (DFOwner f1) d1' d2' /\
    blockmem_same_except (DFOwner f1) bm1' bm2'.
  
  unfold copy_file; intros.
  inv_exec_perm.
  edestruct read_fblock_post; eauto.
  unfold sys_rep; pred_apply; cancel; eauto.
  pred_apply; cancel.
  unfold sys_rep in *.
  eapply read_fblock_same_except in H0; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.
  destruct (fst (snd x1)) eqn:D.
  {
    repeat inv_exec_perm.
    destruct (fst (snd x7)) eqn:D0.
    eapply update_fblock_d_same_except with (f:=f2)(v':= b0) in H4; eauto; cleanup.
    do 3 eexists; split.
    econstructor; eauto.
    rewrite D0.
    repeat econstructor; eauto.
    rewrite <- H9; eauto.
    split; eauto.
    destruct_lift H; subst; eauto.
    rewrite H16; eauto.
    destruct_lift H; subst; eauto.
    rewrite H16; eauto.
    destruct_lift H.
    pred_apply; safecancel.
    destruct_lift H; subst; eauto.
    rewrite <- H14; eauto.
    destruct_lift H; subst; eauto.
    rewrite <- H14; eauto.
    destruct_lift H; subst; eauto.
    rewrite <- H14; eauto.
    rewrite H10 in D; cleanup; try congruence.
    right; eauto.
  }
  {
    repeat inv_exec_perm.
    do 3 eexists; split.
    econstructor; eauto.
    rewrite <- H10.
    rewrite D; repeat econstructor; eauto.
    left; eauto.
    split; auto.
  }
  pred_apply; cancel.
  eauto.
Qed.


Theorem copy_file_equivalent_for:
forall pr d1 bm1 d2 bm2 hm Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname1 inum1 f1 vs1 pathname2 inum2 f2 vs2 d1' bm1' hm' r tr, 
  (Fr * [[sync_invariant Fr]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm1 hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
   [[ find_subtree pathname1 tree = Some (TreeFile inum1 f1) ]] *
   [[[ (DFData f1) ::: (0 |-> vs1) ]]] *
   [[ find_subtree pathname2 tree = Some (TreeFile inum2 f2) ]] *
   [[[ (DFData f2) ::: (0 |-> vs2) ]]] *
   [[ can_access pr (DFOwner f1) ]] *
   [[ can_access pr (DFOwner f2) ]])%pred d1 ->
  exec pr d1 bm1 hm (copy_file fsxp inum1 inum2 mscs) (Finished d1' bm1' hm' r) tr ->
  (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
  (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2) ->
    exists d2' bm2', exec pr d2 bm2 hm (copy_file fsxp inum1 inum2 mscs) (Finished d2' bm2' hm' r) tr /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2').
Proof.
  unfold copy_file; intros.
  inv_exec_perm.
  edestruct read_fblock_post; eauto.
  unfold sys_rep; pred_apply; cancel; eauto.
  pred_apply; cancel.
  unfold sys_rep in *.
  eapply exec_equivalent_finished in H0; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.
  destruct (fst (snd x1)) eqn:D.
  {
    repeat inv_exec_perm.
    eapply exec_equivalent_finished in H3; eauto; cleanup.
    do 2 eexists; split.
    econstructor; eauto.
    rewrite D; repeat econstructor; eauto.
    split; eauto.
    pose proof (@update_fblock_d_ok fsxp inum2 0 b (fst x1) pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2_weak in *.
    edestruct Hok with (d:= x2).
    destruct_lift H.
    repeat eexists; pred_apply; norml.
    inversion H20.
    eassign Fr; cancel.
    inv_exec_perm.
    simpl in *.
    destruct_lift H8.
    eassign (fun (d0: rawdisk) (bm0: block_mem) (hm0: hashmap) (rx: (BFILE.memstate * (res unit * unit))) =>  True).
    left; repeat eexists; simpl in *; eauto.
    inv_exec_perm.
    simpl; auto.
    eassign (fun (_:block_mem) (_:hashmap) (_:rawdisk) => True).
    intros; simpl; auto.
    econstructor; eauto.
    econstructor.
    simpl in *; auto.
    apply trace_secure_impl; auto.
  }
  {
    repeat inv_exec_perm.
    do 2 eexists; split.
    econstructor; eauto.
    rewrite D; repeat econstructor; eauto.
    split; eauto.
  }
Qed.