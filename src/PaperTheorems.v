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
Require Import CopyFile.

Set Implicit Arguments.
Import AFS.
Import ListNotations.

Definition equivalent_for_principal u d0 bm0 (hm0:hashmap) d1 bm1 hm1:=
  (forall tag, can_access u tag ->
  equivalent_for tag d0 d1 /\
  blockmem_equivalent_for tag bm0 bm1) /\
  hm0 = hm1.

Definition ret_noninterference {T} (p: prog T):=
  forall u d0 bm0 hm0 d0' bm0' hm0' ret tr0 d1 bm1 hm1,
    exec u d0 bm0 hm0 p (Finished d0' bm0' hm0' ret) tr0 ->
    equivalent_for_principal u d0 bm0 hm0 d1 bm1 hm1 ->
    exists d1' bm1' hm1' tr1,
      exec u d1 bm1 hm1 p (Finished d1' bm1' hm1' ret) tr1.

Definition equivalent_state_for_principal {T} u (res0 res1: @result T) :=
  exists d0 bm0 hm0 d1 bm1 hm1,
    equivalent_for_principal u d0 bm0 hm0 d1 bm1 hm1 /\
    ((res0 = Crashed d0 bm0 hm0 /\ res1 = Crashed d1 bm1 hm1) \/
     (res0 = Failed d0 bm0 hm0 /\ res1 = Failed d1 bm1 hm1) \/
     (exists v0 v1, res0= Finished d0 bm0 hm0 v0 /\ res1 = Finished d1 bm1 hm1 v1)).                            
Definition state_noninterference {T} (p: prog T):=
  forall viewer caller d0 bm0 hm0 res0 tr0 d1 bm1 hm1,
    exec caller d0 bm0 hm0 p res0 tr0 ->
    equivalent_for_principal viewer d0 bm0 hm0 d1 bm1 hm1 ->
    exists res1 tr1,
      exec caller d1 bm1 hm1 p res1 tr1 /\
      equivalent_state_for_principal viewer res0 res1.

Definition unseal_safe {T} (p:prog T) :=
  forall u d bm hm res tr,
    exec u d bm hm p res tr ->
    forall perm,
      In perm tr -> op_secure u perm.

Definition op_public op:=
  match op with
  | Uns t => t = Public
  | _ => True
  end.

Definition unseal_public {T} (p:prog T) :=
  forall u d bm hm res tr,
    exec u d bm hm p res tr ->
    forall perm,
      In perm tr -> op_public perm.

Lemma unseal_safe_to_trace_secure:
  forall T (p: prog T),
    unseal_safe p ->
    (forall u d bm hm res tr,
        exec u d bm hm p res tr ->
        trace_secure u tr).
Proof.
  unfold unseal_safe; intros.
  specialize H with (1:= H0).
  clear H0.
  generalize dependent tr.
  induction tr; intros; simpl; auto.
  specialize (H a (in_cons_head tr a)) as Hx.
  unfold op_secure in Hx.
  split.
  destruct a; auto.
  eapply IHtr; intros.
  eapply H; apply in_cons; auto.
Qed.

Lemma unseal_public_to_only_public_operations:
  forall T (p: prog T),
    unseal_public p ->
    (forall u d bm hm res tr,
        exec u d bm hm p res tr ->
        only_public_operations tr).
Proof.
  unfold unseal_public; intros.
  specialize H with (1:= H0).
  clear H0.
  generalize dependent tr.
  induction tr; intros; simpl; auto.
  specialize (H a (in_cons_head tr a)) as Hx.
  unfold op_public in Hx.
  split.
  destruct a; auto.
  eapply IHtr; intros.
  eapply H; apply in_cons; auto.
Qed.

Theorem unseal_safe_to_ret_noninterference:
  forall T (p: prog T),
    unseal_safe p -> ret_noninterference p.
Proof.
  unfold ret_noninterference, equivalent_for_principal; intros.
  cleanup.
  eapply unseal_safe_to_trace_secure in H; eauto.
  eapply exec_equivalent_finished in H0; eauto.
  cleanup; repeat eexists; apply H0.
  intros t Ht; specialize (H1 t Ht); intuition.
  intros t Ht; specialize (H1 t Ht); intuition.
Qed.

Theorem unseal_public_to_state_noninterference:
  forall T (p: prog T),
    unseal_public p -> state_noninterference p.
Proof.
  unfold state_noninterference, equivalent_state_for_principal, equivalent_for_principal; intros.
  cleanup.
  eapply unseal_public_to_only_public_operations in H; eauto.
  eapply exec_equivalent_for_viewer in H0 as Hx; eauto.
  repeat split_ors; cleanup.
  do 2 eexists; repeat split; eauto.
  do 6 eexists; split.
  2: { right; right; repeat eexists; eauto. }
  split; auto.
  intros t Ht; intuition eauto.

  do 2 eexists; repeat split; eauto.
  do 6 eexists; split.
  2: { left; repeat eexists; eauto. }
  split; auto.

  do 2 eexists; repeat split; eauto.
  do 6 eexists; split.
  2: { right; left; repeat eexists; eauto. }
  split; auto.

  intros t Ht; specialize (H1 t Ht); intuition.
  intros t Ht; specialize (H1 t Ht); intuition.
Qed.


Theorem write_confidentiality:
forall caller d bm hm Fr fsxp ds mscs sm Fm Ftop tree ilist frees pathname inum f Fd vs d1 bm1 hm1 r1 tr1 off data0 data1, 
  (Fr * [[sync_invariant Fr]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  exec caller d bm hm (update_fblock_d fsxp inum off data0 mscs) (Finished d1 bm1 hm1 r1) tr1 ->
  DFOwner f <> Public ->
  exists d2 bm2 hm2 tr2 r2,
    exec caller d bm hm (update_fblock_d fsxp inum off data1 mscs) (Finished d2 bm2 hm2 r2) tr2 /\
  (forall adv, ~can_access adv (DFOwner f) -> equivalent_for_principal adv d1 bm1 hm1 d2 bm2 hm2).
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
    eauto.
    eauto.
    destruct_lift H4.
    inv_exec'' H7.
    left; repeat eexists; eauto.
    eassign (fun (d:rawdisk) (bm' :block_mem) (hm': hashmap) (r: BFILE.memstate * (res tag * unit)) =>
               let mscs' := fst r in let ok := fst (snd r) in
               (Fr * [[ sync_invariant Fr ]] *LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
               [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs' sm) ]]] *
               [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
               [[[ (DFData f) ::: (Fd * off |-> vs) ]]] *     
               ([[ isError ok ]] \/
                exists t, [[ ok = OK t ]] * [[ t = DFOwner f ]] * [[ can_access caller t ]]))%pred d); simpl ;auto.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inv_exec'' H7; simpl; auto.
    eassign (fun (_:block_mem) (_: hashmap) (_:rawdisk) => True); simpl;
      intros mx Hmx; simpl; auto.
  }
  simpl in *; clear Hspec; split_ors; cleanup; try congruence.
  eapply exec_same_except_finished in H0; eauto; cleanup.
  unfold pair_args_helper in *; simpl in *.
  apply sep_star_or_distr in H5; apply pimpl_or_apply in H5;
    split_ors; destruct_lift H5; cleanup.
  inversion H9.
  {
    Transparent LOG.commit_ro LOG.abort.
    unfold LOG.abort in *.
    repeat inv_exec_perm.
    do 5 eexists; split.
    econstructor; eauto.
    inversion H19; subst.
    simpl; rewrite <- app_nil_l; repeat econstructor; eauto.
    repeat split; simpl; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply same_except_to_equivalent_for; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply blockmem_same_except_to_equivalent_for; eauto.
  }
  {
    inversion H9; subst.
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
      inv_exec'' H9.
      left; repeat eexists; eauto.
      eassign (fun (_:rawdisk) (_:block_mem) (_: hashmap) (_: BFILE.memstate) => True); simpl ;auto.
      inv_exec'' H9; simpl; auto.
      eassign (fun (_:block_mem) (_: hashmap) (_:rawdisk) => True); simpl;
        intros mx Hmx; simpl; auto.
    }
    simpl in *; clear H2 Hspec.
    eapply exec_same_except_finished with (bm':=(Mem.upd x2 x8 (DFOwner f, data1)))in H8;
    eauto; cleanup.
    do 5 eexists; split.
    repeat econstructor; eauto.
    simpl; repeat econstructor; eauto.
    repeat split; simpl; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply same_except_to_equivalent_for; eauto.
    destruct (tag_dec tag (DFOwner f)); subst; intuition.
    eapply blockmem_same_except_to_equivalent_for; eauto.
    eapply blockmem_same_except_upd_same; eauto.
    apply only_public_operations_impl; auto.
  }
  congruence.
  apply same_except_refl.
  apply blockmem_same_except_refl.
  apply only_public_operations_impl; auto.
Qed.
