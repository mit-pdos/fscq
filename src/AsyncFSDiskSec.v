Require Import Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import PermDirCache.
Require Import PermGenSepN.
Require Import ListPred.
Require Import PermInode.
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
Require Import PermBFile.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Require Import DirTreeNames.
Require Import AsyncFS AsyncFSPost AsyncFSProg.

Set Implicit Arguments.
Import DirTree.
Import DIRTREE.
Import AFS.
Import ListNotations.

Notation MSLL := BFILE.MSLL.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSDBlocks := BFILE.MSDBlocks.

Definition equivalent_for tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 = tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).

Definition same_except tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 <> tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).


Definition permission_secure_fbasic {T} d bm hm fsxp mscs pr (p: fbasic T) :=
  forall tr tr' r mscs' ,
    exec_fbasic pr tr d bm hm fsxp mscs p r mscs' (tr'++tr) ->
    trace_secure pr tr'.

Lemma trace_app_fbasic:
  forall T (fp: fbasic T) tr d bm hm fsxp mscs pr out mscs' tr',
    exec_fbasic pr tr d bm hm fsxp mscs fp out mscs' tr' ->
    exists tr'', tr' = tr''++tr.
Proof.
  intros;
  inversion H; subst; try sigT_eq;
  denote exec as Hx; apply trace_app in Hx; auto.
Qed.



Fixpoint filter tag tree:=
  match tree with
  | TreeFile inum f =>
    if tag_dec tag (DFOwner f) then
      TreeFile inum f
    else
      TreeFile inum (mk_dirfile nil INODE.iattr0 (DFOwner f))
  | TreeDir inum ents =>
    TreeDir inum (map (fun st => (fst st, filter tag (snd st))) ents)
  end.

Definition tree_equivalent_for tag tree1 tree2:=
  filter tag tree1 = filter tag tree2.


Fixpoint only_reads_permitted {T} pr (p: prog T) d bm hm:=
  match p with
  | Read n => forall vs, d n = Some vs -> can_access pr (fst (fst vs))
  | Bind p1 p2 => only_reads_permitted pr p1 d bm hm /\
                 forall tr d' bm' hm' r tr',
                   exec pr tr d bm hm p1 (Finished d' bm' hm' r) tr' ->
                   only_reads_permitted pr (p2 r) d' bm' hm'
  | _ => True
  end.

(** Non-deterministic handle return bites us in here **)
Theorem exec_equivalent:
  forall T (p: prog T) pr tr d1 d2 bm hm d1' bm' hm' tr' (r: T),
    exec pr tr d1 bm hm p (Finished d1' bm' hm' r) tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr p d1 bm hm ->
    exists d2', exec pr tr d2 bm hm p (Finished d2' bm' hm' r) tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup;
  try solve [ eexists; split; [econstructor; eauto|]; eauto ].
  { (** Read **)
    unfold only_reads_permitted in *.
    destruct tb.
    specialize H1 with (1:= H14); simpl in *.    
    specialize H0 with (1:= H1) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    destruct x0, t0.
    unfold vsmerge in *; simpl in *.
    inversion H3; inversion H4; simpl in *; subst.
    intuition; cleanup.
    eexists; split; [econstructor; eauto|]; eauto.
  }

  { (** Write **)
    specialize H0 with (1:= can_access_public pr) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    destruct x0; repeat eexists; [econstructor; eauto|].
    unfold equivalent_for in *; intros.
    specialize H0 with (1:= H) as Hx.
    specialize (Hx a); intuition; cleanup; try congruence.
    destruct (Nat.eq_dec n a); subst; cleanup; try congruence.
    left; repeat rewrite Mem.upd_ne; eauto.
    destruct (Nat.eq_dec n a); subst; cleanup; try congruence.
    right; repeat rewrite Mem.upd_eq; eauto.
    repeat eexists; eauto.
    unfold vsmerge in *; simpl in *; eauto.
    unfold vsmerge in *; simpl in *; eauto.
    right; repeat rewrite Mem.upd_ne; eauto.
    repeat eexists; eauto.
  }

  { (** Sync **)
    repeat eexists; [econstructor; eauto|].
    unfold equivalent_for in *; intros.
    specialize H0 with (1:= H) as Hx.
    unfold sync_mem.
    specialize (Hx a); intuition; cleanup; eauto.
    destruct x, x0.
    right; repeat eexists; eauto.
    unfold vsmerge in *; simpl in *; eauto.
    inversion H4; subst.
    econstructor; eauto.
    unfold vsmerge in *; simpl in *; eauto.
    inversion H5; subst.
    econstructor; eauto.
  }
  
  { (** Bind **)
    destruct H2.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2); cleanup.
    specialize H4 with (1:=H0).
    specialize H with (1:=H3)(2:=H6)(3:=H4); cleanup.
    eexists; split; [econstructor; eauto|]; eauto.
  }
Qed.

Definition fbasic_to_prog {T} fsxp ams (fp: fbasic T): prog (BFILE.memstate * (T * unit)) :=
  match fp with
  | (read_fblock_f inum off) => read_fblock fsxp inum off ams
  | file_set_attr_f inum attr => file_set_attr fsxp inum attr ams
  | file_get_attr_f inum => file_get_attr fsxp inum ams
  | file_set_sz_f inum sz => file_set_sz fsxp inum sz ams
  | file_get_sz_f inum => file_get_sz fsxp inum ams
  | update_fblock_d_f inum off v => update_fblock_d fsxp inum off v ams
  | file_truncate_f inum sz => file_truncate fsxp inum sz ams
  | file_sync_f inum => file_sync fsxp inum ams
  | readdir_f inum => readdir fsxp inum ams
  | create_f dnum name tag => create fsxp dnum name tag ams
  | delete_f dnum name => delete fsxp dnum name ams
  | lookup_f dnum fnlist => lookup fsxp dnum fnlist ams
  | rename_f dnum srcpath srcname dstpath dstname => rename fsxp dnum srcpath srcname dstpath dstname ams
  | tree_sync_f => tree_sync fsxp ams
    | tree_sync_noop_f => tree_sync_noop fsxp ams
  end.

Fixpoint fprog_to_prog {T} fsxp ams (fp: fprog T): prog (BFILE.memstate * (T * unit)) :=
  match fp with
  | FBasic p => fbasic_to_prog fsxp ams p
  | FBind p bp => x <- (fbasic_to_prog fsxp ams p);; (fprog_to_prog fsxp (fst x) (bp (fst (snd x))))
  end.


Theorem exec_fbasic_equivalent:
  forall T (p: fbasic T) pr tr d1 d2 bm hm d1' bm' hm' tr' fsxp mscs mscs' (r: T),
    exec_fbasic pr tr d1 bm hm fsxp mscs p (Finished d1' bm' hm' r) mscs' tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr (fbasic_to_prog fsxp mscs p) d1 bm hm ->
    exists d2', exec_fbasic pr tr d2 bm hm fsxp mscs p (Finished d2' bm' hm' r) mscs' tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2').
Proof.
  unfold fbasic_to_prog; intros; destruct p;
  try solve
  [ inversion H; subst; try sigT_eq;
    denote exec as Hx;
    eapply exec_equivalent in Hx; eauto;
    cleanup; eexists; split; eauto;
    econstructor; eauto].
Qed.

  
Theorem fbasic_return :
 forall T (p: fbasic T) pr
   mscs mscs1' fsxp d1 bm hm d1' bm1' hm1' tr1 tr1' d2 (r: T),
   (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->                     
   exec_fbasic pr tr1 d1 bm hm fsxp mscs p (Finished d1' bm1' hm1' r) mscs1' tr1' ->
   only_reads_permitted pr (fbasic_to_prog fsxp mscs p) d1 bm hm ->
  exists d2',
    exec_fbasic pr tr1 d2 bm hm fsxp mscs p (Finished d2' bm1' hm1' r) mscs1' tr1' /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2').
Proof.
  intros. eapply exec_fbasic_equivalent; eauto.
Qed.


Lemma fbasic_to_prog_exec:
    forall T (p: fbasic T) pr tr d bm hm fsxp mscs  d' bm' hm' (v:T) ams' tr',
    exec_fbasic pr tr d bm hm fsxp mscs p (Finished d' bm' hm' v) ams' tr' ->
    exec pr tr d bm hm (fbasic_to_prog fsxp mscs p) (Finished d' bm' hm' ^(ams', v)) tr'.
  Proof.
    unfold fbasic_to_prog; intros; destruct p;
    inversion H; subst; repeat sigT_eq; eauto.
  Qed.


Theorem exec_fprog_equivalent:
  forall T (p: fprog T) pr tr d1 d2 bm hm d1' bm' hm' tr' fsxp mscs mscs' (r: T),
    fexec pr tr d1 bm hm fsxp mscs p (Finished d1' bm' hm' r) mscs' tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr (fprog_to_prog fsxp mscs p) d1 bm hm ->
    exists d2', fexec pr tr d2 bm hm fsxp mscs p (Finished d2' bm' hm' r) mscs' tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2').
Proof.
  unfold fprog_to_prog; induction p; intros.
  inversion H; subst; sigT_eq.
  eapply fbasic_return in H11; eauto.
  cleanup.
  eexists; split; eauto.
  econstructor; eauto.
  
  destruct H2.
  inversion H0; subst; repeat sigT_eq.
  eapply fbasic_return in H18 as Hx; eauto.
  cleanup.
  eapply fbasic_to_prog_exec in H18.
  specialize H3 with (1:=H18).
  specialize H with (1:=H19)(2:=H5)(3:=H3).
  cleanup.
  eexists; split; eauto.
  econstructor; eauto.
  inversion H19.
Qed.


 Lemma authenticate_post:
    forall Fr Fm Ftop pathname f dx ds sm tree mscs fsxp ilist frees d bm hm pr inum tr d' bm' hm' tr' (rx: (BFILE.memstate * (bool * unit))),
      
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds dx) (MSLL mscs) sm bm hm *
       [[[ dx ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
  
  exec pr tr d bm hm (authenticate fsxp inum mscs)
       (Finished d' bm' hm' rx) tr' ->
  let mscs':= fst rx in
  let r := fst (snd rx) in
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds dx) (MSLL mscs') sm bm' hm' *
   [[[ dx ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ MSCache mscs' = MSCache mscs ]] *
   [[ MSAllocC mscs' = MSAllocC mscs ]] *
   [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
   [[ MSDBlocks mscs' = MSDBlocks mscs ]] *
   (([[ r = true ]] * [[ can_access pr (DFOwner f) ]]) \/
    ([[ r = false ]] * [[ ~can_access pr (DFOwner f) ]])))%pred d'.
  Proof.
    unfold sys_rep, corr2; intros.
    pose proof (@authenticate_ok fsxp inum mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H1.
    eassign (fun d0 bm0 hm0 (rx: (BFILE.memstate * (bool * unit))) =>
               let a:= fst rx in
               let a1:= fst (snd rx) in
               (Fr
         ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds dx) (MSLL a) sm bm0 hm0 *
   [[[ dx ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) a sm) ]]] *
   [[ MSAlloc a = MSAlloc mscs ]] *
   [[ MSCache a = MSCache mscs ]] *
   [[ MSAllocC a = MSAllocC mscs ]] *
   [[ MSIAllocC a = MSIAllocC mscs ]] *
   [[ MSDBlocks a = MSDBlocks mscs ]] *
   (([[ a1 = true ]] * [[ can_access pr (DFOwner f) ]]) \/
    ([[ a1 = false ]] * [[ ~can_access pr (DFOwner f) ]])))%pred d0).
    left; repeat eexists; simpl in *; eauto.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    unfold permission_secure; intros.
    inv_exec_perm.
    cleanup; auto.
    unfold trace_secure; eauto.
    eassign (fun (_:block_mem) (_:hashmap) (_:rawdisk) => True).
    intros; simpl; auto.
    econstructor; eauto.
    econstructor.
    simpl in *.
    destruct rx, p.
    intuition; cleanup.
    sigT_eq; eauto.
    destruct_lift H; subst.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inversion H1.
  Qed.



  Lemma LOG_begin_post:
    forall Fr ds sm mscs fsxp d bm hm pr tr d' bm' hm' tr' (rx: LOG.mstate * cachestate),
      
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm)%pred d ->
  
  exec pr tr d bm hm (LOG.begin (FSXPLog fsxp) (MSLL mscs))
       (Finished d' bm' hm' rx) tr' ->
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) rx sm bm' hm' *
  [[ LOG.readOnly (MSLL mscs) rx ]])%pred d'.
  Proof.
     unfold sys_rep, corr2; intros.
    pose proof (@LOG.begin_ok (FSXPLog fsxp) (MSLL mscs) pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H1.
    eassign (fun d0 bm0 hm0 (rx: LOG.mstate * cachestate) =>
               let a:= fst rx in
               let b:= snd rx in
               (Fr
        ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds !!) 
            (a, b) sm bm0 hm0 * [[ LOG.readOnly (MSLL mscs) (a, b) ]] )%pred d0).
    left; repeat eexists; simpl in *; eauto.
    pred_apply; cancel.
    unfold permission_secure; intros.
    inv_exec_perm.
    cleanup; auto.
    unfold trace_secure; eauto.
    eassign (fun (_:block_mem) (_:hashmap) (_:rawdisk) => True).
    intros; simpl; auto.
    econstructor; eauto.
    econstructor.
    simpl in *.
    destruct rx.
    intuition; cleanup.
    sigT_eq; eauto.
    destruct_lift H; subst.
    pred_apply; cancel.
    inversion H1.
  Qed.


Require Import FMapAVL.
Require Import FMapFacts.
Import AddrMap.
Import Map MapFacts.

Lemma maybe_evict_post:
    forall Fr d dx cs bm hm pr tr d' bm' hm' tr' cs',
      (Fr * [[ sync_invariant Fr ]] * PermCacheDef.rep cs dx bm)%pred d ->
      exec pr tr d bm hm (maybe_evict cs)
           (Finished d' bm' hm' cs') tr' ->
      (Fr * [[ sync_invariant Fr ]] *
       PermCacheDef.rep cs' dx bm' *
      [[ forall a, find a (CSMap cs) = None ->
              find a (CSMap cs') = None ]] *                 
      [[ cardinal (CSMap cs') < CSMaxCount cs' ]])%pred d'.
    Proof.
      intros.
      pose proof (@maybe_evict_ok cs pr) as Hok.
      specialize (Hok _ (fun r => Ret r)).
      unfold corr2 in *.
      edestruct Hok with (d:= d).
      pred_apply; cancel.
      eauto.
      eauto.
      inv_exec_perm.
      simpl in *.
      destruct_lift H1.
      eassign (fun d0 (bm0: block_mem) (hm0:hashmap) cs' =>
                 (Fr * PermCacheDef.rep cs' dx bm0 *
                 [[ forall a, find a (CSMap cs) = None ->
                         find a (CSMap cs') = None ]] *                 
                 [[ cardinal (CSMap cs') < CSMaxCount cs' ]])%pred d0).
      left; repeat eexists; simpl in *; eauto.
      pred_apply; cancel.
      unfold permission_secure; intros.
      inv_exec_perm.
      cleanup; auto.
      unfold trace_secure; eauto.
      eassign (fun (_:block_mem) (_:hashmap) (_:rawdisk) => True).
      intros; simpl; auto.
      econstructor; eauto.
      econstructor.
      simpl in *.
      intuition; cleanup.
      sigT_eq; eauto.
      destruct_lift H; subst.
      pred_apply; cancel.
      inversion H1.
    Qed.

Lemma LOG_begin_orp:
  forall pr a b d bm hm,
    only_reads_permitted pr (LOG.begin a b) d bm hm.
Proof.
  intros.
  Transparent LOG.begin.
  unfold LOG.begin; simpl; auto.
Qed.

Lemma writeback_orp:
  forall pr a b d bm hm,
    only_reads_permitted pr (writeback a b) d bm hm.
Proof.
  unfold writeback; simpl; intros.
  destruct (MapUtils.AddrMap.Map.find a (CSMap b)); simpl; auto.
  destruct p; simpl; auto.
  destruct b0; simpl; auto.
Qed.

Hint Resolve LOG_begin_orp writeback_orp.

Lemma maybe_evict_orp:
  forall pr a d bm hm,
    only_reads_permitted pr (maybe_evict a) d bm hm.
Proof.
  unfold maybe_evict; simpl; intros.
  destruct (lt_dec (CSCount a) (CSMaxCount a)); simpl; auto.
  destruct (MapUtils.AddrMap.Map.find 0 (CSMap a)); simpl; auto.
  intuition; simpl.
  destruct (MapUtils.AddrMap.Map.find 0 (CSMap r)); simpl; auto.
  destruct (MapUtils.AddrMap.Map.elements (CSMap a)); simpl; auto.
  destruct p; simpl; auto.
  intuition.
  destruct (MapUtils.AddrMap.Map.find k (CSMap r)); simpl; auto.
Qed.

Hint Resolve maybe_evict_orp.

Lemma PermCacheDef_read_orp:
    forall Fr pr a cs dx d bm hm v,
      (Fr * [[ sync_invariant Fr ]] * PermCacheDef.rep cs dx bm)%pred d ->
      can_access pr (fst (fst v)) ->
      dx a = Some v ->
      only_reads_permitted pr (PermCacheDef.read a cs) d bm hm.
  Proof.
    intros; unfold PermCacheDef.read; simpl.
    destruct (MapUtils.AddrMap.Map.find a (CSMap cs)) eqn:D; simpl; auto.
    destruct p; simpl; auto.
    intuition; simpl.   
    pose proof (maybe_evict_post H H2) as Hspec.
    destruct_lift Hspec.
    specialize H8 with (1:=D).
    unfold PermCacheDef.rep in *.
    rewrite mem_pred_extract in H4; eauto.
    unfold cachepred at 2 in H4.
    rewrite H8 in H4.
    repeat rewrite sep_star_assoc in H4.
    apply sep_star_assoc in H4.
    apply sep_star_assoc in H4.
    apply sep_star_assoc in H4.
    eapply ptsto_subset_valid' in H4.
    simpl in *; cleanup; eauto.
  Qed.

  

  Lemma getowner_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      only_reads_permitted pr (getowner fsxp inum mscs) d bm hm.
  Proof.
    intros; unfold getowner.

  Lemma BFILE_getowner_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      only_reads_permitted pr (BFILE.getowner (FSXPLog fsxp) (FSXPInode fsxp) inum mscs) d bm hm.
  Proof.
    intros; unfold BFILE.getowner.


  Lemma INODE_getowner_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      only_reads_permitted pr (INODE.getowner (FSXPLog fsxp) (FSXPInode fsxp) inum (MSICache mscs) (MSLL mscs)) d bm hm.
  Proof.
    intros; unfold INODE.getowner.



  Lemma INODE_IRec_get_array_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      only_reads_permitted pr (INODE.IRec.get_array (FSXPLog fsxp) (FSXPInode fsxp) inum (MSICache mscs) (MSLL mscs)) d bm hm.
  Proof.
    intros; unfold INODE.IRec.get_array.

   Lemma INODE_IRec_get_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      only_reads_permitted pr (INODE.IRec.get (FSXPLog fsxp) (FSXPInode fsxp) inum (MSICache mscs) (MSLL mscs)) d bm hm.
  Proof.
    intros; unfold INODE.IRec.get.
    destruct (INODE.IRec.Cache.find inum (MSICache mscs)) eqn:D;
    setoid_rewrite D.
    simpl; auto.

  Lemma INODE_IRec_LRA_get_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      only_reads_permitted pr (INODE.IRec.LRA.get (FSXPLog fsxp) (FSXPInode fsxp) inum (MSLL mscs)) d bm hm.
  Proof.
    intros; unfold INODE.IRec.LRA.get.

 Lemma LOG_read_array_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      only_reads_permitted pr (LOG.read_array (FSXPLog fsxp) (INODE.IRecSig.RAStart (FSXPInode fsxp))
       (inum / INODE.IRecSig.items_per_val) (MSLL mscs)) d bm hm.
  Proof.
    intros; unfold LOG.read_array.
    simpl; intuition.
    destruct_lift H.
    denote LOG.rep as Hx.
    unfold LOG.rep, LOG.rep_inner, GLog.rep, MLog.rep, MLog.synced_rep in Hx. destruct_lift Hx.
    assert (INODE.IRecSig.RAStart (FSXPInode fsxp) +
            inum / INODE.IRecSig.items_per_val < length dummy1).
    destruct fsxp; simpl in *.

    denote rep as Hx.
    unfold rep, FSXPBlockAlloc in Hx; destruct_lift Hx; simpl in *.
    denote BFILE.rep as Hx. unfold BFILE.rep in Hx.
    destruct_lift Hx.
    denote INODE.rep as Hx. unfold INODE.rep, INODE.IRec.rep, INODE.IRec.LRA.rep in Hx.
    destruct_lift Hx.
    destruct mscs, MSLL, m, MSGLog; simpl in *.
    unfold LogReplay.map_replay in *.
    unfold LogReplay.map_valid in *.
    Search dummy1.
    Search MSMLog.
    unfold PermDiskLog.rep, rep_common,
    PermDiskLogPadded.rep, rep_inner, rep_contents in *.
    Search dummy0.
    Search MSTxns.
    Search GLog.effective.
    unfold LOG.MSLL; simpl.
    destruct ms_1; simpl in *.
    eapply GLog_read_orp.
    pred_apply; cancel.
    

    Lemma MLog_read_orp:
    forall v pr d bm hm Fr a log ds Ftop MSMLog ms_2 (MSTxns: list input_contents) dummy dx ,
      (Fr * [[ sync_invariant Fr ]] *
      PermCacheDef.rep ms_2 dx bm)%pred d ->
      dx (DataStart log + a) = Some v ->
      can_access pr (fst (fst v)) ->
      (Ftop * MLog.rep log (MLog.Synced dummy (nthd (length (snd ds) - length MSTxns) ds)) MSMLog bm hm)%pred dx ->
      only_reads_permitted pr  (MLog.read log a (MLog.mk_memstate MSMLog ms_2)) d bm hm.
  Proof.
    intros; unfold MLog.read.
    destruct (MapUtils.AddrMap.Map.find a (MLog.MSInLog (MLog.mk_memstate MSMLog ms_2))) eqn:D.
    simpl; auto.
    simpl; intuition.
    eapply PermCacheDef_read_orp; eauto.
  Qed.
    
    Lemma GLog_read_orp:
    forall v pr d bm hm Fr a log dx MSGLog ms_2 ds Ftop,
      (Fr * [[ sync_invariant Fr ]] *
       PermCacheDef.rep ms_2 dx bm)%pred d ->
      dx (DataStart log + a) = Some v ->
      can_access pr (fst (fst v)) ->
     (Ftop ✶ GLog.rep log (GLog.Cached ds) MSGLog bm hm)%pred dx ->
      only_reads_permitted pr (GLog.read log a (MSGLog, ms_2)) d bm hm.
  Proof.
    intros; unfold GLog.read.
    destruct (MapUtils.AddrMap.Map.find a (GLog.MSVMap (fst (MSGLog, ms_2)))) eqn:D.
    simpl; auto.
    simpl; intuition.
    denote GLog.rep as Hx.
    unfold GLog.rep in Hx; destruct_lift Hx.
    destruct MSGLog; simpl in *.
    unfold GLog.MSLL; simpl.
    eapply MLog_read_orp; eauto.
  Qed.


 Lemma LOG_read_orp:
    forall v pr d bm hm log a Fr ds sm ms Ftop,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep log Ftop (LOG.ActiveTxn ds ds !!) ms sm bm hm)%pred d ->
      d (DataStart log + a) = Some v ->
      can_access pr (fst (fst v)) ->
      only_reads_permitted pr (LOG.read log a ms) d bm hm.
  Proof.
    intros; unfold LOG.read.
    destruct (MapUtils.AddrMap.Map.find a (LOG.MSTxn (fst ms))) eqn:D.
    simpl; auto.
    simpl; auto; intuition.
    denote LOG.rep as Hx.
    unfold LOG.rep in Hx. destruct_lift Hx.
    unfold LOG.MSLL; simpl.
    destruct ms_1; simpl in *.
    eapply GLog_read_orp.
    pred_apply; cancel.
    
  
  
    Lemma read_array_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val) (LOG.MSTxn (fst (MSLL mscs))) =
      None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (GLog.MSVMap (fst (LOG.MSLL (MSLL mscs)))) = None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (MLog.MSInLog (GLog.MSLL (LOG.MSLL (MSLL mscs)))) = None ->
      only_reads_permitted pr (read_array (DataStart (FSXPLog fsxp))
                                (INODE.IRecSig.RAStart (FSXPInode fsxp) +
                                  inum / INODE.IRecSig.items_per_val)
                                   (MLog.MSCache (GLog.MSLL (LOG.MSLL (MSLL mscs))))) d bm hm.
  Proof.
    intros; unfold read_array.
    simpl; intuition.
    unfold LOG.rep in *.
    destruct_lift H.
    eapply PermCacheDef_read_orp.
    pred_apply; cancel.

    unfold LOG.rep_inner in *.
    destruct_lift H8.
    unfold GLog.rep in *.
    destruct_lift H4.
    unfold MLog.rep in *.
    destruct_lift H4.
    unfold PermDiskLog.rep in *.
    destruct_lift H4.















    (*******************************************************)

 Lemma LOG_read_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      only_reads_permitted pr (LOG.read (FSXPLog fsxp)
       (INODE.IRecSig.RAStart (FSXPInode fsxp) +
        inum / INODE.IRecSig.items_per_val) (MSLL mscs)) d bm hm.
  Proof.
    intros; unfold LOG.read.
    destruct (MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val) (LOG.MSTxn (fst (MSLL mscs)))) eqn:D.
    simpl; auto.



    Lemma GLog_read_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val) (LOG.MSTxn (fst (MSLL mscs))) =
      None ->
      only_reads_permitted pr (GLog.read (FSXPLog fsxp)
                               (INODE.IRecSig.RAStart (FSXPInode fsxp) +
                                inum / INODE.IRecSig.items_per_val)
                                 (LOG.MSLL (MSLL mscs))) d bm hm.
  Proof.
    intros; unfold GLog.read.
    destruct (MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (GLog.MSVMap (fst (LOG.MSLL (MSLL mscs))))) eqn:D.
    simpl; auto.


    Lemma MLog_read_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val) (LOG.MSTxn (fst (MSLL mscs))) =
      None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (GLog.MSVMap (fst (LOG.MSLL (MSLL mscs)))) = None ->
      only_reads_permitted pr (MLog.read (FSXPLog fsxp)
                                (INODE.IRecSig.RAStart (FSXPInode fsxp) +
                                  inum / INODE.IRecSig.items_per_val)
                                   (GLog.MSLL (LOG.MSLL (MSLL mscs)))) d bm hm.
  Proof.
    intros; unfold MLog.read.
    destruct (MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (MLog.MSInLog (GLog.MSLL (LOG.MSLL (MSLL mscs))))) eqn:D.
    simpl; auto.

    Lemma read_array_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      INODE.IRec.Cache.find inum (MSICache mscs) = None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val) (LOG.MSTxn (fst (MSLL mscs))) =
      None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (GLog.MSVMap (fst (LOG.MSLL (MSLL mscs)))) = None ->
      MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp) +
         inum / INODE.IRecSig.items_per_val)
        (MLog.MSInLog (GLog.MSLL (LOG.MSLL (MSLL mscs)))) = None ->
      only_reads_permitted pr (read_array (DataStart (FSXPLog fsxp))
                                (INODE.IRecSig.RAStart (FSXPInode fsxp) +
                                  inum / INODE.IRecSig.items_per_val)
                                   (MLog.MSCache (GLog.MSLL (LOG.MSLL (MSLL mscs))))) d bm hm.
  Proof.
    intros; unfold read_array.
    simpl; intuition.
    unfold LOG.rep in *.
    destruct_lift H.
    eapply PermCacheDef_read_orp.
    pred_apply; cancel.

    unfold LOG.rep_inner in *.
    destruct_lift H8.
    unfold GLog.rep in *.
    destruct_lift H4.
    unfold MLog.rep in *.
    destruct_lift H4.
    unfold PermDiskLog.rep in *.
    destruct_lift H4.

  Lemma authenticate_orp:
    forall pr d bm hm fsxp inum mscs pathname Fr Fm ds sm Ftop tree ilist frees f,
      (Fr * [[ sync_invariant Fr ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.ActiveTxn ds ds !!) (MSLL mscs) sm bm hm *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
       [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
      only_reads_permitted pr (authenticate fsxp inum mscs) d bm hm.
  Proof.
    intros; unfold authenticate.
    
    simpl; auto.
    intuition; simpl.
    unfold rep, BFILE.rep in *.

Lemma read_fblock_orp:
  forall pathname f pr off vs inum Fd
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 fsxp1 ilist1 frees1 d bm1 hm1,
  (Fr1 * [[ sync_invariant Fr1 ]] *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm1 * rep fsxp1 Ftop1 tree1 ilist1 frees1 mscs1 sm1)]]] *
      [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  only_reads_permitted pr (read_fblock fsxp1 inum off mscs1) d bm1 hm1.
Proof.  
  unfold read_fblock; simpl.
  intuition; simpl; auto.

  assert (A: (Fr1 ✶ ⟦⟦ sync_invariant Fr1 ⟧⟧
          ✶ LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) 
          (MSLL mscs1) sm1 bm1 hm1)%pred d).
    pred_apply; cancel.
    pose proof (LOG_begin_post _ A H0) as Hspec1.

  (((Fr1 ✶ ⟦⟦ sync_invariant Fr1 ⟧⟧)
             ✶ LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1)
                 (LOG.ActiveTxn ds1 ds1 !!) r sm1 bm' hm')
     ✶ ⟦⟦ LOG.readOnly (MSLL mscs1) r ⟧⟧ *
   [[[ ds1!! ::: (Fm1 * rep fsxp1 Ftop1 tree1 ilist1 frees1 mscs1 sm1)]]] *
      [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]])%pred d'

        
  Lemma MLog_read_orp:
    forall pr a b c d bm hm dx v Fr,
      (Fr * [[ sync_invariant Fr ]] *
       PermCacheDef.rep (MLog.MSCache c) dx bm)%pred d ->
      can_access pr (fst (fst v)) ->
      dx (DataStart a + b) = Some v ->
      only_reads_permitted pr (MLog.read a b c) d bm hm.
  Proof.
    intros; unfold MLog.read; simpl; auto.
    destruct (MapUtils.AddrMap.Map.find b (MLog.MSInLog c)); simpl; auto.
    intuition; simpl.      
    eapply PermCacheDef_read_orp; eauto.
  Qed.
    
  Lemma INODE_IRec_get_orp:
    forall pr a b c x y d bm hm Fr1 sm ds dx k,
    (Fr1 * [[ sync_invariant Fr1 ]]
     * LOG.rep a k (LOG.ActiveTxn ds dx) y sm bm hm)%pred d ->
    only_reads_permitted pr (INODE.IRec.get a b c x y) d bm hm.
  Proof.
    intros; unfold INODE.IRec.get; simpl.
    destruct (INODE.IRec.Cache.find c x) eqn:D;
    setoid_rewrite D; simpl; auto.
    intuition; simpl.

    Lemma LOG_read_orp:
      forall pr a b c d bm hm Fr1 k ds dx sm,
        ((Fr1 ✶ ⟦⟦ sync_invariant Fr1 ⟧⟧) ✶ LOG.rep a k (LOG.ActiveTxn ds dx) c sm bm hm)%pred d ->
        only_reads_permitted pr (LOG.read a b c) d bm hm.
    Proof.
      intros; unfold LOG.read; simpl.
      destruct (MapUtils.AddrMap.Map.find b (LOG.MSTxn (fst c))) eqn:D; simpl; auto.
      intuition; simpl.
      unfold LOG.rep, LOG.rep_inner in *.
      destruct_lift H.

      Lemma GLog_read_orp:
        forall pr a b c d bm hm dx v Fr,
          (Fr * [[ sync_invariant Fr ]] *
           PermCacheDef.rep (MLog.MSCache (GLog.MSLL c)) dx bm)%pred d ->
          can_access pr (fst (fst v)) ->
          dx (DataStart a + b) = Some v ->
          only_reads_permitted pr (GLog.read a b c) d bm hm.
      Proof.
        intros; unfold GLog.read; simpl.
        destruct (MapUtils.AddrMap.Map.find b
                  (GLog.MSVMap (fst c))) eqn:D; simpl; auto.
        intuition; simpl.

        

      eapply MLog_read_orp; eauto.
      
          
    unfold maybe_evict; simpl.
    destruct (lt_dec (CSCount (snd r)) (CSMaxCount (snd r))); simpl; eauto.
    destruct (MapUtils.AddrMap.Map.find 0 (CSMap (snd r))); simpl; auto.
    intuition; simpl.
    unfold writeback; simpl.
    destruct (MapUtils.AddrMap.Map.find 0 (CSMap (snd r))); simpl; auto.
    destruct p; simpl; auto.
    destruct b1; simpl; auto.
    destruct (MapUtils.AddrMap.Map.find 0 (CSMap r0)); simpl; auto.
    destruct (MapUtils.AddrMap.Map.elements (CSMap (snd r))); simpl; auto.
    destruct p; auto.
    unfold evict; simpl; auto.
    intuition; simpl.
    unfold writeback; simpl.
    destruct (MapUtils.AddrMap.Map.find k (CSMap (snd r))); simpl; auto.
    destruct p; simpl; auto.
    destruct b1; simpl; auto.
    destruct (MapUtils.AddrMap.Map.find k (CSMap r0)); simpl; auto.

    admit. (** An Actual Goal **)

  - assert (A: (Fr1 ✶ ⟦⟦ sync_invariant Fr1 ⟧⟧
          ✶ LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) 
          (MSLL mscs1) sm1 bm1 hm1)%pred d).
    pred_apply; cancel.
    pose proof (LOG_begin_post _ A H0) as Hspec1.
    assert (A0: (Fr1 * [[ sync_invariant Fr1 ]]
             * LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1)
                 (LOG.ActiveTxn ds1 ds1 !!) (MSLL {|
            BFILE.MSAlloc := MSAlloc mscs1;
            BFILE.MSLL := r;
            BFILE.MSAllocC := MSAllocC mscs1;
            BFILE.MSIAllocC := MSIAllocC mscs1;
            BFILE.MSICache := MSICache mscs1;
            BFILE.MSCache := MSCache mscs1;
            BFILE.MSDBlocks := MSDBlocks mscs1 |}) sm1 bm' hm' *
       [[[  ds1 !! ::: Fm1 * rep fsxp1 Ftop1 tree1 ilist1 (a, b) mscs1 sm1 ]]] *
       [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]])%pred d').
    destruct_lift H.
    pred_apply; cancel.
    pose proof (authenticate_post _ A0 H1) as Hspec2.
    apply sep_star_or_distr in Hspec2.
    apply pimpl_or_apply in Hspec2.
    intuition; simpl in *; destruct_lift H2.
  + intuition; simpl; auto.
      
    unfold INODE.IRec.get; simpl; auto.
    destruct (INODE.IRec.Cache.find inum (MSICache a0)) eqn:D;
    setoid_rewrite D; simpl; auto.
    intuition; simpl.
    unfold LOG.read; simpl; auto.
    destruct (MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp1) +
         inum / INODE.IRecSig.items_per_val) (LOG.MSTxn (fst (MSLL a0)))); simpl; auto.
    unfold GLog.read; simpl; auto.
    intuition; simpl.
    destruct (MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp1) +
         inum / INODE.IRecSig.items_per_val)
        (GLog.MSVMap (LOG.MSGLog (fst (MSLL a0))))); simpl; auto.
    intuition; simpl.
    unfold MLog.read; simpl; auto.
    destruct (MapUtils.AddrMap.Map.find
        (INODE.IRecSig.RAStart (FSXPInode fsxp1) +
         inum / INODE.IRecSig.items_per_val)
        (GLog.MSMLog (LOG.MSGLog (fst (MSLL a0))))); simpl; auto.
    intuition; simpl.
    unfold PermCacheDef.read; simpl; auto.
    destruct (MapUtils.AddrMap.Map.find
        (DataStart (FSXPLog fsxp1) +
         (INODE.IRecSig.RAStart (FSXPInode fsxp1) +
          inum / INODE.IRecSig.items_per_val)) (CSMap (snd (MSLL a0)))); simpl; auto.
    destruct p; simpl; auto.
    intuition; simpl.

    
      
    
    unfold maybe_evict; simpl; auto.