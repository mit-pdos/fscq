Require Import Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import PermDirCache.
Require Import PermGenSepN.
Require Import ListPred.
(* Require Import Idempotent. *)
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
Require Import AsyncFS.

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


Definition sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm:=
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]])%pred.


 Lemma read_fblock_post:
   forall Fr Fm Ftop pathname f Fd ds sm tree mscs fsxp ilist frees d bm hm pr off vs inum tr d' bm' hm' tr' (rx: (BFILE.memstate * (block * res unit * unit))),
     
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  
  exec pr tr d bm hm (read_fblock fsxp inum off mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let r := fst (fst (snd rx)) in
  let ok := snd (fst (snd rx)) in
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   (([[ isError ok ]] *
     [[ r = $0 ]] * [[ ~can_access pr (DFOwner f) ]]) \/
    ([[ ok = OK tt ]] *
     [[ r = snd (fst vs) ]] * [[ can_access pr (DFOwner f) ]])))%pred d'.
  Proof.
    unfold sys_rep, corr2; intros.
    pose proof (@read_fblock_ok fsxp inum off mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H2.
    eassign (fun d0 bm0 hm0 (rx: (BFILE.memstate * (block * res unit * unit))) =>
     let a:= fst rx in let a1:= fst (fst (snd rx)) in let b:= snd (fst (snd rx)) in
    (Fr ✶ (((LOG.rep (FSXPLog fsxp) (SB.rep fsxp) 
                   (LOG.NoTxn ds) (MSLL a) sm bm0 hm0
                 ✶ 【 ds !!
                   ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】)
                ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
               ✶ (⟦⟦ isError b ⟧⟧ ✶ ⟦⟦ a1 = $ (0) ⟧⟧ * [[ ~can_access pr (DFOwner f) ]]
                  ⋁ ⟦⟦ b = OK tt ⟧⟧ ✶ ⟦⟦ a1 = snd (fst vs) ⟧⟧ * [[ can_access pr (DFOwner f) ]])))%pred d0).
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
    destruct rx, p, p.
    intuition; cleanup.
    sigT_eq; eauto.
    destruct_lift H; subst.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inversion H1.
  Qed.

  Lemma file_get_attr_post:
    forall Fr Fm Ftop pathname f ds sm tree mscs fsxp ilist frees d bm hm pr inum tr d' bm' hm' tr' (rx: (BFILE.memstate * (Rec.data INODE.attrtype * res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
  
  exec pr tr d bm hm (file_get_attr fsxp inum mscs)
       (Finished d' bm' hm' rx) tr' ->
  let mscs':= fst rx in
  let r := fst (fst (snd rx)) in
  let ok := snd (fst (snd rx)) in
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs /\ MSCache mscs' = MSCache mscs ]] *
   (([[ isError ok ]] *
     [[ r = INODE.iattr0 ]] * [[ ~can_access pr (DFOwner f) ]]) \/
    ([[ ok = OK tt ]] *
     [[ r = DFAttr f ]] * [[ can_access pr (DFOwner f) ]])))%pred d'.
  Proof.
    unfold sys_rep, corr2; intros.
    pose proof (@file_getattr_ok fsxp inum mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H1.
    eassign (fun d0 bm0 hm0 (rx: (BFILE.memstate * (Rec.data INODE.attrtype * res unit * unit))) =>
               let a:= fst rx in
               let a1:= fst (fst (snd rx)) in
               let b:= snd (fst (snd rx)) in
               ((Fr
         ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
         (MSLL a) sm bm0 hm0)
         ✶ 【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】
         ✶ ⟦⟦ MSAlloc a = MSAlloc mscs /\ MSCache a = MSCache mscs ⟧⟧
        ✶ ((⟦⟦ isError b ⟧⟧
            ✶ ⟦⟦ a1 = INODE.iattr0 ⟧⟧)
           ✶ ⟦⟦ can_access pr (DFOwner f) -> False ⟧⟧
           ⋁ (⟦⟦ b = OK tt ⟧⟧
              ✶ ⟦⟦ a1 = DFAttr f ⟧⟧)
             ✶ ⟦⟦ can_access pr (DFOwner f) ⟧⟧))%pred d0).
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
    destruct rx, p, p.
    intuition; cleanup.
    sigT_eq; eauto.
    destruct_lift H; subst.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inversion H1.
  Qed.


Lemma file_get_sz_post:
    forall Fr Fm Ftop pathname f ds sm tree mscs fsxp ilist frees d bm hm pr inum tr d' bm' hm' tr' (rx: (BFILE.memstate * (word 64 * res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
  
  exec pr tr d bm hm (file_get_sz fsxp inum mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let r := fst (fst (snd rx)) in
  let ok := snd (fst (snd rx)) in
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs /\ MSCache mscs' = MSCache mscs ]] *
   (([[ isError ok ]] *
     [[ r = INODE.ABytes (INODE.iattr0) ]] *
     [[ ~can_access pr (DFOwner f) ]]) \/
    ([[ ok = OK tt ]] *
     [[ r = INODE.ABytes (DFAttr f) ]] *
     [[ can_access pr (DFOwner f) ]])))%pred d'.
  Proof.
    unfold sys_rep, corr2; intros.
    pose proof (@file_get_sz_ok fsxp inum mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H1.
    eassign (fun d0 bm0 hm0 (rx: (BFILE.memstate * (word 64 * res unit * unit))) =>
               let a:= fst rx in
               let a1:= fst (fst (snd rx)) in
               let b:= snd (fst (snd rx)) in
               ((Fr
         ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
         (MSLL a) sm bm0 hm0)
         ✶ 【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】
         ✶ ⟦⟦ MSAlloc a = MSAlloc mscs /\ MSCache a = MSCache mscs ⟧⟧
        ✶ ((⟦⟦ isError b ⟧⟧
            ✶ ⟦⟦ a1 = $0 ⟧⟧) ✶ ⟦⟦ can_access pr (DFOwner f) -> False ⟧⟧
           ⋁ (⟦⟦ b = OK tt ⟧⟧ ✶ ⟦⟦ a1 = INODE.ABytes (DFAttr f) ⟧⟧)
             ✶ ⟦⟦ can_access pr (DFOwner f) ⟧⟧))%pred d0).
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
    destruct rx, p, p.
    intuition; cleanup.
    sigT_eq; eauto.
    destruct_lift H; subst.
    pred_apply; cancel.
    or_l; cancel.
    or_r; cancel.
    inversion H1.
  Qed.

  Lemma update_fblock_d_post:
    forall Fr Fm Ftop pathname f Fd ds sm tree mscs fsxp ilist frees d bm hm pr off vs v inum tr d' bm' hm' tr' (r: (BFILE.memstate * (res unit * unit))),
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  exec pr tr d bm hm (update_fblock_d fsxp inum off v mscs) (Finished d' bm' hm' r) tr' ->
  let (mscs', ok') := r in let (ok, _) := ok' in
       (([[ isError ok ]] * [[ ~can_access pr (DFOwner f) ]] *
       sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm' *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]]) \/       
     ([[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]] *
       exists tree' f' ds' sm' bn,
       sys_rep Fr Fm Ftop fsxp ds' sm' tree' ilist frees mscs' bm' hm' *
       [[ ds' = dsupd ds bn ((DFOwner f, v), vsmerge vs) ]] *
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       (* spec about files on the latest diskset *)
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (DFData f') ::: (Fd * off |-> ((DFOwner f, v), vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]] *
       [[ DFOwner f' = DFOwner f ]] *
       [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                       ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]))%pred d'.
  Proof.
    unfold sys_rep, corr2; intros.
    pose proof (@update_fblock_d_ok fsxp inum off v mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel. 
    eauto.
    eauto.
    inv_exec_perm.
    destruct_lift H2.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in let (a0, _) := ok' in
     (Fr
        ✶ (((((((⟦⟦ isError a0 ⟧⟧ ✶ ⟦⟦ can_access pr (DFOwner f) -> False ⟧⟧)
                ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) 
                    (LOG.NoTxn ds) (MSLL a) sm bm0 hm0)
               ✶ 【 ds !!
                 ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】)
              ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
             ✶ ⟦⟦ MSCache a = MSCache mscs ⟧⟧)
            ✶ ⟦⟦ MSAllocC a = MSAllocC mscs ⟧⟧)
           ✶ ⟦⟦ MSIAllocC a = MSIAllocC mscs ⟧⟧
           ⋁ (⟦⟦ a0 = OK tt ⟧⟧ ✶ ⟦⟦ can_access pr (DFOwner f) ⟧⟧)
             ✶ (exists
                  (tree' : dirtree) (f' : dirfile) (ds' : diskset) 
                (sm' : Mem.mem) (bn : addr),
                  (((((((((((LOG.rep (FSXPLog fsxp) 
                               (SB.rep fsxp) (LOG.NoTxn ds') 
                               (MSLL a) sm' bm0 hm0
                             ✶ ⟦⟦ ds' = dsupd ds bn (DFOwner f, v, vsmerge vs)
                               ⟧⟧)
                            ✶ ⟦⟦ BFILE.block_belong_to_file ilist bn inum off
                              ⟧⟧) ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
                          ✶ ⟦⟦ MSCache a = MSCache mscs ⟧⟧)
                         ✶ ⟦⟦ MSAllocC a = MSAllocC mscs ⟧⟧)
                        ✶ ⟦⟦ MSIAllocC a = MSIAllocC mscs ⟧⟧)
                       ✶ 【 ds' !!
                         ‣‣ Fm
                            ✶ rep fsxp Ftop tree' ilist 
                                (frees_1, frees_2) a sm' 】)
                      ✶ ⟦⟦ tree' =
                           update_subtree pathname (TreeFile inum f') tree ⟧⟧)
                     ✶ 【 DFData f' ‣‣ Fd ✶ off |-> (DFOwner f, v, vsmerge vs) 】)
                    ✶ ⟦⟦ DFAttr f' = DFAttr f ⟧⟧)
                   ✶ ⟦⟦ DFOwner f' = DFOwner f ⟧⟧)
                  ✶ ⟦⟦ dirtree_safe ilist
                         (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                         tree ilist
                         (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                         tree' ⟧⟧)))%pred d0).
    left; repeat eexists; simpl in *; eauto.
    unfold permission_secure; intros.
    inv_exec_perm.
    cleanup; auto.
    unfold trace_secure; eauto.
    eassign (fun (_:block_mem) (_:hashmap) (_:rawdisk) => True).
    intros; simpl; auto.
    econstructor; eauto.
    econstructor.
    simpl in *.
    destruct r, p.
    intuition; cleanup.
    sigT_eq; eauto.
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    inversion H1.
  Qed.



Lemma file_set_attr_post:
    forall Fr Fm Ftop pathname f ds sm tree mscs fsxp ilist frees d bm hm pr inum tr d' bm' hm' tr' attr (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
  
  exec pr tr d bm hm (file_set_attr fsxp inum attr mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (([[ isError ok  ]] *
   sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ MSCache mscs' = MSCache mscs ]] *
   [[ MSDBlocks mscs' = MSDBlocks mscs ]] *
   [[ MSAllocC mscs' = MSAllocC mscs ]] *
   [[ MSIAllocC mscs' = MSIAllocC mscs ]]) \/
  ([[ ok = OK tt  ]] * [[ can_access pr (DFOwner f) ]] *
   exists d tree' f' ilist',
     sys_rep Fr Fm Ftop fsxp (pushd d ds) sm tree' ilist' frees mscs' bm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
     [[ f' = mk_dirfile (DFData f) attr (DFOwner f) ]] *
     [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                     ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
     [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]))%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@file_set_attr_ok fsxp inum attr mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel. 
  eauto.
  eauto.
  inv_exec_perm.
  destruct_lift H2.
  destruct_lift H1.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in let (a0, _) := ok' in
      (Fr * [[ MSAlloc a = MSAlloc mscs ]] 
        ✶ (⟦⟦ isError a0 ⟧⟧
           ✶ ((((((LOG.rep (FSXPLog fsxp) (SB.rep fsxp) 
                     (LOG.NoTxn ds) (MSLL a) sm bm0 hm0
                   ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
                  ✶ ⟦⟦ MSCache a = MSCache mscs ⟧⟧)
                 ✶ ⟦⟦ MSDBlocks a = MSDBlocks mscs ⟧⟧)
                ✶ ⟦⟦ MSAllocC a = MSAllocC mscs ⟧⟧)
               ✶ ⟦⟦ MSIAllocC a = MSIAllocC mscs ⟧⟧)
              ✶ 【 ds !!
                ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】)
           ⋁ (⟦⟦ a0 = OK tt ⟧⟧ ✶ ⟦⟦ can_access pr (DFOwner f) ⟧⟧)
             ✶ (exists
                  (d : diskstate) (tree' : dirtree) 
                (f' : dirfile) (ilist' : list INODE.inode),
                  ((((LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
                        (LOG.NoTxn (pushd d ds)) (MSLL a) sm bm0 hm0
                      ✶ 【 d
                        ‣‣ Fm
                           ✶ rep fsxp Ftop tree' ilist' (frees_1, frees_2) a sm
                        】)
                     ✶ ⟦⟦ tree' =
                          update_subtree pathname (TreeFile inum f') tree ⟧⟧)
                    ✶ ⟦⟦ f' =
                         {|
                         DFData := DFData f;
                         DFAttr := attr;
                         DFOwner := DFOwner f |} ⟧⟧)
                   ✶ ⟦⟦ dirtree_safe ilist
                          (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                          tree ilist'
                          (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                          tree' ⟧⟧)
                  ✶ ⟦⟦ BFILE.treeseq_ilist_safe inum ilist ilist' ⟧⟧)))%pred d0).
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    eauto.
    eauto.
    eauto.
    inversion H1.
Qed.



Lemma file_truncate_post:
    forall Fr Fm Ftop pathname f ds sm tree mscs fsxp ilist frees d bm hm pr inum tr d' bm' hm' tr' sz (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
  
  exec pr tr d bm hm (file_truncate fsxp inum sz mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (([[ isError ok ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
     sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm') \/
    ([[ ok = OK tt ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
     exists d tree' f' ilist' frees',
       sys_rep Fr Fm Ftop fsxp (pushd d ds) sm tree' ilist' frees' mscs' bm' hm' *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (setlen (DFData f) sz (DFOwner f, $ (0), [])) (DFAttr f) (DFOwner f)]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
        [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]]))%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@file_truncate_ok fsxp inum sz mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel. 
  eauto.
  inv_exec_perm.
  destruct_lift H2.
  destruct_lift H1.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in let (a0, _) := ok' in
      (Fr * [[ MSAlloc a = MSAlloc mscs ]]
        ✶ ((⟦⟦ isError a0 ⟧⟧
            ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
                (MSLL a) sm bm0 hm0)
           ✶ 【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】
           ⋁ ⟦⟦ a0 = OK tt ⟧⟧
             ✶ (exists
                  (d : diskstate) (tree' : dirtree) 
                (f' : dirfile) (ilist' : list INODE.inode) 
                (frees' : list addr * list addr),
                  ((((LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
                        (LOG.NoTxn (pushd d ds)) (MSLL a) sm bm0 hm0
                      ✶ 【 d ‣‣ Fm ✶ rep fsxp Ftop tree' ilist' frees' a sm 】)
                     ✶ ⟦⟦ tree' =
                          update_subtree pathname (TreeFile inum f') tree ⟧⟧)
                    ✶ ⟦⟦ f' =
                         {|
                         DFData := setlen (DFData f) sz (DFOwner f, $ (0), []);
                         DFAttr := DFAttr f;
                         DFOwner := DFOwner f |} ⟧⟧)
                   ✶ ⟦⟦ dirtree_safe ilist
                          (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                          tree ilist' (BFILE.pick_balloc frees' (MSAlloc a))
                          tree' ⟧⟧)
                  ✶ ⟦⟦ sz >= length (DFData f) ->
                       BFILE.treeseq_ilist_safe inum ilist ilist' ⟧⟧)))%pred d0).
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    eauto.
    eauto.
    eauto.
    inversion H1.
Qed.



Lemma file_sync_post:
    forall Fr Fm Ftop pathname f ds sm tree mscs fsxp ilist frees d bm hm pr inum tr d' bm' hm' tr' (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]])%pred d ->
  
  exec pr tr d bm hm (file_sync fsxp inum mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (([[ isError ok ]] * [[ ~can_access pr (DFOwner f) ]] *
    sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm') \/
   (exists sm' ds' tree' al,
      [[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]] *
      [[ MSAlloc mscs = MSAlloc mscs' ]] *
      [[ MSCache mscs = MSCache mscs' ]] *
      [[ MSAllocC mscs = MSAllocC mscs' ]] *
      [[ MSIAllocC mscs = MSIAllocC mscs' ]] *
      sys_rep Fr Fm Ftop fsxp ds' sm' tree' ilist frees mscs' bm' hm' *
      [[ ds' = dssync_vecs ds al]] *
      [[ length al = length (DFData f) /\
         forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]] *
      [[ tree' = update_subtree pathname (TreeFile inum  (synced_dirfile f)) tree ]] *
      [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                      ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]))%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@file_sync_ok fsxp inum mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel. 
  eauto.
  inv_exec_perm.
  destruct_lift H2.
  destruct_lift H1.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in let (a0, _) := ok' in
      (Fr
        ✶ ((⟦⟦ isError a0 ⟧⟧ ✶ ⟦⟦ can_access pr (DFOwner f) -> False ⟧⟧
           ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
           (MSLL a) sm bm0 hm0 *
           【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】)
           ⋁ (exists
                (sm' : Mem.mem) (ds' : diskset) (tree' : dirtree) 
              (al : list addr),
                ((((((((((⟦⟦ a0 = OK tt ⟧⟧ ✶ ⟦⟦ can_access pr (DFOwner f) ⟧⟧)
                         ✶ ⟦⟦ MSAlloc mscs = MSAlloc a ⟧⟧)
                        ✶ ⟦⟦ MSCache mscs = MSCache a ⟧⟧)
                       ✶ ⟦⟦ MSAllocC mscs = MSAllocC a ⟧⟧)
                      ✶ ⟦⟦ MSIAllocC mscs = MSIAllocC a ⟧⟧)
                     ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) 
                         (LOG.NoTxn ds') (MSLL a) sm' bm0 hm0)
                    ✶ ⟦⟦ ds' = dssync_vecs ds al ⟧⟧)
                   ✶ ⟦⟦ length al = length (DFData f) /\
                        (forall i : addr,
                         i < length al ->
                         BFILE.block_belong_to_file ilist (selN al i 0) inum i) ⟧⟧)
                  ✶ 【 ds' !!
                    ‣‣ Fm ✶ rep fsxp Ftop tree' ilist (frees_1, frees_2) a sm'
                    】)
                 ✶ ⟦⟦ tree' =
                      update_subtree pathname
                        (TreeFile inum (synced_dirfile f)) tree ⟧⟧)
                ✶ ⟦⟦ dirtree_safe ilist
                       (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a)) tree
                       ilist (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                       tree' ⟧⟧)))%pred d0).
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    destruct_lift H; eauto.
    eauto.
    eauto.
    eauto.
    inversion H1.
Qed.



Lemma tree_sync_post:
    forall Fr Fm Ftop ds sm tree mscs fsxp ilist frees d bm hm pr tr d' bm' hm' tr' (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm)%pred d ->
  
  exec pr tr d bm hm (tree_sync fsxp mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm bm' hm' *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *            
   [[ ok = OK tt ]] *             
   [[ MSAlloc mscs' = negb (MSAlloc mscs) ]] *
   [[ MSCache mscs' = MSCache mscs ]] *
   [[ MSICache mscs' = MSICache mscs ]] *
   [[ MSAllocC mscs' = MSAllocC mscs ]] *
   [[ MSIAllocC mscs' = MSIAllocC mscs ]])%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@tree_sync_ok fsxp mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel. 
  eauto.
  inv_exec_perm.
  destruct_lift H2.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in let (a0, _) := ok' in
      (Fr
        ✶ (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL a) sm bm0 hm0 *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs sm)]]] *            
      [[ a0 = OK tt ]] *             
      [[ MSAlloc a = negb (MSAlloc mscs) ]] *
      [[ MSCache a = MSCache mscs ]] *
      [[ MSICache a = MSICache mscs ]] *
      [[ MSAllocC a = MSAllocC mscs ]] *
      [[ MSIAllocC a = MSIAllocC mscs ]]))%pred d0).
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
    destruct rx, p.
    intuition; cleanup.
    sigT_eq; eauto.
    pred_apply; cancel.
    destruct_lift H; eauto.
    inversion H1.
Qed.

Lemma tree_sync_noop_post:
    forall Fr Fm Ftop ds sm tree mscs fsxp ilist frees d bm hm pr tr d' bm' hm' tr' (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm)%pred d ->
  
  exec pr tr d bm hm (tree_sync_noop fsxp mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *            
   [[ ok = OK tt ]] *             
   [[ MSAlloc mscs' = negb (MSAlloc mscs) ]])%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@tree_sync_noop_ok fsxp mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel. 
  eauto.
  inv_exec_perm.
  destruct_lift H2.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in let (a0, _) := ok' in
      (Fr
        ✶ (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL a) sm bm0 hm0 *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) mscs sm)]]] *            
      [[ a0 = OK tt ]] *             
      [[ MSAlloc a = negb (MSAlloc mscs) ]]))%pred d0).
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
    destruct rx, p.
    intuition; cleanup.
    sigT_eq; eauto.
    pred_apply; cancel.
    destruct_lift H; eauto.
    inversion H1.
Qed.


Lemma lookup_post:
    forall Fr Fm Ftop ds sm tree mscs fsxp ilist frees d bm hm pr tr d' bm' hm' tr' fnlist dnum (rx: (BFILE.memstate * (res (addr * bool) * unit))),
      
      (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
      [[ dirtree_inum tree = dnum]] *
      [[ dirtree_isdir tree = true ]])%pred d ->
  
  exec pr tr d bm hm (lookup fsxp dnum fnlist mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
           (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   (([[ isError ok ]] *
     [[ None = find_name fnlist tree ]]) \/
    (exists v, [[ ok = OK v ]] *
    [[ Some v = find_name fnlist tree]])))%pred d'.
Proof.
    unfold sys_rep, corr2; intros.
  pose proof (@lookup_ok fsxp dnum fnlist mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel. 
  inv_exec_perm.
  destruct_lift H2.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res (addr * bool) * unit))) =>
      let (a, ok') := r in
      let (a0, _) := ok' in
      (Fr
        ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
           (LOG.NoTxn ds) (MSLL a) sm bm0 hm0 *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist (frees_1, frees_2) a sm) ]]] *
   [[ MSAlloc a = MSAlloc mscs ]] *
   (([[ isError a0 ]] *
     [[ None = find_name fnlist tree ]]) \/
    (exists v, [[ a0 = OK v ]] *
    [[ Some v = find_name fnlist tree]])))%pred d0).
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    inversion H1.
Qed.


Lemma create_post:
    forall Fr Fm Ftop pathname ds sm tree mscs fsxp ilist frees d bm hm pr tr d' bm' hm' tr' name tag dnum tree_elem (rx: (BFILE.memstate * (res addr * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]])%pred d ->
  
  exec pr tr d bm hm (create fsxp dnum name tag mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (([[ isError ok ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
    sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm') \/
   (exists inum, [[ ok = OK inum ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
    exists d tree' ilist' frees',
      sys_rep Fr Fm Ftop fsxp (pushd d ds) sm tree' ilist' frees' mscs' bm' hm' *
      [[ tree' = tree_graft dnum tree_elem pathname name
                            (TreeFile inum {| DFData:= nil;
                                              DFAttr:= INODE.iattr0;
                                              DFOwner:= tag |}) tree ]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                      ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]]))%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@create_ok fsxp dnum name mscs pr tag) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel.
  eauto.
  inv_exec_perm.
  destruct_lift H2.
  destruct_lift H1.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res addr * unit))) =>
      let (a, ok') := r in
      let (a0, _) := ok' in
      (Fr
        ✶ (((⟦⟦ isError a0 ⟧⟧ ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
            ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
                (MSLL a) sm bm0 hm0)
           ✶ 【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】
           ⋁ (exists inum : addr,
                (⟦⟦ a0 = OK inum ⟧⟧ ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
                ✶ (exists
                     (d : diskstate) (tree' : dirtree) 
                   (ilist' : list INODE.inode) (frees' : list addr * list addr),
                     ((LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
                         (LOG.NoTxn (pushd d ds)) (MSLL a) sm bm0 hm0
                       ✶ ⟦⟦ tree' =
                            tree_graft dnum tree_elem pathname name
                              (TreeFile inum
                                 {|
                                 DFData := [];
                                 DFAttr := INODE.iattr0;
                                 DFOwner := tag |}) tree ⟧⟧)
                      ✶ 【 d ‣‣ Fm ✶ rep fsxp Ftop tree' ilist' frees' a sm 】)
                     ✶ ⟦⟦ dirtree_safe ilist
                            (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                            tree ilist' (BFILE.pick_balloc frees' (MSAlloc a))
                            tree' ⟧⟧))))%pred d0).
    left; repeat eexists; simpl in *; eauto.
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    rewrite pushd_latest; eauto.
    eauto.
    inversion H1.
Qed.


Lemma rename_post:
    forall Fr Fm Ftop ds sm tree mscs fsxp ilist frees d bm hm pr tr d' bm' hm' tr' dnum tree_elem dstname dstpath srcname srcpath cwd (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree cwd tree = Some (TreeDir dnum tree_elem) ]])%pred d ->
  
  exec pr tr d bm hm (rename fsxp dnum srcpath srcname dstpath dstname mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (([[ isError ok ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
       sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm') \/
   (Fr * [[ sync_invariant Fr ]] *
    [[ ok = OK tt ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
    rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname bm' hm'))%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@rename_ok fsxp dnum srcpath srcname dstpath dstname mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel.
  eauto.
  inv_exec_perm.
  destruct_lift H2.
  destruct_lift H1.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in
      let (a0, _) := ok' in
      (Fr
        ✶ (((⟦⟦ isError a0 ⟧⟧ ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
            ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
                (MSLL a) sm bm0 hm0)
           ✶ 【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】
           ⋁ (⟦⟦ a0 = OK tt ⟧⟧ ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
             ✶ rename_rep ds a sm Fm fsxp Ftop tree tree_elem ilist
                 (frees_1, frees_2) cwd dnum srcpath srcname dstpath dstname
                 bm0 hm0))%pred d0).
    left; repeat eexists; simpl in *; eauto.
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; cancel.
    destruct_lift H; eauto.
    inversion H1.
Qed.


Lemma delete_post:
    forall Fr Fm Ftop ds sm tree mscs fsxp ilist frees d bm hm pr tr d' bm' hm' tr' dnum tree_elem pathname name (rx: (BFILE.memstate * (res unit * unit))),
      
  (sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm *
   [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]])%pred d ->
  
  exec pr tr d bm hm (delete fsxp dnum name mscs)
       (Finished d' bm' hm' rx) tr' ->
  
  let mscs':= fst rx in
  let ok := fst (snd rx) in
  (([[ isError ok ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
      sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs' bm' hm') \/
      ([[ ok = OK tt ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
      exists d tree' ilist' frees',
      sys_rep Fr Fm Ftop fsxp (pushd d ds) sm tree' ilist' frees' mscs' bm' hm' *
      [[ tree' = update_subtree pathname
             (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                  ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ forall inum def', inum <> dnum -> In inum (tree_inodes tree) ->
           In inum (tree_inodes tree') ->
           selN ilist inum def' = selN ilist' inum def' ]]))%pred d'.
Proof.
  unfold sys_rep, corr2; intros.
  pose proof (@delete_ok fsxp dnum name mscs pr) as Hok.
  specialize (Hok _ (fun r => Ret r)).
  unfold corr2 in *.
  edestruct Hok with (d:= d).
  pred_apply; cancel.
  eauto.
  inv_exec_perm.
  destruct_lift H2.
  destruct_lift H1.
    eassign (fun d0 bm0 hm0 (r: (BFILE.memstate * (res unit * unit))) =>
      let (a, ok') := r in
      let (a0, _) := ok' in
      (Fr
        ✶ (((⟦⟦ isError a0 ⟧⟧ ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
            ✶ LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) 
                (MSLL a) sm bm0 hm0)
           ✶ 【 ds !! ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】
           ⋁ (⟦⟦ a0 = OK tt ⟧⟧ ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
             ✶ (exists
                  (d : diskstate) (tree' : dirtree) 
                (ilist' : list INODE.inode) (frees' : list addr * list addr),
                  (((LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
                       (LOG.NoTxn (pushd d ds)) (MSLL a) sm bm0 hm0
                     ✶ ⟦⟦ tree' =
                          update_subtree pathname
                            (TreeDir dnum (delete_from_list name tree_elem))
                            tree ⟧⟧)
                    ✶ 【 d ‣‣ Fm ✶ rep fsxp Ftop tree' ilist' frees' a sm 】)
                   ✶ ⟦⟦ dirtree_safe ilist
                          (BFILE.pick_balloc (frees_1, frees_2) (MSAlloc a))
                          tree ilist' (BFILE.pick_balloc frees' (MSAlloc a))
                          tree' ⟧⟧)
                  ✶ ⟦⟦ forall (inum : addr) (def' : INODE.inode),
                       (inum = dnum -> False) ->
                       In inum (tree_inodes tree) ->
                       In inum (tree_inodes tree') ->
                       selN ilist inum def' =
                       selN ilist' inum def' ⟧⟧)))%pred d0).
    left; repeat eexists; simpl in *; eauto.
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
    pred_apply; cancel.
    or_l; cancel.
    destruct_lift H; eauto.
    or_r; safecancel.
    destruct_lift H; eauto.
    rewrite pushd_latest; pred_apply; cancel.
    eauto.
    eauto.
    eapply H9; eauto.
    inversion H1.
Qed.


