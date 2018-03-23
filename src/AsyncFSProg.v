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


 Lemma read_post:
    forall Fr Fm Ftop pathname f Fd ds sm tree mscs fsxp ilist frees d bm hm pr off vs inum tr d' bm' hm' tr' (rx: (BFILE.memstate * (block * (res unit * unit)))),
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  exec pr tr d bm hm (read_fblock fsxp inum off mscs) (Finished d' bm' hm' rx) tr' ->
  let mscs':= fst rx in let r := fst (snd rx) in let ok := fst (snd (snd rx)) in
       (Fr * [[ sync_invariant Fr ]] *
       (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           (([[ isError ok ]] * [[ r = $0 ]] * [[ ~can_access pr (DFOwner f) ]]) \/
           ([[ ok = OK tt ]] * [[ r = snd (fst vs) ]] * [[ can_access pr (DFOwner f) ]]))))%pred d'.
  Proof.
    unfold corr2; intros.
    pose proof (@read_fblock_ok fsxp inum off mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eassign Fm; cancel.
    eauto.
    eauto.
    inv_exec_perm.
    simpl in *.
    destruct_lift H2.
    eassign (fun d0 bm0 hm0 (rx: (BFILE.memstate * (block * (res unit * unit)))) =>
     let a:= fst rx in let a0:= fst (snd rx) in let a1:= fst (snd (snd rx)) in
    (Fr ✶ (((LOG.rep (FSXPLog fsxp) (SB.rep fsxp) 
                   (LOG.NoTxn ds) (MSLL a) sm bm0 hm0
                 ✶ 【 ds !!
                   ‣‣ Fm ✶ rep fsxp Ftop tree ilist (frees_1, frees_2) a sm 】)
                ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
               ✶ (⟦⟦ isError a1 ⟧⟧ ✶ ⟦⟦ a0 = $ (0) ⟧⟧ * [[ ~can_access pr (DFOwner f) ]]
                  ⋁ ⟦⟦ a1 = OK tt ⟧⟧ ✶ ⟦⟦ a0 = snd (fst vs) ⟧⟧ * [[ can_access pr (DFOwner f) ]])))%pred d0).
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


  Lemma write_post:
    forall Fr Fm Ftop pathname f Fd ds sm tree mscs fsxp ilist frees d bm hm pr off vs v inum tr d' bm' hm' tr' (r: (BFILE.memstate * (res unit * unit))),
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
   [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
   [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
  exec pr tr d bm hm (update_fblock_d fsxp inum off v mscs) (Finished d' bm' hm' r) tr' ->
  let (mscs', ok') := r in let (ok, _) := ok' in
       (Fr * [[ sync_invariant Fr ]] *
       (([[ isError ok ]] * [[ ~can_access pr (DFOwner f) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]]) \/       
     ([[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]] *
       exists tree' f' ds' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm bm' hm' *
       [[ ds' = dsupd ds bn ((DFOwner f, v), vsmerge vs) ]] *
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       (* spec about files on the latest diskset *)
       [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees mscs' sm) ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (DFData f') ::: (Fd * off |-> ((DFOwner f, v), vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]] *
       [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                       ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]])))%pred d'.
  Proof.
    unfold corr2; intros.
    pose proof (@update_fblock_d_ok fsxp inum off v mscs pr) as Hok.
    specialize (Hok _ (fun r => Ret r)).
    unfold corr2 in *.
    edestruct Hok with (d:= d).
    pred_apply; cancel.
    eassign Fm; cancel.
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
                (bn : addr),
                  ((((((((((LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
                              (LOG.NoTxn ds') (MSLL a) sm bm0 hm0
                            ✶ ⟦⟦ ds' = dsupd ds bn (DFOwner f, v, vsmerge vs)
                              ⟧⟧)
                           ✶ ⟦⟦ BFILE.block_belong_to_file ilist bn inum off ⟧⟧)
                          ✶ ⟦⟦ MSAlloc a = MSAlloc mscs ⟧⟧)
                         ✶ ⟦⟦ MSCache a = MSCache mscs ⟧⟧)
                        ✶ ⟦⟦ MSAllocC a = MSAllocC mscs ⟧⟧)
                       ✶ ⟦⟦ MSIAllocC a = MSIAllocC mscs ⟧⟧)
                      ✶ 【 ds' !!
                        ‣‣ Fm
                           ✶ rep fsxp Ftop tree' ilist (frees_1, frees_2) a sm
                        】)
                     ✶ ⟦⟦ tree' =
                          update_subtree pathname (TreeFile inum f') tree ⟧⟧)
                    ✶ 【 DFData f' ‣‣ Fd ✶ off |-> (DFOwner f, v, vsmerge vs) 】)
                   ✶ ⟦⟦ DFAttr f' = DFAttr f ⟧⟧)
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



(** Safety **)

Axiom one_tag_per_user:
  forall pr t t',
    t <> Public ->
    t' <> Public ->
    t <> t' ->
    can_access pr t ->
    ~can_access pr t'.

Inductive fprog_basic : Type -> Type :=
| FRead : fs_xparams ->
          INODE.IRec.Cache.key ->
          addr ->
          fprog_basic (block * res unit)

| FWrite : fs_xparams ->
           INODE.IRec.Cache.key ->
           addr ->
           block ->
           fprog_basic (res unit).

Inductive fprog : Type -> Type :=
| FBasic : forall T, fprog_basic T -> fprog T
| FBind: forall T T', fprog T  -> (T -> fprog_basic T') -> fprog T'.

Inductive fexec_basic:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> hashmap -> BFILE.memstate ->
       fprog_basic T ->  result -> BFILE.memstate -> trace -> Prop :=
| FExecRead    :
    forall pr d bm hm tr tr' fsxp inum off (ams ams': BFILE.memstate)
      (b: block) (ok: res unit) d' bm' hm',
      exec pr tr d bm hm (read_fblock fsxp inum off ams)
           (Finished d' bm' hm' ^(ams', b, ok)) tr' ->
      fexec_basic pr tr d bm hm ams (FRead fsxp inum off)
            (Finished d' bm' hm' (b, ok)) ams' tr'
                   
| FExecWrite   :
    forall pr d bm hm tr d' bm' hm' tr' fsxp
      inum off v (ams ams': BFILE.memstate) (ok: res unit),
      exec pr tr d bm hm (update_fblock_d fsxp inum off v ams)
           (Finished d' bm' hm' ^(ams', ok)) tr' ->
      fexec_basic pr tr d bm hm ams (FWrite fsxp inum off v)
            (Finished d' bm' hm' ok) ams' tr'.


Inductive fexec:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> hashmap -> BFILE.memstate ->
       fprog T ->  result -> BFILE.memstate -> trace -> Prop :=
| FExecBasic    :
    forall T (p :fprog_basic T) pr d bm hm tr tr' (ams ams': BFILE.memstate)
     out,
      fexec_basic pr tr d bm hm ams p out ams' tr' ->
      fexec pr tr d bm hm ams (FBasic p) out ams' tr'
                   
| FExecBind :
    forall T T' pr (p1 : fprog T) (p2: T -> fprog_basic T') d bm hm d'
      bm' hm' v r tr tr' tr'' ams ams' ams'',
               fexec pr tr d bm hm ams p1 (Finished d' bm' hm' v) ams' tr' ->
               fexec_basic pr tr' d' bm' hm' ams' (p2 v) r ams'' tr'' ->
               fexec pr tr d bm hm ams (FBind p1 p2) r ams'' tr''

| FCrashBind : forall T T' pr (p1 : fprog T) (p2: T -> fprog_basic T') d d' bm bm' hm hm' tr tr' r ams ams',
                fexec pr tr d bm hm ams p1 r ams' tr' ->
                r = (Crashed d' bm' hm') ->
                fexec pr tr d bm hm ams (FBind p1 p2) r ams' tr'.

Fixpoint filter tag tree:=
  match tree with
  | TreeFile inum f =>
    if tag_dec Public (DFOwner f) then
      TreeFile inum f
    else
      if tag_dec tag (DFOwner f) then
        TreeFile inum f
      else
        TreeFile inum (mk_dirfile nil INODE.iattr0 (DFOwner f))
  | TreeDir inum ents =>
    TreeDir inum (map (fun st => (fst st, filter tag (snd st))) ents)
  end.

Definition equivalent_for tag tree1 tree2:=
  filter tag tree1 = filter tag tree2.

Definition same_except tag tree1 tree2:=
  forall tag', tag' <> tag -> equivalent_for tag' tree1 tree2.


Definition permission_secure_f {T} d bm hm mscs pr (p: fprog T) :=
  forall tr tr' r mscs' ,
    fexec pr tr d bm hm mscs p r mscs' (tr'++tr) ->
    trace_secure pr tr'.

(*
Theorem permission_secure_f_same_except:
  forall T (p: fprog T) tag Fr Fm Ftop ds sm tree1 tree2 mscs fsxp ilist frees pr d1 bm hm d2,
    (Fr *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree1 ilist frees mscs sm)]]])%pred d1 ->
    (Fr *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]])%pred d2 ->
    permission_secure_f d1 bm hm mscs pr p ->
    can_access pr tag ->
    tag <> Public ->
    equivalent_for tag tree1 tree2 ->
    permission_secure_f d2 bm hm mscs pr p.
Proof.
  induction p; simpl; intros.
  admit.
  unfold permission_secure_f; 
  inversion H6; subst; sigT_eq.
*)






Lemma map_app_exists:
  forall A B (l l0 l1: list A) (f: A -> B),
    map f (l0++l1) = map f l ->
    exists l0' l1',
      l = l0'++l1' /\
      length l0' = length l0 /\
      length l1' = length l1. 
Proof.
  induction l; simpl ; intros.
  rewrite map_app in H.
  apply app_eq_nil in H.
  cleanup.
  apply map_eq_nil in H; apply map_eq_nil in H0.
  exists l0, l1.
  cleanup; eauto.
  destruct l0; simpl in *.
  destruct l1;  simpl in *; try congruence.
  inversion H.
  assert (map f ([]++l1) = map f l). simpl; auto.
  specialize IHl with (1:=H0).
  cleanup.
  apply length_zero_iff_nil in H4; cleanup.
  exists nil, (a::x0).
  simpl; eauto.
  
  inversion H.
  specialize IHl with (1:=H2).
  cleanup.
  exists (a::x), (x0).
  simpl; eauto.
Qed.

Lemma app_inv_length:
  forall A (l1 l2 l3 l4: list A),
    length l1 = length l2 ->
    l1 ++ l3 = l2 ++ l4 ->
    l1 = l2 /\ l3 = l4.
Proof.
  induction l1; intros;
  destruct l2; simpl in *; try congruence.
  eauto.
  inversion H; inversion H0; subst.
  apply IHl1 in H4; destruct H4; subst; eauto.
Qed.

Lemma equivalent_for_find_subtree:
  forall pathname tree1 tree2 t inum f,
    equivalent_for t tree1 tree2 ->
    find_subtree pathname tree1 = Some (TreeFile inum f) ->
    DFOwner f = t ->
    tree_names_distinct tree1 ->
    tree_names_distinct tree2 ->
    find_subtree pathname tree2 = Some (TreeFile inum f).
Proof.
  induction pathname; intros.
  {
    simpl in *.
    unfold equivalent_for, filter in *.
    destruct f; simpl in *.
    cleanup; simpl in *.
    destruct t; subst.
    {
      destruct tree2; simpl in *; intuition.
      destruct d; simpl in *.
      destruct (DFOwner).
      cleanup; auto.
      inversion H; subst; intuition.
      inversion H.
    }

    {
      destruct (tag_dec (Private o) (Private o)); try congruence.
      destruct tree2; simpl in *; intuition.
      destruct d; simpl in *.
      destruct (DFOwner).
      cleanup; auto.
      destruct (Nat.eq_dec o o0); subst; simpl in *.
      inversion H; subst; intuition.
      inversion H; subst; intuition.
      inversion H.
    }
  }
  {
    destruct tree1; try solve [ simpl in *; congruence].
    destruct tree2; try solve [ simpl in *; congruence].
    {
      simpl in *.
      unfold equivalent_for, filter in H.
      destruct (tag_dec Public (DFOwner d)); try congruence.
      destruct (tag_dec t (DFOwner d)); try congruence.
    }
    {
      unfold equivalent_for in *.
      eapply lookup_firstelem_path in H0.
      cleanup.
      simpl in H0.
      apply find_subtree_helper_in in H0 as Hx; cleanup.
      specialize IHpathname with (2:=H4).
      inversion H; subst; clear H.
      eapply map_app_exists in H6 as Hx; cleanup.
      destruct x3.
      simpl in H5.
      inversion H5.
      destruct p.
      repeat rewrite map_app in H6.
      apply app_inv_length in H6; [|repeat rewrite map_length; auto]; cleanup.
      simpl in H6.
      inversion H6; subst.
      eapply IHpathname in H9; eauto.
      replace (s::pathname) with ([s]++pathname) by (simpl; auto).
      erewrite <- find_subtree_extend; eauto.
      apply find_subtree_leaf_in.
      intuition.
      eapply tree_names_distinct_nodup; eauto.
      inversion H2.
      rewrite map_app in H11.
      eapply forall_app_l in H11.
      simpl in H11; inversion H11; auto.
      inversion H3.
      rewrite map_app in H11.
      eapply forall_app_l in H11.
      simpl in H11; inversion H11; auto.
    }
  }
Qed.




(*
Definition corr2' (T: Type) pr pre post crash (p: prog T):=
  forall d bm hm tr tr' out,
    pre bm hm d
  -> exec pr tr d bm hm p out tr'
  -> ((exists d' bm' hm' (v: T), out = Finished d' bm' hm' v /\
                  post bm' hm' v d') \/
      (exists d' bm' hm', out = Crashed d' bm' hm' /\ crash bm' hm' d')).

Lemma corr2_transform':
  forall T (p: prog T) pr pre post crash,
   corr2 pr pre p ->
   corr2' pr (pre post crash) (fun bm hm r d => post d bm hm r) crash p.
Proof.
  unfold corr2, corr2'; intros.
  edestruct H with (d:= d).
  eauto.
  eauto.
  eauto.
Qed.

Lemma exec_out_destruct:
  forall T (p:prog T) pr tr d bm hm tr' out,
    exec pr tr d bm hm p out tr' ->
    (exists d' bm' hm' (r:T), out = Finished d' bm' hm' r) \/
    (exists d' bm' hm',  out = Crashed d' bm' hm').
Proof.
  induction 1; intros.
  all: eauto; try solve [(left; repeat eexists; eauto)];
  try solve [(right; repeat eexists; eauto)].
Qed.

Lemma corr2'_ret_noop:
  forall T (p: prog T) pre post crash pr,
    corr2' pr pre post crash (x <- p;; Ret x) ->
    corr2' pr pre post crash p.
Proof.
  unfold corr2'; intros.
  eapply exec_out_destruct in H0 as Hx.
  intuition; cleanup.
  eapply H; eauto.
  repeat econstructor; eauto.
  eapply H; eauto.
  eapply CrashBind; eauto.
Qed.

Lemma desugar_write:
  forall T (p: prog T) pre post crash pr,
    {< (ds : diskset) (sm : @Mem.mem addr addr_eq_dec bool)
       (Fm : @pred addr addr_eq_dec valuset)
       (Ftop : @pred addr Nat.eq_dec BFILE.bfile) 
       (tree : dirtree) (pathname : list String.string) 
       (f : dirfile) (Fd : @pred addr Nat.eq_dec datatype) 
       (vs : datatype) (frees : list addr * list addr)
       (ilist : list INODE.inode),
   PERM: pr
   PRE: bm, hm, pre
   POST: bm', hm', post                       
   CRASH: bm', hm', crash
   >} p ->
  corr2' pr (fun _ _ => pre) (fun _ _ r => post emp r) (fun _ _ => crash) p.
Proof.
  intros.
  eapply corr2_transform' with
      (post:= fun d (_:block_mem) (_:hashmap) r => post emp r d)
      (crash:= fun _ _ d => crash d) in H.
  apply corr2'_ret_noop in H.
  unfold corr2' in *; intros.
  eapply H; eauto.
  pred_apply; cancel.
  unfold corr2; intros.
  inv_exec_perm.
  destruct_lift H2.
  split; eauto.
  left; repeat eexists; eauto.
  unfold permission_secure; intros.
  inv_exec_perm.
  cleanup; auto.
  unfold trace_secure; eauto.
  cancel.
  Unshelve.
  all: eauto.
  all: try exact nil.
  all: try repeat constructor.
  exact emp.
  exact $0.
Qed.

Lemma exis_merge:
  forall A B AT AEQ V (P: @pred AT AEQ V),
    A ->
    B ->
    exis (fun a:A => exis (fun b:B => P)) =p=> exis (fun (ab: A*B) => P).
Proof.
  intros.
  cancel.
  Unshelve.
  all: eauto.
Qed.

Lemma extract_post_condition_finished:
  forall T (p: prog T) (pre: block_mem -> hashmap -> pred) post crash tr d bm hm pr d' bm' hm' r tr',
    exec pr tr d bm hm p (Finished d' bm' hm' r) tr' ->
    corr2' pr pre post crash p ->
    pre bm hm d ->
    post bm' hm' r d'.
  Proof.
    unfold corr2'; intros.
    edestruct H0 with (d:= d); eauto.
    cleanup.
    sigT_eq; eauto.
    cleanup.
    inversion H2.
  Qed.
 *)

Lemma read_equivalent_exec:
  forall Fr Fm Ftop pathname f Fd ds sm tree1 tree2 mscs mscs1 mscs2 fsxp ilist frees pr off vs inum tr d1 bm hm d1' bm1 hm1 d2 d2' bm2 hm2 tr1 (r1 r2: block * res unit) tr2,
  fexec_basic pr tr d1 bm hm mscs (FRead fsxp inum off) (Finished d1' bm1 hm1 r1) mscs1 tr1 ->
  fexec_basic pr tr d2 bm hm mscs (FRead fsxp inum off) (Finished d2' bm2 hm2 r2) mscs2 tr2 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree1 ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d1 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]])%pred d2 ->
  equivalent_for (DFOwner f) tree1 tree2 ->
  r1 = r2.
Proof.  
  intros.
  assert (A: (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree2 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d2).
  destruct_lift H1; pred_apply; cancel.
  apply rep_tree_names_distinct in H4.
  apply rep_tree_names_distinct in H5.
  eapply equivalent_for_find_subtree; eauto.
  inversion H; subst; sigT_eq; clear H.
  inversion H0; subst; sigT_eq; clear H0.
  pose proof (read_post _ H1 H19) as Hspec1.
  pose proof (read_post _ A H18) as Hspec2.
  destruct_lift Hspec1.
  repeat rewrite sep_star_or_distr in Hspec1.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition.
  destruct_lift H; intuition.
  repeat rewrite sep_star_or_distr in Hspec2.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H0; intuition.
  admit. (* isError hides the error so can't show equality *) 
  destruct_lift H0; intuition.
  
  destruct_lift H; intuition.
  repeat rewrite sep_star_or_distr in Hspec2.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H0; intuition.
  destruct_lift H0; intuition.
Admitted.



  
Lemma write_equivalent_exec:
  forall Fr Fm Ftop pathname f Fd ds sm tree1 tree2 mscs mscs1 mscs2 fsxp ilist frees pr off vs v inum tr d1 bm hm d1' bm1 hm1 d2 d2' bm2 hm2 tr1 (r1 r2: res unit) tr2,
  fexec_basic pr tr d1 bm hm mscs (FWrite fsxp inum off v) (Finished d1' bm1 hm1 r1) mscs1 tr1 ->
  fexec_basic pr tr d2 bm hm mscs (FWrite fsxp inum off v) (Finished d2' bm2 hm2 r2) mscs2 tr2 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree1 ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d1 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]])%pred d2 ->
  equivalent_for (DFOwner f) tree1 tree2 ->
  r1 = r2.
Proof.  
  intros.
  assert (A: (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree2 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d2).
  destruct_lift H1; pred_apply; cancel.
  apply rep_tree_names_distinct in H4.
  apply rep_tree_names_distinct in H5.
  eapply equivalent_for_find_subtree; eauto.
  inversion H; subst; sigT_eq; clear H.
  inversion H0; subst; sigT_eq; clear H0.
  pose proof (write_post _ H1 H20) as Hspec1.
  pose proof (write_post _ A H19) as Hspec2.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition.
  destruct_lift H; intuition.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H4; intuition.
  admit. (* isError hides the error so can't show equality *) 
  destruct_lift H4; intuition.
  
  destruct_lift H; intuition.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H0; intuition.
  destruct_lift H0; intuition.
Admitted.

