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
Require Import AsyncFS AsyncFSPost.

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


(** Safety **)

(** 
(** this axioms may simplify tree equivalence after execution proofs *)
Axiom one_tag_per_user:
  forall pr t t',
    t <> Public ->
    t' <> Public ->
    can_access pr t ->
    can_access pr t' ->
    t = t'.

Axiom one_user_per_tag:
  forall pr pr' t,
    t <> Public ->
    can_access pr t ->
    can_access pr' t ->
    pr = pr'.
 *)

Inductive fbasic : Type -> Type :=
| file_get_attr_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    fbasic (Rec.data (Rec.field_type
           (Rec.FE [("owner", Rec.WordF 8);
                    ("unused", Rec.WordF 16)]
                     "attr" INODE.attrtype)) *
            res unit)
                           
| file_set_attr_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    INODE.iattrin ->
    fbasic (res unit)

| file_get_sz_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    fbasic (word 64 * res unit)

| file_set_sz_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    word 64 ->
    fbasic (res unit)
                         
| read_fblock_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    addr ->
    fbasic (block * res unit)

| update_fblock_d_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    addr ->
    block ->
    fbasic (res unit)
(*
| update_fblock_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    addr ->
    block ->
    fbasic (bool * res unit)
*)
| file_truncate_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    addr ->
    fbasic (res unit)

| file_sync_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    fbasic (res unit)

| readdir_f :
    fs_xparams ->
    INODE.IRec.Cache.key ->
    fbasic (list (String.string * (addr * bool)))
(*
| mkdir_f :
    fs_xparams ->
    BFcache.key ->
    Dcache.key ->
    fbasic (res addr)

| mksock_f :
    fs_xparams ->
    BFcache.key ->
    Dcache.key ->
    tag ->
    fbasic (res INODE.IRec.Cache.key)
*)
| create_f :
    fs_xparams ->
    BFcache.key ->
    Dcache.key ->
    tag ->
    fbasic (res addr)
           
| delete_f :
    fs_xparams ->
    BFcache.key ->
    Dcache.key ->
    fbasic (res unit)

| lookup_f :
    fs_xparams ->
    addr ->
    list String.string ->
    fbasic (res (BFcache.key * bool))
           
| rename_f :
    fs_xparams ->
    addr ->
    list String.string ->
    Dcache.key ->
    list String.string ->
    Dcache.key ->
    fbasic (res unit)

| tree_sync_f :
    fs_xparams ->
    fbasic (res unit)

| tree_sync_noop_f :
    fs_xparams ->
    fbasic (res unit).

Inductive fprog : Type -> Type :=
| FBasic : forall T, fbasic T -> fprog T
| FBind: forall T T', fbasic T  -> (T -> fprog T') -> fprog T'.

Inductive exec_fbasic:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> hashmap -> BFILE.memstate ->
       fbasic T ->  result -> BFILE.memstate -> trace -> Prop :=
| FExecRead    :
    forall pr d bm hm tr tr' fsxp inum off (ams ams': BFILE.memstate)
      (r: block * res unit) d' bm' hm',
      exec pr tr d bm hm (read_fblock fsxp inum off ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (read_fblock_f fsxp inum off)
                  (Finished d' bm' hm' r) ams' tr'
                  
| FExecSetAttr    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      attr (r: res unit) d' bm' hm',
      exec pr tr d bm hm (file_set_attr fsxp inum attr ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (file_set_attr_f fsxp inum attr)
                  (Finished d' bm' hm' r) ams' tr'

| FExecGetAttr    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      (r: INODE.iattr * res unit) d' bm' hm',
      exec pr tr d bm hm (file_get_attr fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (file_get_attr_f fsxp inum)
                  (Finished d' bm' hm' r) ams' tr'

| FExecSetSz    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      sz (r: res unit) d' bm' hm',
      exec pr tr d bm hm (file_set_sz fsxp inum sz ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (file_set_sz_f fsxp inum sz)
                  (Finished d' bm' hm' r) ams' tr'

| FExecGetSz    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      (r: word 64 * res unit) d' bm' hm',
      exec pr tr d bm hm (file_get_sz fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (file_get_sz_f fsxp inum)
            (Finished d' bm' hm' r) ams' tr'
                   
| FExecWrite   :
    forall pr d bm hm tr d' bm' hm' tr' fsxp
      inum off v (ams ams': BFILE.memstate) (ok: res unit),
      exec pr tr d bm hm (update_fblock_d fsxp inum off v ams)
           (Finished d' bm' hm' ^(ams', ok)) tr' ->
      exec_fbasic pr tr d bm hm ams (update_fblock_d_f fsxp inum off v)
                  (Finished d' bm' hm' ok) ams' tr'

| FExecTruncate    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      sz (r: res unit) d' bm' hm',
      exec pr tr d bm hm (file_truncate fsxp inum sz ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (file_truncate_f fsxp inum sz)
                  (Finished d' bm' hm' r) ams' tr'

| FExecFileSync    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      (r: res unit) d' bm' hm',
      exec pr tr d bm hm (file_sync fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (file_sync_f fsxp inum)
                  (Finished d' bm' hm' r) ams' tr'

| FExecReaddir    :
    forall pr d bm hm tr tr' fsxp inum (ams ams': BFILE.memstate)
      (r: list (String.string * (addr * bool))) d' bm' hm',
      exec pr tr d bm hm (readdir fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (readdir_f fsxp inum)
                  (Finished d' bm' hm' r) ams' tr'

| FExecCreate    :
    forall pr d bm hm tr tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res addr) name tag d' bm' hm',
      exec pr tr d bm hm (create fsxp dnum name tag ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (create_f fsxp dnum name tag)
                  (Finished d' bm' hm' r) ams' tr'

| FExecDelete    :
    forall pr d bm hm tr tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res addr) name d' bm' hm',
      exec pr tr d bm hm (delete fsxp dnum name ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (delete_f fsxp dnum name)
                  (Finished d' bm' hm' r) ams' tr'

| FExecLookup    :
    forall pr d bm hm tr tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res (BFcache.key * bool)) fnlist d' bm' hm',
      exec pr tr d bm hm (lookup fsxp dnum fnlist ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (lookup_f fsxp dnum fnlist)
                  (Finished d' bm' hm' r) ams' tr'

| FExecRename    :
    forall pr d bm hm tr tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res unit) srcpath srcname dstpath dstname d' bm' hm',
      exec pr tr d bm hm (rename fsxp dnum srcpath srcname dstpath dstname ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (rename_f fsxp dnum srcpath srcname dstpath dstname)
                  (Finished d' bm' hm' r) ams' tr'

| FExecTreeSync    :
    forall pr d bm hm tr tr' fsxp (ams ams': BFILE.memstate)
      (r: res unit) d' bm' hm',
      exec pr tr d bm hm (tree_sync fsxp ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (tree_sync_f fsxp)
                  (Finished d' bm' hm' r) ams' tr'

| FExecTreeSyncNoop    :
    forall pr d bm hm tr tr' fsxp (ams ams': BFILE.memstate)
      (r: res unit) d' bm' hm',
      exec pr tr d bm hm (tree_sync_noop fsxp ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr tr d bm hm ams (tree_sync_noop_f fsxp)
                  (Finished d' bm' hm' r) ams' tr'.


Inductive fexec:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> hashmap -> BFILE.memstate ->
       fprog T ->  result -> BFILE.memstate -> trace -> Prop :=
| FExecBasic    :
    forall T (p :fbasic T) pr d bm hm tr tr' (ams ams': BFILE.memstate)
     out,
      exec_fbasic pr tr d bm hm ams p out ams' tr' ->
      fexec pr tr d bm hm ams (FBasic p) out ams' tr'
                   
| FExecBind :
    forall T T' pr (p1 : fbasic T) (p2: T -> fprog T') d bm hm d'
      bm' hm' v r tr tr' tr'' ams ams' ams'',
               exec_fbasic pr tr d bm hm ams p1 (Finished d' bm' hm' v) ams' tr' ->
               fexec pr tr' d' bm' hm' ams' (p2 v) r ams'' tr'' ->
               fexec pr tr d bm hm ams (FBind p1 p2) r ams'' tr''

| FCrashBind : forall T T' pr (p1 : fbasic T) (p2: T -> fprog T') d d' bm bm' hm hm' tr tr' r ams ams',
                exec_fbasic pr tr d bm hm ams p1 r ams' tr' ->
                r = (Crashed d' bm' hm') ->
                fexec pr tr d bm hm ams (FBind p1 p2) r ams' tr'.

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

Definition equivalent_for tag tree1 tree2:=
  filter tag tree1 = filter tag tree2.

Definition public_equivalent tree1 tree2:=
  equivalent_for Public tree1 tree2.

Definition same_except tag tree1 tree2:=
  forall tag', tag' <> tag -> equivalent_for tag' tree1 tree2.

Definition same_except_nonpublic tag tree1 tree2:=
  forall tag', tag'<> Public -> tag' <> tag -> equivalent_for tag' tree1 tree2.

Definition fbasic_to_prog {T} mscs (fp: fbasic T): prog (BFILE.memstate * (T * unit)) :=
  match fp with
  | FRead fsxp inum off => read_fblock fsxp inum off mscs
  | FWrite fsxp inum off v => update_fblock_d fsxp inum off v mscs
  end.

Fixpoint fprog_to_prog {T} mscs (fp: fprog T): prog (BFILE.memstate * (T * unit)) :=
  match fp with
  | FBasic p => fbasic_to_prog mscs p
  | FBind p bp => x <- (fprog_to_prog mscs p);; (fbasic_to_prog (fst x) (bp (fst (snd x))))
  end.

Definition permission_secure_fbasic {T} d bm hm mscs pr (p: fbasic T) :=
  forall tr tr' r mscs' ,
    exec_fbasic pr tr d bm hm mscs p r mscs' (tr'++tr) ->
    trace_secure pr tr'.

Definition permission_secure_fprog {T} d bm hm mscs pr (p: fprog T) :=
  forall tr tr' r mscs' ,
    fexec pr tr d bm hm mscs p r mscs' (tr'++tr) ->
    trace_secure pr tr'.

Theorem ps_fbasic2prog:
  forall T (fp: fbasic T) d bm hm mscs pr,
    permission_secure d bm hm pr (fbasic_to_prog mscs fp) ->
    permission_secure_fbasic d bm hm mscs pr fp.
Proof.
  unfold permission_secure_fbasic, permission_secure; intros.
  inversion H0; subst; sigT_eq; clear H0; eauto.
Qed.

Theorem ps_fbasic2fprog:
  forall T (fp: fbasic T) d bm hm mscs pr,
    permission_secure_fbasic d bm hm mscs pr fp ->
    permission_secure_fprog d bm hm mscs pr (FBasic fp).
Proof.
  unfold permission_secure_fbasic, permission_secure_fprog; intros.
  inversion H0; subst; sigT_eq; clear H0; eauto.
Qed.

Lemma trace_app_fbasic:
  forall T (fp: fbasic T) tr d bm hm mscs pr out mscs' tr',
    exec_fbasic pr tr d bm hm mscs fp out mscs' tr' ->
    exists tr'', tr' = tr''++tr.
Proof.
  intros;
  inversion H; subst; sigT_eq;
  denote exec as Hx; apply trace_app in Hx; auto.
Qed.

Lemma trace_app_fprog:
  forall T (fp: fprog T) tr d bm hm mscs pr out mscs' tr',
    fexec pr tr d bm hm mscs fp out mscs' tr' ->
    exists tr'', tr' = tr''++tr.
Proof.
  induction fp; intros.
  inversion H; subst; repeat sigT_eq;
  denote exec_fbasic as Hx; apply trace_app_fbasic in Hx; auto.
  inversion H; subst; repeat sigT_eq.
  specialize IHfp with (1:= H13).
  denote exec_fbasic as Hx; apply trace_app_fbasic in Hx; auto.
  cleanup; eexists; rewrite app_assoc; eauto.
  specialize IHfp with (1:= H13); auto.
Qed.
  
Theorem ps_fprog_bind:
  forall T T' (p: fprog T) (fp: T -> fbasic T') d bm hm mscs pr,
    permission_secure_fprog d bm hm mscs pr p ->
    (forall tr d' bm' hm' r mscs' tr',
       fexec pr tr d bm hm mscs p (Finished d' bm' hm' r) mscs' tr' ->
       permission_secure_fbasic d' bm' hm' mscs' pr (fp r)) ->
    permission_secure_fprog d bm hm mscs pr (FBind p fp).
Proof.
  unfold permission_secure_fbasic, permission_secure_fprog; intros.
  inversion H1; subst; repeat sigT_eq; clear H1; eauto.
  specialize H0 with (1:= H15).
  apply trace_app_fprog in H15 as Hx; cleanup.
  apply trace_app_fbasic in H16 as Hx; cleanup.
  specialize H with (1:=H15).
  rewrite <- app_assoc in H16; specialize H0 with (1:=H16).
  apply trace_secure_app; eauto.  
Qed.


(**
Theorem ps_fprog2prog:
  forall T (fp: fprog T) d bm hm mscs pr,
    permission_secure d bm hm pr (fprog_to_prog mscs fp) ->
    permission_secure_fprog d bm hm mscs pr fp.
Proof.
  induction fp; intros.
  apply ps_fbasic2fprog.
  simpl in H.
  apply ps_fbasic2prog; auto.
  simpl in H.
  unfold permission_secure_fprog, permission_secure in *; intros.

  inversion H0; subst; repeat sigT_eq; clear H0; eauto.
Abort.

(* this direction requires crashes *)
Theorem ps_prog2fb:
  forall T (fp: fbasic T) d bm hm mscs pr,
    permission_secure_fbasic d bm hm mscs pr fp ->
    permission_secure d bm hm pr (fbasic_to_prog mscs fp).
    
Proof.
  unfold permission_secure_fbasic, permission_secure; intros.
  destruct fp; simpl in *; eapply H; econstructor; eauto.
Qed.
*)


Theorem permission_secure_fbasic_equivalent:
  forall T (p: fbasic T) tag Fr Fm Ftop ds sm tree1 tree2 mscs fsxp ilist frees pr d1 bm hm d2,
    (Fr *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree1 ilist frees mscs sm)]]])%pred d1 ->
    (Fr *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]])%pred d2 ->
    permission_secure_fbasic d1 bm hm mscs pr p ->
    can_access pr tag ->
    tag <> Public ->
    equivalent_for tag tree1 tree2 ->
    permission_secure_fbasic d2 bm hm mscs pr p.
Proof.
  intros.
  apply ps_fbasic2prog.
Abort.


Lemma equivalent_update_nt:
  forall pathname tree tag f1 f2 inum,
    tag <> (DFOwner f1) ->
    (DFOwner f1) = (DFOwner f2) ->
    tree_names_distinct tree ->
    equivalent_for tag (update_subtree pathname (TreeFile inum f1) tree)
                   (update_subtree pathname (TreeFile inum f2) tree).
Proof.
  induction pathname; intros.
  unfold equivalent_for; simpl; intros.
  destruct (tag_dec tag (DFOwner f1)); try congruence.
  destruct (tag_dec tag (DFOwner f2)); try congruence.
  destruct tree.
  unfold equivalent_for in *; simpl; auto.
  
  replace (a::pathname) with ([a]++pathname) by (simpl; auto).
  destruct (find_subtree [a] (TreeDir n l)) eqn:D.
  repeat erewrite update_subtree_app; eauto.
  simpl in D; apply find_subtree_helper_in in D as Hx; cleanup.
  simpl.
  repeat rewrite map_app; simpl.
  destruct (String.string_dec a a); try congruence.
  inversion H1; subst.
  rewrite map_app in H5; simpl in H5;
  apply NoDup_remove_2 in H5; intuition.
  repeat rewrite update_subtree_notfound; intuition.
  unfold equivalent_for in *; simpl; auto.
  repeat rewrite map_app; simpl.
  erewrite IHpathname; eauto.
  rewrite map_app in H4; apply forall_app_l in H4; inversion H4; auto.

  eapply find_subtree_app_none in D.
  repeat erewrite update_subtree_path_notfound; eauto.
  unfold equivalent_for in *; simpl; auto.
Qed.




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
    destruct (tag_dec t t); try congruence.
    
    destruct tree2; simpl in *; intuition.
    destruct d; simpl in *.
    destruct (tag_dec t DFOwner).
    cleanup; auto.
    inversion H; subst; intuition.
    inversion H.
  }
  {
    destruct tree1; try solve [ simpl in *; congruence].
    destruct tree2; try solve [ simpl in *; congruence].
    {
      simpl in *.
      unfold equivalent_for, filter in H.
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

(** Security Examples **)

Theorem write_same_except_after:
  forall Fr Fm Fd Ftop ds sm pathname f tree vs mscs mscs1 fsxp ilist frees pr off v1 inum tr d bm hm d1 bm1 hm1 tr1 (r1: res unit),
  exec_fbasic pr tr d bm hm mscs (FWrite fsxp inum off v1) (Finished d1 bm1 hm1 r1) mscs1 tr1 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
   exists tree1 fsxp1 ds1 sm1 ilist1 frees1,
    (Fr *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm * rep fsxp1 Ftop tree1 ilist1 frees1 mscs1 sm1)]]])%pred d1 /\
    same_except (DFOwner f) tree tree1.
Proof.
  intros.
  inversion H; subst; sigT_eq; clear H.
  pose proof (write_post _ H0 H17) as Hspec1.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition; destruct_lift H;
  do 6 eexists;
  split; [pred_apply; cancel; eauto | |pred_apply; cancel; eauto |].
  unfold same_except, equivalent_for; eauto.
  destruct_lift H0.
  erewrite <- update_subtree_same at 1; eauto.
  unfold same_except; intros.
  eapply equivalent_update_nt; cleanup; eauto.
  destruct_lift H1; eapply rep_tree_names_distinct; eauto.
  destruct_lift H1; eapply rep_tree_names_distinct; eauto.
Qed.


Theorem write_same_except_two:
  forall Fr Fm Fd Ftop ds sm pathname f tree vs mscs mscs1 mscs2 fsxp ilist frees pr off v1 v2 inum tr d bm hm d1 bm1 hm1 d2 bm2 hm2 tr1 (r1 r2: res unit) tr2,
  exec_fbasic pr tr d bm hm mscs (FWrite fsxp inum off v1) (Finished d1 bm1 hm1 r1) mscs1 tr1 ->
  exec_fbasic pr tr d bm hm mscs (FWrite fsxp inum off v2) (Finished d2 bm2 hm2 r2) mscs2 tr2 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
    exists tree1 fsxp1 ds1 sm1 ilist1 frees1 tree2 fsxp2 ds2 sm2 ilist2 frees2,
    (Fr *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm * rep fsxp1 Ftop tree1 ilist1 frees1 mscs1 sm1)]]])%pred d1 /\
    (Fr *
     LOG.rep (FSXPLog fsxp2) (SB.rep fsxp2) (LOG.NoTxn ds2) (MSLL mscs2) sm2 bm2 hm2 *
     [[[ ds2!! ::: (Fm * rep fsxp2 Ftop tree2 ilist2 frees2 mscs2 sm2)]]])%pred d2 /\
    same_except (DFOwner f) tree1 tree2.
Proof.
  intros.
  inversion H; subst; sigT_eq; clear H.
  inversion H0; subst; sigT_eq; clear H0.
  pose proof (write_post _ H1 H18) as Hspec1.
  pose proof (write_post _ H1 H17) as Hspec2.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition.
  destruct_lift H; intuition.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H2; intuition.
  do 12 eexists.
  split.
  clear H12.
  pred_apply; safecancel.
  split.
  pred_apply; cancel; eauto.
  unfold same_except, equivalent_for; eauto.

  destruct_lift H2; intuition.

  destruct_lift H; intuition.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H2; intuition.
  destruct_lift H2; intuition.
  do 12 eexists.
  split.
  pred_apply; cancel; eauto.
  split.
  pred_apply; cancel; eauto.
  unfold same_except; intros.
  eapply equivalent_update_nt; cleanup; eauto.
  destruct_lift H1; eapply rep_tree_names_distinct; eauto.
Qed.


Lemma read_equivalent_return:
  forall pathname f pr off vs inum Fd
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 mscs1' fsxp1 ilist1 frees1 d1 bm1 hm1 d1' bm1' hm1' tr1 tr1'
    Fr2 Fm2 Ftop2 ds2 sm2 tree2 mscs2 mscs2' fsxp2 ilist2 frees2 d2 bm2 hm2 d2' bm2' hm2' tr2 tr2'
    (r1 r2: block * res unit),
  exec_fbasic pr tr1 d1 bm1 hm1 mscs1 (FRead fsxp1 inum off) (Finished d1' bm1' hm1' r1) mscs1' tr1' ->
  exec_fbasic pr tr2 d2 bm2 hm2 mscs2 (FRead fsxp2 inum off) (Finished d2' bm2' hm2' r2) mscs2' tr2' ->
  (Fr1 * [[ sync_invariant Fr1 ]] *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm1 * rep fsxp1 Ftop1 tree1 ilist1 frees1 mscs1 sm1)]]] *
      [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d1 ->
  (Fr2 * [[ sync_invariant Fr2 ]] *
     LOG.rep (FSXPLog fsxp2) (SB.rep fsxp2) (LOG.NoTxn ds2) (MSLL mscs2) sm2 bm2 hm2 *
     [[[ ds2!! ::: (Fm2 * rep fsxp2 Ftop2 tree2 ilist2 frees2 mscs2 sm2)]]])%pred d2 ->
  equivalent_for (DFOwner f) tree1 tree2 ->
  r1 = r2.
Proof.  
  intros.
  assert (A: (Fr2 * [[ sync_invariant Fr2 ]] *
     LOG.rep (FSXPLog fsxp2) (SB.rep fsxp2) (LOG.NoTxn ds2) (MSLL mscs2) sm2 bm2 hm2 *
      [[[ ds2!! ::: (Fm2 * rep fsxp2 Ftop2 tree2 ilist2 frees2 mscs2 sm2)]]] *
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