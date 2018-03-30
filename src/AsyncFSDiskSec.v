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


Fixpoint only_reads_permitted {T} pr (p: prog T) d:=
  match p with
  | Read n => forall vs, d n = Some vs -> can_access pr (fst (fst vs))
  | Bind p1 p2 => only_reads_permitted pr p1 d /\
                 forall tr bm hm d' bm' hm' r tr',
                   exec pr tr d bm hm p1 (Finished d' bm' hm' r) tr' ->
                   only_reads_permitted pr (p2 r) d'
  | _ => True
  end.

(** Non-deterministic handle return bites us in here **)
Theorem exec_equivalent:
  forall T (p: prog T) pr tr d1 d2 bm hm d1' bm' hm' tr' (r: T),
    exec pr tr d1 bm hm p (Finished d1' bm' hm' r) tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr p d1 ->
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
    only_reads_permitted pr (fbasic_to_prog fsxp mscs p) d1 ->
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
   only_reads_permitted pr (fbasic_to_prog fsxp mscs p) d1 ->
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
    only_reads_permitted pr (fprog_to_prog fsxp mscs p) d1 ->
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