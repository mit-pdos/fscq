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
Require Import DirTree.
Require Import AsyncFS AsyncFSPost AsyncFSProg.
Require Import FMapAVL.
Require Import FMapFacts.


Set Implicit Arguments.
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

Theorem exec_equivalent_finished:
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

Theorem exec_equivalent_crashed:
  forall T (p: prog T) pr tr d1 d2 bm hm d1' bm' hm' tr',
    exec pr tr d1 bm hm p (Crashed d1' bm' hm') tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr p d1 bm hm ->
    exists d2', exec pr tr d2 bm hm p (Crashed d2' bm' hm') tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup;
  try solve [ eexists; split; [econstructor; eauto|]; eauto ].
  { (** Bind **)
    inversion H2.
    intuition.
    { (** p Crashed **)
      specialize IHp with (1:=H5)(2:=H1)(3:=H3); cleanup.
      eexists; split.
      eapply CrashBind; eauto.
      eauto.
    }
    { (** p0 crashed **)
      cleanup.
      specialize H4 with (1:=H0).
      eapply exec_equivalent_finished in H0; eauto; cleanup.
      specialize H with (1:=H5)(2:=H6)(3:=H4); cleanup.
      eexists; split.
      econstructor; eauto.
      eauto.
    }
  }
Qed.




Theorem exec_equivalent:
  forall T (p: prog T) pr tr d1 d2 bm hm (out: @result T) tr',
    exec pr tr d1 bm hm p out tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr p d1 bm hm ->
    (exists d1' bm' hm' (r: T), out = Finished d1' bm' hm' r /\
     exists d2', exec pr tr d2 bm hm p (Finished d2' bm' hm' r) tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2')) \/
    (exists d1' bm' hm', out = Crashed d1' bm' hm' /\
     exists d2', exec pr tr d2 bm hm p (Crashed d2' bm' hm') tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2')).
Proof.
  intros.
  destruct out.
  left; do 4 eexists; split; eauto.
  eapply exec_equivalent_finished; eauto.
  right; do 3 eexists; split; eauto.
  eapply exec_equivalent_crashed; eauto.
Qed.



Theorem exec_equivalent_rfinished:
  forall T T' (p1: prog T) (p2: prog T') pr tr d1 d2 bm hm d1' bm' hm' tr' (r: T),
    exec_recover pr tr d1 bm hm p1 p2 (RFinished T' d1' bm' hm' r) tr' ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    only_reads_permitted pr p1 d1 bm hm ->
    exists d2', exec_recover pr tr d2 bm hm p1 p2 (RFinished T' d2' bm' hm' r) tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2').
Proof.
  intros.
  inversion H; subst.
  eapply exec_equivalent_finished in H14; eauto; cleanup.
  exists x; split; eauto.
  econstructor; eauto.
Qed.

Fixpoint index {T} (EQ:forall (x y:T), {x=y}+{x<>y}) (item: T) (list: list T) :=
  match list with
  |nil => 0
  |h::tl => if EQ item h then
             0
           else
             S(index EQ item tl)
  end.
   
Lemma index_app_l:
  forall T EQ l1 l2 (t:T),
    In t l1 ->
    index EQ t (l1++l2) = index EQ t l1.
Proof.
  induction l1; intros.
  inversion H.
  destruct H; subst; simpl in *.
  destruct (EQ t t); try congruence.
  destruct (EQ t a); subst; eauto.
Qed.

Lemma index_in_lt:
  forall T EQ l (t:T),
    In t l -> index EQ t l < length l.
Proof.
  induction l; intros.
  inversion H.
  destruct H; subst; simpl.
  destruct (EQ t t); try congruence; try omega.
  destruct (EQ t a); subst; eauto; try omega.
  specialize IHl with (1:=H); omega.
Qed.

Lemma index_in_selN:
  forall T EQ l (t:T) def,
    In t l -> selN l (index EQ t l) def = t.
Proof.
  induction l; intros; inversion H; subst.
  simpl; auto.
  destruct (EQ t t); try congruence; auto.
  simpl.
  destruct (EQ t a); subst; eauto.
Qed.



Lemma possible_crash_equivalent:
  forall d1 cd1 d2 pr,
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    possible_crash d1 cd1 ->
    exists cd2, possible_crash d2 cd2 /\
    (forall tag, can_access pr tag -> equivalent_for tag cd1 cd2).
Proof.
  unfold equivalent_for, possible_crash; intros.
  exists(fun i => match cd1 i with
          | Some (v, []) =>
            match d1 i with
            | Some vs1 =>
              match d2 i with
              | Some vs2 =>
                Some (selN (vsmerge vs2)
                       (index tagged_block_dec v (vsmerge vs1))
                        tagged_block0, [])
              | _ => None (** Not reachable **)
              end
            | _ => None (** Not reachable **)
            end
          | _ => None
          end); split; intros.
  {
    specialize (H0 a); intuition.
    specialize H with (1:= can_access_public pr) as Hx;
    specialize (Hx a); intuition; cleanup; try congruence.
    left; auto.
    cleanup.
    specialize H with (1:= can_access_public pr) as Hx;
    specialize (Hx a); intuition; cleanup; try congruence.
    right; do 2 eexists; eauto.
    repeat split; eauto.
    apply in_selN.
    apply forall2_length in H5; setoid_rewrite <- H5.
    eapply index_in_lt; eauto.
  }

  {
    specialize (H0 a); intuition.
    cleanup; left; eauto.
    cleanup.
    specialize H with (1:=H1) as Hx;
    specialize (Hx a); intuition; cleanup; try congruence.
    right; do 2 eexists; eauto.
    repeat split; eauto.
    eapply forall2_selN with
        (n:= (index tagged_block_dec x0 (vsmerge x1))) in H6.
    constructor; eauto.
    erewrite index_in_selN in H6; eauto.
    simpl; auto.
    eapply index_in_lt; eauto.

    
    eapply forall2_selN with
        (n:= (index tagged_block_dec x0 (vsmerge x1))) in H7.
    constructor; eauto.
    erewrite index_in_selN in H7; eauto.
    simpl; auto.
    eapply index_in_lt; eauto.
  }
  
  Unshelve.
  all: exact tagged_block0.
Qed.



Theorem exec_equivalent_recover:
  forall T T' (p1: prog T) (p2: prog T') pr tr d1 bm hm tr' out,
    exec_recover pr tr d1 bm hm p1 p2 out tr' ->
    only_reads_permitted pr p1 d1 bm hm ->
    (forall tr d1 bm hm d1' bm' hm' tr' cd1',
       exec pr tr d1 bm hm p1 (Crashed d1' bm' hm') tr' ->
       possible_crash d1' cd1' ->
       only_reads_permitted pr p2 cd1' bm' hm') ->
    (forall tr d1 bm hm d1' bm' hm' tr' cd1',
       exec pr tr d1 bm hm p2 (Crashed d1' bm' hm') tr' ->
       possible_crash d1' cd1' ->
       only_reads_permitted pr p2 cd1' bm' hm') ->
    forall d2,
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    (exists d1' bm' hm' r, out = RFinished T' d1' bm' hm' r /\
     exists d2', exec_recover pr tr d2 bm hm p1 p2 (RFinished T' d2' bm' hm' r) tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2')) \/
    (exists d1' bm' hm' r, out = RRecovered T d1' bm' hm' r /\
     exists d2', exec_recover pr tr d2 bm hm p1 p2 (RRecovered T d2' bm' hm' r) tr' /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2')).
Proof.
  induction 1; intros.
  { (** p1 Finished **)
    eapply exec_equivalent_finished in H; eauto; cleanup.
    left; do 4 eexists; split; eauto.
    exists x; split; eauto.
    econstructor; eauto.
  }
  { (** p1 Crashed then p2 Finished **)
    clear IHexec_recover.
    right; do 4 eexists; split; eauto.
    specialize H3 with (1:=H)(2:=H0).
    eapply exec_equivalent_crashed in H; eauto; cleanup.
    eapply possible_crash_equivalent in H6 as Hx; eauto; cleanup.
    inversion H1; subst.
    eapply exec_equivalent_finished in H21 as Hp2; eauto; cleanup.
    eexists; split; eauto.
    econstructor; eauto.
    econstructor; eauto.
  }
  { (** p1 Crashed then p2 Crashed **)
    right; do 4 eexists; split; eauto.
    specialize H3 with (1:=H)(2:=H0).
    specialize IHexec_recover with (1:=H3)(2:=H4)(3:=H4).
    eapply exec_equivalent_crashed in H; eauto; cleanup.
    eapply possible_crash_equivalent in H6 as Hx; eauto; cleanup.
    specialize IHexec_recover with (1:=H8).
    intuition; cleanup; try congruence.
    inversion H9; subst; clear H9.
    eexists; split; eauto.
    eapply XRCrashedRecovered; eauto.
  }
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



Lemma MLog_read_orp:
  forall vs F pr d bm hm Fr a ms na xp ds,
    (Fr * [[ sync_invariant Fr ]] *
     exists raw, PermCacheDef.rep (snd ms) raw bm *
     [[ (F * MLog.rep xp (MLog.Synced na ds) (fst ms) bm hm)%pred raw ]] *
     [[[ ds ::: exists F', (F' * a |-> vs) ]]])%pred d ->
    can_access pr (fst (fst vs)) ->
    only_reads_permitted pr (MLog.read xp a ms) d bm hm.
Proof.
  intros; unfold MLog.read.
  destruct (MapUtils.AddrMap.Map.find a (MLog.MSInLog ms)) eqn:D; simpl; auto.
  intuition.
  destruct_lift H.
  denote MLog.rep as Hx; unfold MLog.rep, MLog.synced_rep in Hx.
  destruct_lift Hx.
  unfold LogReplay.map_replay in *.
  eapply map_find_In_elements_none in D.
  cleanup.
  eapply LogReplay.replay_disk_none_selN in D.
  2: pred_apply' H5; cancel.
  apply sep_star_comm in H1.
  apply sep_star_assoc in H1.
  eapply arrayN_selN_subset in H1.
  cleanup.
  eapply PermCacheDef_read_orp; eauto.
  pred_apply; cancel.
  setoid_rewrite H3.
  rewrite minus_plus.
  rewrite D; simpl; auto.
  omega.
  apply list2nmem_inbound in H5.
  rewrite LogReplay.replay_disk_length in H5.
  omega.
  Unshelve.
  exact valuset0.
Qed.

Lemma GLog_read_orp:
    forall vs F pr d bm hm Fr a ms xp ds,
    (Fr * [[ sync_invariant Fr ]] *
     exists raw, PermCacheDef.rep (snd ms) raw bm *
     [[ (F * GLog.rep xp (GLog.Cached ds) (fst ms) bm hm)%pred raw ]] *
     [[[ ds!! ::: exists F', (F' * a |-> vs) ]]])%pred d ->
    can_access pr (fst (fst vs)) ->
    only_reads_permitted pr (GLog.read xp a ms) d bm hm.
  Proof.
    intros; unfold GLog.read.
    destruct (MapUtils.AddrMap.Map.find a (GLog.MSVMap (fst ms))) eqn:D.
    simpl; auto.
    simpl; intuition.
    denote GLog.rep as Hx.
    unfold GLog.rep in Hx; destruct_lift Hx.
    eapply list2nmem_inbound in H5 as Hlen.
    erewrite <- GLog.latest_effective in H5; eauto.
    eapply GLog.diskset_vmap_find_none in D as Hx; eauto.
    erewrite GLog.dset_match_nthd_effective_fst in H2; eauto.
    eapply MLog_read_orp; eauto.
    pred_apply; cancel.
    eexists.
    apply list2nmem_array_pick.
    eapply GLog.diskset_ptsto_bound_effective; eauto.
    erewrite <- GLog.latest_effective; eauto.
    setoid_rewrite Hx; simpl; auto.
  Qed.


Lemma LOG_read_orp:
  forall pr d bm hm lxp a Fr ds sm ms Ftop vs,
    (Fr * [[ sync_invariant Fr ]] *
     LOG.rep lxp Ftop (LOG.ActiveTxn ds ds !!) ms sm bm hm *
     [[[ ds!! ::: exists F', (F' * a |-> vs) ]]])%pred d ->
    can_access pr (fst (fst vs)) ->
    only_reads_permitted pr (LOG.read lxp a ms) d bm hm.
Proof.
  intros; unfold LOG.read.
  destruct (MapUtils.AddrMap.Map.find a (LOG.MSTxn (fst ms))) eqn:D.
  simpl; auto.
  simpl; auto; intuition.
  denote LOG.rep as Hx.
  unfold LOG.rep, LOG.rep_inner in Hx. destruct_lift Hx.
  eapply GLog_read_orp; eauto.
  pred_apply; cancel.
  simpl; auto.
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

