Require Import Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import PermDirCache.
Require Import PermGenSepN.
Require Import ListPred.

Require Import List ListUtils.
Require Import Bytes.

Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.

Require Import Lia.
Require Import FunctionalExtensionality.

Require Import DirTree.
Require Import SuperBlock.
Require Import PermInode.
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
Import ListNotations.

Set Implicit Arguments.
Import DIRTREE.
Import AFS.


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


Definition blockmem_equivalent_for tag (bm1 bm2: block_mem) :=
  forall a,
    (bm1 a = None /\ bm2 a = None) \/
    (exists v1 v2,
       bm1 a = Some v1 /\ bm2 a = Some v2 /\
       fst v1 = fst v2 /\
       (fst v1 = tag -> snd v1 = snd v2)).


Definition same_except tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 <> tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).

Theorem extend_exec_equivalent_finished:
  forall T (p: prog T) pr tr d1 d2 bm1 bm2 hm d1' bm1' hm' tr' (r: T),
    (Fr * [[ sync_invariant Fr ]] *
    PermCacheDef.rep cs d bm *
    [[ (F * rep xp (Synced old) hm)%pred d ]] *
    [[ handles_valid bm (map ent_handle new) ]] *
    [[ blocks = extract_blocks bm (map ent_handle new) ]] *
    [[ Forall entry_valid new /\ sync_invariant F ]])%pred d1 ->
    exec pr tr d1 bm1 hm (extend xp new cs) (Finished d1' bm1' hm' r) (tr'++tr) ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2) ->
    trace_secure pr tr' ->
    exists d2' bm2', exec pr tr d2 bm2 hm p (Finished d2' bm2' hm' r) (tr'++tr) /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2').












(* I am doing something ugly in here. Type of the input 'log' has type list (addr * handle)
   and blocks of the "real log" is sitting in the block memory *)
Definition extend xp (log: input_contents) cs :=
    (* Synced *)
    let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, (ndesc, ndata), (h_addr, h_valu)) := nr in
    let '(nndesc, nndata) := ((ndesc_list log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
       (* I need to seal addr blocks to write them back *)
      ahl <- seal_all (addr_tags nndesc)
             (DescDefs.ipack (map ent_addr log));;
      h_addr <- hash_list_handle h_addr ahl;;
      (* Need a special hash instruction to hash from handle *)
      h_valu <- hash_list_handle h_valu (map ent_handle log);;
      cs <- Desc.write_aligned xp ndesc ahl cs;;
      (* I need handles to be supplied to me to write data blocks back *) 
      cs <- Data.write_aligned xp ndata (map ent_handle log) cs;;
      cs <- PermDiskLogHdr.write xp ((ndesc, ndata),
                          (ndesc + nndesc, ndata + nndata),
                          (h_addr, h_valu)) cs;;
      (* Extended *)
      cs <- PermCacheDef.begin_sync cs;;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;;
      cs <- Data.sync_aligned xp ndata nndata cs;;
      cs <- PermDiskLogHdr.sync xp cs;;
      cs <- PermCacheDef.end_sync cs;;
      (* Synced *)
      Ret ^(cs, true)
    } else {
      Ret ^(cs, false)
    }.




Definition extend_ok :
    forall xp (new: input_contents) cs pr,
    {< F old d blocks,
    PERM:pr   
    PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * rep xp (Synced old) hm)%pred d ]] *
          [[ handles_valid bm (map ent_handle new) ]] *
          [[ blocks = extract_blocks bm (map ent_handle new) ]] *
          [[ Forall entry_valid new /\ sync_invariant F ]]
    POST:bm', hm', RET: ^(cs, r) exists d',
          PermCacheDef.rep cs d' bm' * 
          ([[ r = true /\
              (F * rep xp (Synced ((padded_log old) ++
                                   (combine (map fst new) blocks))) hm')%pred d' ]] \/
           [[ r = false /\ length ((padded_log old) ++
                                   (combine (map fst new) blocks)) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:bm'', hm_crash, exists cs' d',
          PermCacheDef.rep cs' d' bm'' *
          ([[ (F * rep xp (Synced old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (Extended old (combine (map fst new) blocks)) hm_crash)%pred d' ]])
    >} extend xp new cs.

(*
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
*)
Axiom can_access_dec: forall pr t, {can_access pr t}+{~can_access pr t}.






























Ltac rewriteall :=
  match goal with
  | [H: ?x = ?x |- _ ] => clear H; repeat rewriteall
  | [H: ?x = ?y, H0: ?y = ?x |- _ ] => clear H0; repeat rewriteall
  | [H: ?x = _, H0: ?x = _ |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _, H0: _ = ?x |- _ ] => rewrite H in H0; repeat rewriteall
  (*| [H: ?x = _ |- context [?x] ] => rewrite H; repeat rewriteall *)
  end.


Ltac cleanup:= try split_match; try logic_clean; subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try some_subst;
               try clear_trace; subst; try rewriteall.

Theorem exec_equivalent_finished_blockmem:
  forall T (p: prog T) pr tr d1 d2 bm1 bm2 hm d1' bm1' hm' tr' (r: T),
    exec pr tr d1 bm1 hm p (Finished d1' bm1' hm' r) (tr'++tr) ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2) ->
    trace_secure pr tr' ->
    exists d2' bm2', exec pr tr d2 bm2 hm p (Finished d2' bm2' hm' r) (tr'++tr) /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    destruct tb.
    specialize H1 with (1:= can_access_public pr) as Hx;
    specialize (Hx r); intuition; cleanup; try congruence.
    specialize H0 with (1:= can_access_public pr) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    destruct x0, t0.
    unfold vsmerge in *; simpl in *.
    inversion H5; inversion H6; simpl in *; subst.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r); subst.
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
    inversion H10; inversion H12; simpl in *; subst.
    eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Write **)
    destruct tb, tbs, t0.
    destruct (can_access_dec pr t).
    { (** can access **)
      specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= c) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 2 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (handle_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** can't access **)
      specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public pr) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 2 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      destruct (tag_dec t2 tag); subst; intuition.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (handle_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; intuition.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
  }
  { (** Seal **)
    specialize H1 with (1:= can_access_public pr) as Hx;
    specialize (Hx r); intuition; cleanup; try congruence.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Unseal **)
    intuition.
    destruct tb; simpl in *.
    specialize H1 with (1:= H) as Hx;
    specialize (Hx h); intuition; cleanup; try congruence.
    simpl in *; intuition; subst.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
  }
  { (** Sync **)
    repeat eexists; [econstructor; eauto| |eauto].
    unfold equivalent_for in *; intros.
    specialize H0 with (1:= H) as Hx.
    unfold sync_mem.
    specialize (Hx a); intuition; cleanup; eauto.
    rewrite H4, H5; eauto.
    rewrite H3, H4; eauto.
    destruct x, x0.
    right; repeat eexists; eauto.
    unfold vsmerge in *; simpl in *; eauto.
    inversion H5; subst.
    econstructor; eauto.
    unfold vsmerge in *; simpl in *; eauto.
    inversion H6; subst; auto.
  }
  admit. (** handle hashing **)
  admit. (** handle hashing **)
  { (** Bind **)
    apply trace_app in H0 as Hx; cleanup.
    apply trace_app in H4 as Hx; cleanup.
    apply trace_secure_app_split in H3; cleanup.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H5); cleanup.
    rewrite <- app_assoc in H4.
    specialize H with (1:=H4)(2:=H7)(3:=H8)(4:=H3); cleanup.
    rewrite app_assoc in H.
    repeat eexists; [econstructor; eauto| |]; eauto.
  }
Admitted.




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
    eapply exec_equivalent_finished in Hx; eauto;
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
  inversion H; subst; repeat sigT_eq.
  eapply fbasic_return in H12; eauto.
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
Qed.

