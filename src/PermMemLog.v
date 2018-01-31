Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classes.SetoidTactics.
Require Import Mem Pred.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Eqdep_dec.
Require Import WordAuto.
Require Import Idempotent.
Require Import ListUtils.
Require Import FSLayout.
Require Import MapUtils.
Require Import FMapFacts.
Require Import Lock.

Require Export PermLogReplay.

Import ListNotations.

Set Implicit Arguments.

  Ltac solve_blockmem_subset:=
    match goal with
    | [|- block_mem_subset _ =p=> (fun _ : mem => _ c= _)] =>
      unfold pimpl; intros; solve_blockmem_subset
    | [|- _ c= _ ] =>
      auto; eapply block_mem_subset_trans;
      eauto; solve_blockmem_subset
    end.

Definition extract_block (bm: block_mem) h :=
  match bm h with
  | None => tagged_block0
  | Some tb => tb
  end.

Import AddrMap LogReplay.

Definition extract_blocks_map bm hm :=
  Map.map (fun x => extract_block bm x) hm.

Module LogNotations.

  Notation "'<<' F ',' func ':' a1 a2 ms bm hm '>>'" :=
    (exists raw, PermCacheDef.rep (snd ms%pred) raw (bm%pred) *
     lift_empty ((F * (func a1 a2 (extract_blocks_map bm (fst ms)) hm))%pred raw) *
     lift_empty (handles_valid (bm%pred) (map snd (Map.elements (fst (ms%pred))))))%pred
    (at level 100, func, F, a1, a2, ms, bm, hm at level 0, only parsing) : pred_scope.

  Notation "'<<' F ',' func ':' a1 a2 a3 ms bm hm '>>'" :=
    (exists raw, PermCacheDef.rep (snd ms%pred) raw (bm%pred) *
     lift_empty ((F * (func a1 a2 a3 (extract_blocks_map bm (fst ms)) hm))%pred raw) *
     lift_empty (handles_valid (bm%pred) (map snd (Map.elements (fst (ms%pred))))))%pred
    (at level 100, func, F, a1, a2, a3, ms, bm, hm at level 0, only parsing) : pred_scope.

  Notation "'<<' F ',' func ':' a1 a2 bm hm '--' '>>'" :=
    (exists raw cs, PermCacheDef.rep cs raw bm *
     lift_empty ((F * (func a1 a2 hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, bm, hm at level 0, only parsing) : pred_scope.

  Notation "'<<' F ',' func ':' a1 a2 a3 bm hm '--' '>>'" :=
    (exists raw cs, PermCacheDef.rep cs raw bm *
     lift_empty ((F * (func a1 a2 a3 hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, a3, bm, hm at level 0, only parsing) : pred_scope.

End LogNotations.


Module MLog.

  Import LogNotations.

  Definition mstate := Map.t handle.
  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate ms cs : memstate := (ms, cs).
  Definition MSCache (ms : memstate) := snd ms.
  Definition MSInLog (ms : memstate) := fst ms.

  Definition readOnly (ms ms' : memstate) := (fst ms = fst ms').
  
  Inductive logstate :=
  | Synced  (na : nat) (d : diskstate)
  (* Synced state: both log and disk content are synced *)

  | Flushing (d : diskstate) (ents : contents)
  (* A transaction is being flushed to the log, but not sync'ed yet
   * e.g. DiskLog.ExtendedUnsync or DiskLog.Extended *)

  | Applying (d : diskstate)
  (* In the process of applying the log to real disk locations.
     Block content might or might not be synced.
     Log might be truncated but not yet synced.
     e.g. DiskLog.Synced or DiskLog.Truncated
   *)

  | Rollback (d : diskstate)
  (* Crashed during a flush and the data no longer matches the header.
    Will eventually recover this diskstate. *)

  | Recovering (d : diskstate)
  (* In the process of recovering from a Crashed state. *)
  .

  Definition equal_unless_in (keys: list addr) (l1 l2: list valuset) :=
    length l1 = length l2 /\
    forall a,  ~ In a keys -> selN l1 a valuset0 = selN l2 a valuset0.

  Definition synced_rep xp (d : diskstate) : rawpred :=
    arrayS (DataStart xp) d.

  Definition unsync_rep xp (ms : blockmap) (old : diskstate) : rawpred :=
    (exists vs, [[ equal_unless_in (map_keys ms) old vs ]] *
     arrayS (DataStart xp) vs
    )%pred.


  Definition rep xp st mm hm :=
    ( exists log d0,
      [[ Map.Equal mm (replay_mem log bmap0) ]] *
      [[ goodSize addrlen (length d0) /\ map_valid mm d0 ]] *
    match st with
    | Synced na d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        PermDiskLog.rep xp (PermDiskLog.Synced na log) hm
    | Flushing d ents => exists na,
        [[ log_valid ents d /\ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        (PermDiskLog.rep xp (PermDiskLog.Synced na log) hm
      \/ PermDiskLog.rep xp (PermDiskLog.Extended log ents) hm)
    | Applying d => exists na,
        [[ map_replay mm d0 d ]] *
        (((PermDiskLog.rep xp (PermDiskLog.Synced na log) hm) *
          (unsync_rep xp mm d0))
      \/ ((PermDiskLog.rep xp (PermDiskLog.Truncated log) hm) *
          (synced_rep xp d)))
    | Rollback d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        PermDiskLog.rep xp (PermDiskLog.Rollback log) hm
    | Recovering d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        PermDiskLog.rep xp (PermDiskLog.Recovering log) hm
    end)%pred.


  (* some handy state wrappers used in crash conditons *)

  Definition would_recover_before xp d hm :=
    (exists mm, rep xp (Applying d) mm hm \/
     exists mm na', rep xp (Synced na' d) mm hm)%pred.

  Definition would_recover_either xp d ents hm :=
     (exists mm,
      (exists na', rep xp (Synced na' d) mm hm) \/
      (exists na', rep xp (Synced na' (replay_disk ents d)) mm hm) \/
      rep xp (Flushing d ents) mm hm \/
      rep xp (Applying d) mm hm \/
      rep xp (Recovering d) mm hm)%pred.

  Theorem sync_invariant_rep : forall xp st mm hm,
    sync_invariant (rep xp st mm hm).
  Proof.
    unfold rep, synced_rep, unsync_rep; destruct st; intros; eauto 20.
  Qed.

  Hint Resolve sync_invariant_rep.

  Theorem sync_invariant_would_recover_before : forall xp d hm,
    sync_invariant (would_recover_before xp d hm).
  Proof.
    unfold would_recover_before; eauto.
  Qed.

  Theorem sync_invariant_would_recover_either : forall xp d ents hm,
    sync_invariant (would_recover_either xp d ents hm).
  Proof.
    unfold would_recover_either; eauto 10.
  Qed.

  Hint Resolve sync_invariant_would_recover_before sync_invariant_would_recover_either.

  
  (******************  Program *)

  Definition read xp a ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    match Map.find a oms with
    | Some h => Ret ^(ms, h)
    | None =>
        let^ (cs, h) <- PermCacheDef.read_array (DataStart xp) a cs;;
        Ret ^(mk_memstate oms cs, h)
    end.

  Definition flush_noapply xp ents ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    let^ (cs, ok) <- PermDiskLog.extend xp ents cs;;
    If (bool_dec ok true) {
      Ret ^(mk_memstate (replay_mem ents oms) cs, true)
    } else {
      Ret ^(mk_memstate oms cs, false)
    }.

  Definition apply xp ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- PermCacheDef.write_vecs (DataStart xp) (Map.elements oms) cs;;
    cs <- PermCacheDef.sync_vecs_now (DataStart xp) (map_keys oms) cs;;
    cs <- PermDiskLog.trunc xp cs;;
    Ret (mk_memstate hmap0 cs).

  Definition flush xp ents ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    If (addr_eq_dec (length ents) 0) {
      Ret ^(ms, true)
    } else {
      let^ (cs, na) <- PermDiskLog.avail xp cs;;
      let ms := (mk_memstate oms cs) in
      ms' <- If (lt_dec na (length ents)) {
        ms <- apply xp ms;;
        Ret ms
      } else {
        Ret ms
      };;
      r <- flush_noapply xp ents ms';;
      Ret r
   }.

  Definition sync_cache (xp : log_xparams) ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- PermCacheDef.sync_all cs;;
    Ret (mk_memstate oms cs).

  Definition dwrite xp a v ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- If (MapFacts.In_dec oms a) {
      ms <- apply xp ms;;
      Ret ms
    } else {
      Ret ms
    };;
    cs' <- PermCacheDef.write_array (DataStart xp) a v (MSCache ms');;
    Ret (mk_memstate (MSInLog ms') cs').


  Definition dsync xp a ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs' <- PermCacheDef.begin_sync cs;;
    cs' <- PermCacheDef.sync_array (DataStart xp) a cs';;
    cs' <- PermCacheDef.end_sync cs';;
    Ret (mk_memstate oms cs').

  Definition recover xp cs :=
    cs <- PermDiskLog.recover xp cs;;
    let^ (cs, log) <- PermDiskLog.read xp cs;;
    Ret (mk_memstate (replay_mem log (@gmap0 handle)) cs).

  Definition init (xp : log_xparams) cs :=
    cs <- PermDiskLog.init xp cs;;
    Ret (mk_memstate hmap0 cs).


  Arguments PermDiskLog.rep: simpl never.
  Hint Extern 0 (okToUnify (PermDiskLog.rep _ _ _) (PermDiskLog.rep _ _ _)) => constructor : okToUnify.



  (****** auxiliary lemmas *)



  Lemma rep_hashmap_subset : forall xp mm hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st mm hm
        =p=> rep xp st mm hm'.
  Proof.
    unfold rep; intros.
    destruct st; cancel.
    all: eauto.
    all: erewrite PermDiskLog.rep_hashmap_subset; eauto; cancel.
    or_l; cancel.
    or_r; cancel.
    Unshelve. all: easy.
  Qed.

  Lemma would_recover_either_hashmap_subset : forall xp d ents hm hm',
    (exists l, hashmap_subset l hm hm')
    -> would_recover_either xp d ents hm
        =p=> would_recover_either xp d ents hm'.
  Proof.
    unfold would_recover_either; intros; cancel.
    all: erewrite rep_hashmap_subset; eauto; cancel.
  Qed.

  Lemma synced_applying : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    exists ms', rep xp (Applying d) ms' hm.
  Proof.
    unfold rep, map_replay, unsync_rep, synced_rep in *.
    cancel; eauto.
    or_l; cancel.
    unfold equal_unless_in; intuition.
  Qed.

  Lemma synced_flushing : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    exists ms' ents, rep xp (Flushing d ents) ms' hm.
  Proof.
    unfold rep, map_replay, unsync_rep, synced_rep in *.
    cancel; eauto.
    or_l.
    eassign na.
    unfold PermDiskLog.rep. cancel; eauto.
    cancel.
    unfold log_valid; intuition.
    unfold KNoDup; auto.
    inversion H1.
    inversion H1.
  Qed.


  Lemma equal_unless_in_length_eq : forall a b l,
    equal_unless_in l a b -> length b = length a.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.

  Lemma apply_synced_data_ok' : forall l d,
    NoDup (map fst l) ->
    vssync_vecs (vsupd_vecs d l) (map fst l) = replay_disk l d.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl.
    inversion H; subst.
    rewrite <- IHl by auto.

    rewrite vsupd_vecs_vsupd_notin by auto.
    rewrite vssync_vsupd_eq.
    rewrite updN_vsupd_vecs_notin; auto.
  Qed.

  Lemma apply_synced_data_ok : forall xp m d,
    arrayS (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (map_keys m))
    =p=> synced_rep xp (replay_disk (Map.elements m) d).
  Proof.
    unfold synced_rep; intros.
    apply arrayN_unify.
    apply apply_synced_data_ok'.
    apply KNoDup_NoDup; auto.
  Qed.


  Lemma apply_unsync_applying_ok' : forall l d n,
    NoDup (map fst l) ->
    equal_unless_in (map fst l) d (vsupd_vecs d (firstn n l)).
  Proof.
    unfold equal_unless_in; induction l; intros; simpl.
    rewrite firstn_nil; simpl; intuition.
    split; intuition;
    destruct n; simpl; auto;
    destruct a; inversion H; simpl in *; intuition; subst.

    rewrite vsupd_vecs_vsupd_notin.
    rewrite vsupd_length, vsupd_vecs_length; auto.
    rewrite <- firstn_map_comm.
    contradict H2.
    eapply in_firstn_in; eauto.

    pose proof (IHl d n H5) as [Hx Hy].
    rewrite Hy by auto.
    rewrite vsupd_vecs_vsupd_notin.
    unfold vsupd; rewrite selN_updN_ne; auto.
    rewrite <- firstn_map_comm.
    contradict H4.
    eapply in_firstn_in; eauto.
  Qed.


  Lemma apply_unsync_applying_ok : forall xp m d n,
    arrayS (DataStart xp) (vsupd_vecs d (firstn n (Map.elements m)))
       =p=> unsync_rep xp m d.
  Proof.
    unfold unsync_rep, map_replay; cancel.
    apply apply_unsync_applying_ok'.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma apply_unsync_syncing_ok' : forall l a d n,
    NoDup (map fst l) ->
    ~ In a (map fst l) ->
    selN d a valuset0 = selN (vssync_vecs (vsupd_vecs d l) (firstn n (map fst l))) a valuset0.
  Proof.
    induction l; intros; simpl.
    rewrite firstn_nil; simpl; auto.

    destruct a; inversion H; simpl in *; subst; intuition.
    destruct n; simpl; auto.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite selN_updN_ne by auto.
    rewrite vsupd_vecs_selN_not_in; auto.

    unfold vssync.
    rewrite -> updN_vsupd_vecs_notin by auto.
    rewrite <- IHl; auto.
    rewrite selN_updN_ne by auto.
    unfold vsupd.
    rewrite selN_updN_ne; auto.
  Qed.

  Lemma apply_unsync_syncing_ok : forall xp m d n,
    arrayS (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (firstn n (map_keys m)))
       =p=> unsync_rep xp m d.
  Proof.
    unfold unsync_rep, equal_unless_in; cancel.
    rewrite vssync_vecs_length, vsupd_vecs_length; auto.
    apply apply_unsync_syncing_ok'.
    apply KNoDup_NoDup; auto.
    eauto.
  Qed.


  Lemma rep_rollback_pimpl : forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=>
      rep xp (Recovering d) ms hm.
  Proof.
    unfold rep; intros.
    cancel; eauto.
    rewrite PermDiskLog.rep_rollback_pimpl; eauto.
    cancel.
  Qed.

  Lemma rep_synced_pimpl : forall xp nr d ms hm,
    rep xp (Synced nr d) ms hm =p=>
      rep xp (Recovering d) ms hm.
  Proof.
    unfold rep; intros.
    cancel; eauto.
    rewrite PermDiskLog.rep_synced_pimpl; eauto.
    cancel.
  Qed.


  Theorem recover_before_either : forall xp d ents hm,
    would_recover_before xp d hm =p=>
    would_recover_either xp d ents hm.
  Proof.
    unfold would_recover_before, would_recover_either; cancel.
  Qed.

  Theorem synced_recover_before : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    would_recover_before xp d hm.
  Proof.
    unfold would_recover_before; cancel.
    Unshelve. eauto.
  Qed.

  Theorem synced_recover_either : forall xp na d ms ents hm,
    rep xp (Synced na d) ms hm =p=>
    would_recover_either xp d ents hm.
  Proof.
    unfold would_recover_either; cancel.
  Qed.

  Theorem rollback_recover_either : forall xp d ms ents hm,
    rep xp (Rollback d) ms hm =p=>
    would_recover_either xp d ents hm.
  Proof.
    unfold would_recover_either; cancel.
    rewrite rep_rollback_pimpl.
    or_r; or_r; or_r; cancel.
  Qed.

  Theorem applying_recover_before : forall xp d ms hm,
    rep xp (Applying d) ms hm =p=>
    would_recover_before xp d hm.
  Proof.
    unfold would_recover_before; cancel.
  Qed.

  Theorem synced_recover_after : forall xp na d ms ents hm,
    rep xp (Synced na (replay_disk ents d)) ms hm =p=>
    would_recover_either xp d ents hm.
  Proof.
    unfold would_recover_either; intros.
    (** FIXME:
     * `cancel` works slowly when there are existentials.
     *  (when calling `apply finish_frame`)
     *)
    norm; unfold stars; simpl; auto.
    or_r; or_l; cancel.
  Qed.

  Theorem applying_recover_after : forall xp d ms ents hm,
    rep xp (Applying d) ms hm =p=>
    would_recover_either xp d ents hm.
  Proof.
    unfold would_recover_either; cancel.
  Qed.

  Theorem flushing_recover_after : forall xp d ms ents hm,
    rep xp (Flushing d ents) ms hm =p=>
    would_recover_either xp d ents hm.
  Proof.
    unfold would_recover_either; intros.
    norm; unfold stars; simpl; auto.
    or_r; or_r; cancel.
  Qed.

  Lemma map_not_In_empty:
    forall (V : Type) (m : Map.t V),
      (forall a,  ~ Map.In a m) ->
      Map.Empty m.
  Proof.
    intros.
    unfold Map.Empty, not; intros.
    eapply H.
    exists e. apply H0.
  Qed.

  
  

  (** specs *)


  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

  Section UnfoldProof1.
  Local Hint Unfold rep map_replay: hoare_unfold.

  
  Definition init_ok :
    forall xp cs pr,
    {< F l m d,
    PERM:pr   
    PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * arrayS (DataStart xp) m *
              arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET: ms  exists d' nr,
          let bmap := extract_blocks_map bm' (MSInLog ms) in
          PermCacheDef.rep (MSCache ms) d' bm' *
          [[ handles_valid bm' (map snd (Map.elements (MSInLog ms))) ]] *
          [[ (F * rep xp (Synced nr m) bmap hm')%pred d' ]]
    XCRASH:bm'', hm_crash, any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    step.
    step.
    unfold handles_valid; rewrite Forall_forall; intuition.
    rewrite PermDiskLog.rep_hashmap_subset; eauto; cancel.
    simpl.
    unfold bmap0, hmap0, gmap0; simpl.
    apply is_empty_eq_map0.
    apply Map.is_empty_1.
    apply map_not_In_empty; unfold not; intros x Hx.
    unfold Map.In in Hx; cleanup.
    denote (Map.MapsTo _ _ _) as Hx.
    apply MapFacts.map_mapsto_iff in Hx; cleanup.
    eapply MapFacts.empty_mapsto_iff; eauto.

    eapply goodSize_trans; [ | eauto ]; omega.
    apply map_valid_map0.
    solve_hashmap_subset.
    Unshelve.
    exact tagged_block.
    all: eauto.
    apply bmap0.
  Qed.

    Lemma handles_valid_app:
        forall hl1 hl2 bm,
          handles_valid bm (hl1++hl2) ->
          handles_valid bm hl1 /\ handles_valid bm hl2.
      Proof.
        unfold handles_valid; intros.
        split; [eapply forall_app_r; eauto
               | eapply forall_app_l; eauto ].
      Qed.

      Lemma handles_valid_cons:
        forall h hl bm,
          handles_valid bm (h::hl) ->
          handle_valid bm h /\ handles_valid bm hl.
      Proof.
        unfold handles_valid; intros.
        inversion H; eauto.
      Qed.

    Lemma map_find_extract_blocks_mem:
      forall hmap bm a h,
        Map.find a hmap = Some h ->
        handles_valid bm (map snd (Map.elements hmap)) ->
        Map.find a (extract_blocks_map bm hmap) =
            Some (extract_block bm h).
    Proof.
      intro hmap; destruct hmap.
      generalize dependent this;
      induction this; unfold Map.find, Map.elements in *; simpl in *;
      intros; try congruence.
      inversion is_bst; subst.
      unfold AddrMap_AVL.Raw.elements in H0; simpl in H0.
      repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in H0.
      rewrite app_nil_r, map_app in H0; simpl in H0.
      apply handles_valid_app in H0; intuition.
      apply handles_valid_cons in H2; intuition.
      cleanup; intuition.
    Qed.

Lemma extract_blocks_map_extract_blocks_eq:
      forall hmap bm,
        handles_valid bm (map snd (Map.elements hmap)) ->
        map snd (Map.elements (extract_blocks_map bm hmap)) =
        extract_blocks bm (map snd (Map.elements hmap)).
    Proof.
      intro hmap; destruct hmap.
      generalize dependent this;
      induction this; simpl; intros; auto.
      inversion is_bst; subst.
      unfold Map.elements, AddrMap_AVL.Raw.elements in *; simpl in *.
      repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
      repeat rewrite app_nil_r, map_app in *; simpl in *.
      repeat (simpl; rewrite extract_blocks_app).
      simpl in *.
      apply handles_valid_app in H; intuition.
      apply handles_valid_cons in H1; intuition.
      unfold extract_block, handle_valid in *; cleanup.
      unfold AddrMap_AVL.Raw.elements; rewrite H, H2; auto.
    Qed.      

    Lemma map_find_In_elements:
        forall hmap a (h: handle),
          Map.find a hmap = Some h ->
          In h (map snd (Map.elements hmap)).
      Proof.
         intro hmap; destruct hmap.
         generalize dependent this;
         induction this; unfold Map.find, Map.elements in *;
         simpl; intros; auto; try congruence.
         inversion is_bst; subst.
         unfold Map.elements, AddrMap_AVL.Raw.elements in *; simpl in *.
         repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
         repeat rewrite app_nil_r, map_app in *; simpl in *.
         simpl in *.
         apply in_or_app.
         cleanup; intuition.
         left; eapply H0; eauto.
         right; simpl; right; eapply H1; eauto.
      Qed.

      Lemma map_find_In_elements_none:
        forall hmap bm a,
          Map.find a hmap = None ->
          Map.find a (extract_blocks_map bm hmap) = None.
      Proof.
         intro hmap; destruct hmap.
         generalize dependent this;
         induction this; unfold Map.find, Map.elements in *;
         simpl in *; intros; auto; try congruence.
         inversion is_bst; subst.
         cleanup; intuition eauto; congruence.
      Qed.
    
    Lemma extract_blocks_map_subset_trans:
      forall hmap bm bm',
        handles_valid bm (map snd (Map.elements hmap)) ->
        bm c= bm' ->
        Map.Equal (extract_blocks_map bm hmap)
                  (extract_blocks_map bm' hmap).
    Proof.
      intros.
      unfold Map.Equal; intros.
      destruct (Map.find y hmap) eqn:D.
      repeat erewrite map_find_extract_blocks_mem; eauto.
      unfold extract_block.
      destruct (bm h) eqn:D0.
      erewrite block_mem_subset_extract_some; eauto.
      apply map_find_In_elements in D.
      unfold handles_valid, handle_valid  in *;
      rewrite Forall_forall in H.
      specialize (H _ D); cleanup; congruence.
      eapply handles_valid_subset_trans; eauto.
      repeat erewrite map_find_In_elements_none; eauto.
    Qed.

  
  Theorem read_ok:
    forall xp ms a pr,
    {< F d na vs,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Synced na d) ms bm hm >> *
      [[[ d ::: exists F', (F' * a |-> vs) ]]]
    POST:bm', hm', RET:^(ms', r)
      << F, rep: xp (Synced na d) ms' bm' hm' >> *
      [[ extract_block bm' r = fst vs ]] *
      [[ readOnly ms ms' ]]
    CRASH:bm'', hm'',
      exists ms', << F, rep: xp (Synced na d) ms' bm'' hm'' >>
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.

    cancel.
    step.
    eapply PermDiskLog.rep_hashmap_subset; eauto.
    subst.
    eapply replay_disk_eq; eauto.
    eassign a; eassign (extract_blocks_map bm ms_1).
    apply map_find_extract_blocks_mem; auto.
    eassign dummy1; pred_apply; cancel.
    unfold false_pred; cancel.

    unfold synced_rep; cancel.
    subst; eapply synced_data_replay_inb; eauto.
    eassign (Map.elements (extract_blocks_map bm ms_1));
    pred_apply; cancel.

    step.
    prestep.
    cancel; subst; auto.
    eapply PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.

    eapply MapFacts.Equal_trans.
    apply MapFacts.Equal_sym.
    apply extract_blocks_map_subset_trans; eauto.
    auto.

    eapply map_valid_equal; eauto.
    apply extract_blocks_map_subset_trans; eauto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
    unfold extract_block; rewrite H15.

    assert (selN dummy1 a valuset0 = (t, l)) as Hx.
    erewrite replay_disk_none_selN; eauto.
    eassign (extract_blocks_map bm ms_1).
    apply map_find_In_elements_none; auto.
    pred_apply; cancel.
    destruct (selN _ a _); inversion Hx; auto.
    unfold readOnly; simpl; auto.
    solve_hashmap_subset.

    rewrite <- H1; cancel; eauto.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    eapply MapFacts.Equal_trans.
    apply MapFacts.Equal_sym.
    apply extract_blocks_map_subset_trans; eauto.
    auto.

    eapply map_valid_equal; eauto.
    apply extract_blocks_map_subset_trans; eauto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
  Qed.

  End UnfoldProof1.



  Local Hint Resolve log_valid_nodup.


  Section UnfoldProof2.
  Local Hint Unfold rep map_replay synced_rep: hoare_unfold.


Lemma map_add_extract_blocks_mem_comm:
  forall hmap bm a x,
    bm (snd a) = Some x ->
    Map.Equal (Map.add (fst a) x (extract_blocks_map bm hmap))
              (extract_blocks_map bm
                                  (Map.add (fst a) (snd a) hmap)).
Proof.
  intro hmap; destruct hmap.
  generalize dependent this;
  induction this;
  simpl in *; intros; auto; try congruence.
  unfold Map.Equal, Map.find; simpl; unfold extract_block;
  cleanup; eauto.

  unfold Map.Equal in *; simpl in *; intros.
  unfold extract_blocks_map in *.
  rewrite MapFacts.map_o; unfold option_map.
  inversion is_bst; subst.
  destruct (OrderedTypeEx.Nat_as_OT.eq_dec (fst a) y).
  { (* fst a = y *)
    repeat rewrite MapFacts.add_eq_o; auto.
    unfold extract_block; cleanup; auto.
  }
  { (* fst a <> y *) 
    repeat rewrite MapFacts.add_neq_o in *; auto.
    rewrite MapFacts.map_o; unfold option_map; auto.
  }
Qed.



Lemma extract_blocks_map_replay_mem_comm:
  forall ents bm hmap,
    handles_valid bm (map ent_handle ents) ->
    Map.Equal (replay_mem (List.combine (map fst ents)
                                        (extract_blocks bm (map snd ents)))
                          (extract_blocks_map bm hmap))
              (extract_blocks_map bm (replay_mem ents hmap)).
Proof.
  induction ents; simpl; intros; auto.
  apply MapFacts.Equal_refl.
  apply handles_valid_cons in H;
  unfold ent_handle, handle_valid in *; cleanup; simpl in *.
  eapply MapFacts.Equal_trans; [ | eauto ].
  apply replay_mem_equal.
  apply map_add_extract_blocks_mem_comm; auto.
Qed.

Lemma log_valid_combine:
  forall T B (ents: @generic_contents B) (l: list T) d,
    log_valid ents d ->
    log_valid (List.combine (map fst ents) l) d.
Proof.
  unfold log_valid; induction ents; simpl; intros; auto.
  intuition.
  constructor.
  inversion H.
  inversion H.
  destruct l.
  intuition.
  constructor.
  inversion H.
  inversion H.
  edestruct IHents.
  intuition.
  inversion H0; subst; auto.
  edestruct H1.
  right; eauto.
  auto.
  edestruct H1.
  right; eauto.
  eauto.
  intuition.
  constructor; eauto.
  {
    unfold not; intros.
    inversion H2.
    apply H6.
    destruct a;
    apply In_KIn.
    apply InA_alt in H; cleanup.
    destruct x0; simpl  in *.
    inversion H; simpl in *; subst.
    eapply in_combine_l; eauto.
  }
  {
    destruct a; simpl in *.
    inversion H; subst.
    inversion H6; simpl in *; subst.        
    edestruct H3.
    left; eauto.
    simpl in *; eauto.
    edestruct H1; eauto.
  }
  {
    destruct a; simpl in *.
    inversion H; subst.
    inversion H5; simpl in *; subst.        
    edestruct H3.
    left; eauto.
    simpl in *; eauto.
    edestruct H1; eauto.
  }
  Unshelve.
  all: auto.
Qed.

Lemma handles_valid_replay_mem:
  forall ents hmap bm,
    KNoDup ents ->
    handles_valid bm (map snd ents) ->
    handles_valid bm (map snd (Map.elements hmap)) ->
    handles_valid bm (map snd (Map.elements (replay_mem ents hmap))).
Proof.
  unfold handles_valid; induction ents; simpl; intros; auto.
  destruct a; inversion H; subst.
  erewrite mapeq_elements;
  [| apply replay_mem_add; auto].
  simpl.
  inversion H0; subst; intuition.
  rewrite Forall_forall; intros.
  apply in_map_iff in H2; cleanup.
  destruct x0; simpl in *.
  eapply In_InA in H3; eauto.
  apply Map.elements_2 in H3.

  destruct (OrderedTypeEx.Nat_as_OT.eq_dec k0 k); subst.
  apply mapsto_add in H3; subst; auto.
  apply Map.add_3 in H3; auto.
  apply Map.elements_1 in H3.
  apply InA_alt in H3; cleanup.
  destruct x; inversion H2; simpl in *; subst.
  eapply (in_map snd) in H3; simpl in *.
  setoid_rewrite Forall_forall in IHents at 3.
  eapply IHents in H3; eauto.
Qed.
  
  Theorem flush_noapply_ok:
    forall xp (ents: input_contents) ms pr,
    {< F d na,
    PERM:pr   
    PRE:bm, hm,
       << F, rep: xp (Synced na d) ms bm hm >> *
       [[ handles_valid bm (map snd ents) ]] *            
       [[ log_valid ents d /\ sync_invariant F ]]
    POST:bm', hm', RET:^(ms',r)
       let blocks := List.combine (map fst ents)
                             (extract_blocks bm' (map snd ents)) in
        ([[ r = true ]]  * exists na',                                      
          << F, rep: xp (Synced na' (replay_disk blocks d))
                                           ms' bm' hm' >>) \/
        ([[ r = false /\ length ents > na ]] *
          << F, rep: xp (Synced na d) ms' bm' hm' >>)
    XCRASH:bm'', hm'',  exists ms',
          let blocks := List.combine (map fst ents)
                             (extract_blocks bm'' (map snd ents)) in
          << F, rep: xp (Flushing d blocks) ms' bm'' hm'' >>
    >} flush_noapply xp ents ms.
  Proof.
    unfold flush_noapply.
    step.
    eapply log_valid_entries_valid; eauto.
    step.
    step.
    step.

    or_l.
    cancel; unfold map_merge.
    eapply PermDiskLog.rep_hashmap_subset; eauto.
    rewrite replay_mem_app; eauto.
    apply MapFacts.Equal_sym.
    eapply MapFacts.Equal_trans;
    [| apply extract_blocks_map_replay_mem_comm; eauto].
    erewrite extract_blocks_subset; eauto.
    apply replay_mem_equal.
    apply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.    

    eapply map_valid_equal.
    apply extract_blocks_map_replay_mem_comm; auto.
    eapply handles_valid_subset_trans; eauto. 
    apply map_valid_replay_mem'; auto.
    eapply log_valid_replay; eauto.   
    apply log_valid_combine; auto.
    eapply map_valid_equal; [| eauto].
    apply extract_blocks_map_subset_trans; auto.
    rewrite replay_disk_replay_mem; auto.
    erewrite mapeq_elements; eauto.
    eapply MapFacts.Equal_trans;
    [| apply extract_blocks_map_replay_mem_comm; eauto].
    erewrite extract_blocks_subset; eauto.
    apply replay_mem_equal.
    apply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
    apply log_valid_combine; auto.
    eapply handles_valid_subset_trans.
    apply handles_valid_replay_mem; eauto.
    eauto.
    solve_hashmap_subset.

    step.
    step.
    step.
    step.

    or_r; cancel.
    eapply PermDiskLog.rep_hashmap_subset; eauto.
    eapply MapFacts.Equal_trans; eauto.
    eapply MapFacts.Equal_sym;
    apply extract_blocks_map_subset_trans; auto.
    
    eapply map_valid_equal; eauto.
    apply extract_blocks_map_subset_trans; auto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel; eauto.
    xcrash.
    or_l; cancel.
    eapply MapFacts.Equal_trans; eauto.
    eapply MapFacts.Equal_sym;
    apply extract_blocks_map_subset_trans; auto.
    
    eapply map_valid_equal; eauto.
    apply extract_blocks_map_subset_trans; auto.
    apply log_valid_combine; auto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.

    or_r; cancel.
    erewrite extract_blocks_subset; eauto.
    eapply MapFacts.Equal_trans; eauto.
    eapply MapFacts.Equal_sym;
    apply extract_blocks_map_subset_trans; auto.

    eapply map_valid_equal; eauto.
    apply extract_blocks_map_subset_trans; auto.
    apply log_valid_combine; auto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.

    Unshelve.
    auto.
  Qed.

  End UnfoldProof2.



  Section UnfoldProof3.
  Local Hint Unfold rep map_replay would_recover_before: hoare_unfold.
  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

  Lemma goodSize_vssync_vsupd_vecs : forall l ents ks,
    goodSize addrlen (length l) ->
    goodSize addrlen (length (vssync_vecs (vsupd_vecs l ents) ks)).
  Proof.
    intros. rewrite vssync_vecs_length, vsupd_vecs_length; auto.
  Qed.

  Lemma map_valid_vssync_vsupd_vecs :
    forall T l mm ents ks,
    @map_valid T mm l ->
    map_valid mm (vssync_vecs (vsupd_vecs l ents) ks).
  Proof.
    intros.
    eapply length_eq_map_valid; eauto.
    rewrite vssync_vecs_length, vsupd_vecs_length; auto.
  Qed.

  Lemma replay_disk_vssync_vsupd_vecs : forall d mm,
    replay_disk (Map.elements mm) d =
    vssync_vecs (vsupd_vecs d (Map.elements mm)) (map_keys mm).
  Proof.
    intros; rewrite apply_synced_data_ok'. auto.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma replay_disk_vssync_vsupd_vecs_twice : forall d mm,
    replay_disk (Map.elements mm) d =
    replay_disk (Map.elements mm) (vssync_vecs (vsupd_vecs d (Map.elements mm)) (map_keys mm)).
  Proof.
    intros; rewrite apply_synced_data_ok'; auto.
    rewrite replay_disk_twice; auto.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma replay_disk_vsupd_vecs' : forall l d,
    KNoDup l ->
    replay_disk l (vsupd_vecs d l) =
    replay_disk l d.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst; simpl in *.
    assert (~ In k (map fst l)).
    contradict H2.
    apply In_KIn; auto.

    rewrite replay_disk_updN_comm; auto.
    rewrite IHl; unfold vsupd; auto.
    rewrite replay_disk_updN_comm; auto.
    rewrite updN_twice.
    rewrite replay_disk_updN_comm; auto.
  Qed.

  Lemma replay_disk_vsupd_vecs : forall mm d,
    replay_disk (Map.elements mm) (vsupd_vecs d (Map.elements mm)) =
    replay_disk (Map.elements mm) d.
  Proof.
    intros.
    apply replay_disk_vsupd_vecs'.
    auto.
  Qed.


  Local Hint Resolve goodSize_vssync_vsupd_vecs map_valid_map0
                     map_valid_vssync_vsupd_vecs KNoDup_NoDup
                     replay_disk_vssync_vsupd_vecs replay_disk_vssync_vsupd_vecs_twice
                     replay_disk_vsupd_vecs.


  Lemma in_fst_snd_map_split:
    forall A B (l: list (A * B)) x y,
      In (x,y) l ->
      In x (map fst l) /\ In y (map snd l).
  Proof.
    induction l; simpl; intros; auto.
    destruct a; intuition; simpl in *.
    inversion H0; subst; auto.
    inversion H0; subst; auto.
    right; specialize (IHl x y H0); intuition.
    right; specialize (IHl x y H0); intuition.
  Qed.
  
  Lemma in_fst:
    forall A B (l: list (A * B)) x y,
      In (x,y) l -> In x (map fst l).
  Proof.
    intros; apply in_fst_snd_map_split in H; intuition.
  Qed.

  Lemma in_fst_exists_snd:
    forall A B (l: list (A * B)) x,
      In x (map fst l) ->
      exists y, In (x, y) l.
  Proof.
    induction l; simpl; intros; intuition.
    destruct a; simpl in *; subst; eexists; eauto.
    specialize (IHl x H0); destruct IHl; eauto.
  Qed.

  Lemma in_extract_blocks_map:
    forall hmap bm x y b,
      In (x,y) (Map.elements hmap) ->
      bm y = Some b ->
      In (x,b) (Map.elements (extract_blocks_map bm hmap)).
  Proof.
    intro hmap; destruct hmap.
    generalize dependent this;
    induction this;
    simpl in *; intros; auto; try congruence.
    unfold Map.elements,
    AddrMap_AVL.Raw.elements in *; simpl in *;
    unfold extract_block; cleanup; eauto.
    rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
    apply in_app_iff.
    apply in_app_iff in H.
    inversion is_bst; subst.
    intuition.
    left; eapply H; eauto.
    inversion H1.
    inversion H3; subst; cleanup.
    right; left; auto.
    right; right; eapply H2; eauto.
  Qed.

  Lemma Forall_extract_blocks_mem_addr_in_len:
    forall A hmap bm (l: list A),
      handles_valid bm (map snd (Map.elements hmap)) ->
      Forall (fun e : addr * tagged_block => fst e < length l)
             (Map.elements (extract_blocks_map bm hmap)) ->
      Forall (fun e : addr * handle => fst e < length l)
             (Map.elements hmap).
  Proof.
    unfold handles_valid, handle_valid; intros;
    rewrite Forall_forall in *; intros.
    destruct x ; simpl in *.
    apply in_fst_snd_map_split in H1 as Hx; intuition.
    specialize (H h H3); cleanup.
    eapply in_extract_blocks_map in H1; eauto.
    specialize (H0 _ H1); simpl in *; auto.
  Qed.

  Lemma Forall_map_keys:
    forall A hmap (l: list A),
      Forall (fun e : addr * handle => fst e < length l)
             (Map.elements hmap) ->
      Forall (fun e : addr => e < length l)
             (map_keys hmap).
  Proof.
    unfold handles_valid, handle_valid, map_keys; intros;
    rewrite Forall_forall in *; intros.
    apply in_fst_exists_snd in H0; cleanup.
    specialize (H _ H0); simpl in *; auto.
  Qed.

  Lemma extract_blocks_map_empty:
    forall bm,
      Map.Equal (extract_blocks_map bm hmap0) bmap0.
  Proof.
    unfold Map.Equal; intros;    
    unfold extract_blocks_map, bmap0, hmap0, gmap0, map0; simpl.
    rewrite MapFacts.map_o; unfold option_map;
    repeat rewrite MapFacts.empty_o; auto.
  Qed.


  Lemma map_keys_extract_blocks_map_eq:
    forall hmap bm,
      map_keys (extract_blocks_map bm hmap) = map_keys hmap.
  Proof.
    intro hmap; destruct hmap.
    generalize dependent this;
    induction this;
    simpl in *; intros; auto; try congruence.
    unfold map_keys, Map.elements,
    AddrMap_AVL.Raw.elements in *; simpl in *;
    unfold extract_block in *; cleanup; eauto.
    repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
    repeat rewrite map_app; simpl in *.
    inversion is_bst; subst.
    unfold AddrMap_AVL.Raw.elements;
    erewrite app_nil_r,  IHthis1, IHthis2; auto; simpl.
    repeat rewrite app_nil_r; auto.
  Qed.

  Lemma combine_elements_eq:
    forall hmap bm,
      handles_valid bm (map snd (Map.elements hmap)) ->
      List.combine (map fst (Map.elements hmap))
                   (extract_blocks bm (map snd (Map.elements hmap))) =
      (Map.elements (extract_blocks_map bm hmap)).
  Proof.
    intro hmap; destruct hmap.
    generalize dependent this;
    induction this;
    simpl in *; intros; auto; try congruence.
    unfold handles_valid, handle_valid, Map.elements,
    AddrMap_AVL.Raw.elements in *; simpl in *;
    unfold extract_block in *; cleanup; eauto.
    repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
    repeat rewrite map_app in *; simpl in *.
    inversion is_bst; subst.
    
    rewrite extract_blocks_app; simpl.
    rewrite combine_app.
    repeat rewrite app_nil_r in *.
    eapply forall_app_l in H as Hl.
    apply forall_app_r in H as Hr.
    inversion Hl; cleanup; simpl.
    unfold AddrMap_AVL.Raw.elements;
    erewrite IHthis1, IHthis2; auto; simpl.
    apply length_map_fst_extract_blocks_eq.
    unfold handles_valid, handle_valid;
    apply forall_app_r in H; auto.
  Qed.
      

  
  Theorem apply_ok:
    forall xp ms pr,
    {< F d na,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Synced na d) ms bm hm >> *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Synced (LogLen xp) d) ms' bm' hm' >> *
      [[ Map.Empty (MSInLog ms') ]]
    XCRASH:bm'', hm'',
      << F, would_recover_before: xp d bm'' hm'' -- >>
    >} apply xp ms.
  Proof.
    unfold apply; intros.
    step.
    unfold synced_rep; cancel.
    eapply Forall_extract_blocks_mem_addr_in_len; eauto. 

    step.
    rewrite vsupd_vecs_length.
    apply Forall_map_keys.
    eapply Forall_extract_blocks_mem_addr_in_len; eauto.

    safestep.
    erewrite PermDiskLog.rep_hashmap_subset.
    cancel.
    solve_hashmap_subset.
    auto.

    step.
    safestep.
    unfold synced_rep; eauto.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    cancel.
    simpl.
    apply extract_blocks_map_empty.
    rewrite vssync_vecs_length, vsupd_vecs_length; eauto.
    eapply map_valid_equal; eauto.
    eapply MapFacts.Equal_sym.
    eapply MapFacts.Equal_trans.
    apply extract_blocks_map_empty.
    unfold bmap0; apply MapFacts.Equal_refl.
    rewrite replay_disk_vssync_vsupd_vecs; auto.
    rewrite map_keys_extract_blocks_map_eq.
    rewrite combine_elements_eq; auto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
    apply Forall_nil.
    solve_hashmap_subset.
    solve_blockmem_subset.

    (* crash conditions *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash_rewrite.
    rewrite combine_elements_eq; auto.
    erewrite mapeq_elements with (m2:= extract_blocks_map bm ms_1).
    erewrite <- map_keys_extract_blocks_map_eq with (bm:= bm).
    setoid_rewrite <- firstn_exact with
        (l:=  (map_keys (extract_blocks_map bm ms_1))) at 1.
    setoid_rewrite apply_unsync_syncing_ok.
    setoid_rewrite apply_synced_data_ok.
    xcrash; or_l; safecancel; eauto.
    apply MapFacts.Equal_sym.
    apply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash.
    rewrite <- extract_blocks_subset with (bm:= bm).
    rewrite combine_elements_eq.
    rewrite <- firstn_exact with
        (l:= Map.elements (extract_blocks_map bm ms_1)).
    rewrite apply_unsync_applying_ok.
    or_l; safecancel; eauto.
    erewrite PermDiskLog.rep_hashmap_subset.
    cancel.
    solve_hashmap_subset.
    rewrite firstn_exact; auto.
    all: auto.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash_rewrite.
    rewrite <- extract_blocks_subset with (bm:= bm).
    rewrite combine_elements_eq.
    setoid_rewrite apply_unsync_applying_ok.
    xcrash.
    or_l; safecancel; eauto.
    erewrite PermDiskLog.rep_hashmap_subset.
    cancel.
    solve_hashmap_subset.
    all: auto.

    Unshelve.
    all: eauto; unfold EqDec; apply handle_eq_dec.
  Qed.

  End UnfoldProof3.


  Local Hint Unfold map_replay : hoare_unfold.
  Hint Extern 1 ({{_|_}} Bind (apply _ _) _) => apply apply_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (flush_noapply _ _ _) _) => apply flush_noapply_ok : prog.
  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.

  Theorem flush_ok:
    forall xp ents ms pr,
    {< F d na,
     PERM: pr   
     PRE:bm, hm,
         << F, rep: xp (Synced na d) ms bm hm >> *
         [[ handles_valid bm (map snd ents) ]] * 
         [[ log_valid ents d /\ sync_invariant F ]]
     POST:bm', hm', RET:^(ms',r)
          exists na',
          let blocks:= List.combine (map fst ents)
               (extract_blocks bm' (map snd ents)) in
          ([[ r = true ]] *
           << F, rep: xp (Synced na' (replay_disk blocks d)) ms' bm' hm' >>) \/
          ([[ r = false /\ length ents > (LogLen xp) ]] *
           << F, rep: xp (Synced na' d) ms' bm' hm' >>)
     XCRASH:bm'', hm'',
       let blocks:= List.combine (map fst ents)
            (extract_blocks bm'' (map snd ents)) in  
          << F, would_recover_either: xp d blocks bm'' hm'' -- >>
    >} flush xp ents ms.
  Proof.
    unfold flush; intros.

    (* Be careful: only unfold rep in the preconditon,
       otherwise the goal will get messy as there are too many
       disjuctions in post/crash conditons *)
    prestep.
    unfold rep at 1.
    cancel.
    step.
    step.
    cancel.
    or_l; cancel.
    unfold rep; cancel.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    auto.
    unfold map_replay.
    rewrite length_nil with (l:=ents); eauto.

    (* case 1: apply happens *)
    prestep.
    cancel; auto.
    step.
    safestep.
    unfold rep; cancel.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    eapply map_valid_equal; [| eauto ].
    eapply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    auto.

    safestep.
    safestep.
    rewrite rep_hashmap_subset; eauto.
    cancel.
    eapply handles_valid_subset_trans; eauto.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    auto.

    step.
    step.

    or_l; cancel.
    erewrite mapeq_elements.
    erewrite rep_hashmap_subset; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    solve_hashmap_subset.

    step.
    or_r; cancel.
    erewrite mapeq_elements.
    erewrite rep_hashmap_subset; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    solve_hashmap_subset.

    (* crashes *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash.
    rewrite flushing_recover_after; cancel.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    cancel.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash.
    rewrite recover_before_either; cancel.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    
    (* case 2: no apply *)
    step.
    prestep.
    unfold rep at 1.
    safecancel.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    cancel.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    eapply map_valid_equal; [| eauto ].
    eapply extract_blocks_map_subset_trans; auto.
    unfold map_replay.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    auto.
    step.
    step.

    or_l; cancel.
    erewrite mapeq_elements.
    erewrite rep_hashmap_subset; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    solve_hashmap_subset.
   

    (* crashes *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash.
    rewrite flushing_recover_after; cancel.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.

    rewrite <- H1; cancel.
    cancel.
    unfold would_recover_either, rep.
    eapply pimpl_exists_r; eexists.
    or_l; cancel; eauto.
    solve_hashmap_subset.

    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Lemma empty_extract_blocks_map:
    forall hmap bm,
      Map.Empty hmap ->
      Map.Empty (extract_blocks_map bm hmap).
  Proof.
    unfold Map.Empty, not; intros.
    apply MapFacts.map_mapsto_iff in H0; cleanup; eauto.
  Qed.

  Lemma map_in_extract_blocks_map:
    forall hmap a bm,
      Map.In a (extract_blocks_map bm hmap) ->
      Map.In a hmap.
  Proof.
    unfold extract_blocks_map; intros; eapply Map.map_2; eauto.
  Qed.

  Theorem dwrite_ok:
    forall xp a h ms pr,
    {< F Fd d na vs v,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Synced na d) ms bm hm >> *
      [[ bm h = Some v ]] *            
      [[[ d ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      exists d' na',
      << F, rep: xp (Synced na' d') ms' bm' hm' >> *
      [[ d' = updN d a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    XCRASH:bm'', hm'',
      << F, would_recover_before: xp d bm'' hm'' -- >> \/
      exists ms' na' d',
      << F, rep: xp (Synced na' d') ms' bm'' hm'' >> *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]] *
      [[ d' = updN d a (v, vsmerge vs) ]]
    >} dwrite xp a h ms.
  Proof.
    unfold dwrite, would_recover_before.
    step.

    (* case 1: apply happens *)
    prestep.
    denote rep as Hx; unfold rep, synced_rep in Hx; destruct_lift Hx.
    norm. cancel. intuition simpl.
    pred_apply; unfold rep, synced_rep; cancel.
    auto.

    unfold rep, synced_rep.
    safestep.
    safestep.
    eapply block_mem_subset_extract_some; eauto.
    replace (length _) with (length (replay_disk (Map.elements (extract_blocks_map bm ms_1)) dummy0)).
    eapply list2nmem_inbound; eauto.
    erewrite replay_disk_length.
    erewrite replay_disk_eq_length_eq; eauto.

    step.
    step.
    unfold rep, synced_rep; cancel.
    rewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eauto.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    unfold vsupd, map_replay.
    rewrite replay_disk_updN_comm.
    denote (replay_disk _ _ = replay_disk _ _) as Hreplay.
    rewrite Hreplay.
    f_equal. f_equal. f_equal.
    erewrite <- replay_disk_selN_other at 1.
    erewrite list2nmem_sel with (x := (t, l)).
    erewrite <- Hreplay; eauto.
    eauto.
    intuition. denote In as HIn.
    apply In_map_fst_MapIn in HIn.
    eapply map_empty_not_In; [| eauto].
    apply empty_extract_blocks_map; auto.

    intuition. denote In as HIn.
    apply In_map_fst_MapIn in HIn.
    eapply map_empty_not_In; [| eauto].
    apply empty_extract_blocks_map; auto.
    
    eapply list2nmem_updN; eauto.
    solve_hashmap_subset.

    (* crashes for case 1 *)
    norml.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash.
    or_r; cancel.
    xform_normr; cancel.
    unfold rep, synced_rep, unsync_rep, map_replay.
    xform_normr; cancel; eauto.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.

    rewrite vsupd_length; eauto.
    
    eapply length_eq_map_valid.
    2: apply vsupd_length.
    eapply map_valid_equal; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    unfold vsupd, map_replay.
    rewrite replay_disk_updN_comm.
    denote (replay_disk _ _ = replay_disk _ _) as Hreplay.
    rewrite Hreplay.
    f_equal. f_equal.
    apply mapeq_elements.
    eapply extract_blocks_map_subset_trans; auto.

    erewrite <- replay_disk_selN_other.
    erewrite list2nmem_sel with (x := (t, l)).
    erewrite <- Hreplay; eauto.
    eauto.
    intuition. denote In as HIn.
    apply In_map_fst_MapIn in HIn.
    eapply map_empty_not_In; [| eauto].
    apply empty_extract_blocks_map; auto.

    intuition. denote In as HIn.
    apply In_map_fst_MapIn in HIn.
    eapply map_empty_not_In; [| eauto].
    apply empty_extract_blocks_map; auto.

    eapply handles_valid_subset_trans; eauto.
    eapply list2nmem_updN; eauto.

    cancel.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    or_l; cancel.
    xform; cancel.
    xform_normr.
    norm. cancel.
    intuition simpl; pred_apply.
    unfold would_recover_before.
    denote map_replay as Hd. rewrite <- Hd; cancel.
    or_l; cancel.
    or_r; cancel.

    (* case 2: no apply *)
    denote (rep _ _ _) as Hx.
    unfold rep, synced_rep, map_replay in Hx; destruct_lift Hx.
    step.
    step.
    erewrite <- replay_disk_length.
    eapply list2nmem_inbound; eauto.

    step.
    step.
    unfold rep, synced_rep, map_replay; cancel.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eauto.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    unfold eqlen, vsupd; autorewrite with lists; auto.
    eapply replay_disk_updN_eq_not_in; eauto.

    unfold not; intros HIn.
    apply H16; eapply map_in_extract_blocks_map; eauto.
    eapply list2nmem_updN; eauto.
    solve_hashmap_subset.

    (* crashes for case 2 *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    or_r; cancel.
    xform_normr; cancel.
    unfold rep, synced_rep, unsync_rep, map_replay.
    xform_normr; cancel; eauto.
    erewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    rewrite vsupd_length; eauto.

    eapply length_eq_map_valid.
    2: apply vsupd_length.
    eapply map_valid_equal; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    erewrite mapeq_elements.
    eapply replay_disk_updN_eq_not_in; eauto.
    unfold not; intros;
    apply H16; eapply map_in_extract_blocks_map; eauto.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.
    eapply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    eapply list2nmem_updN; eauto.
    
    Unshelve. all: eauto.
    unfold EqDec; apply handle_eq_dec.
    exact (Synced 0 nil).
    exact bmap0.
  Qed.

  Section UnfoldProof4.
  Local Hint Unfold rep map_replay synced_rep: hoare_unfold.

  Theorem dsync_ok:
    forall xp a ms pr,
    {< F Fd d na vs,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Synced na d) ms bm hm >> *
      [[[ d ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists d' na',
      << F, rep: xp (Synced na' d') ms' bm' hm' >> *
      [[[ d' ::: (Fd * a |-> (fst vs, nil)) ]]] *
      [[  d' = vssync d a ]]
    CRASH:bm'', hm'',
      exists ms' na',
      << F, rep: xp (Synced na' d) ms' bm'' hm'' >>
    >} dsync xp a ms.
  Proof.
    unfold dsync.
    step.
    safestep.
    eassign F_; cancel.
    pred_apply; cancel.
    subst; erewrite <- replay_disk_length.
    eapply list2nmem_inbound; eauto.
    auto.
    auto.
    safestep.
    eassign F_; cancel.
    auto.

    step.
    step.
    rewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    unfold vssync; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    setoid_rewrite <- replay_disk_vssync_comm.
    unfold vssync.
    erewrite <- list2nmem_sel; eauto; simpl.
    eapply list2nmem_updN; eauto.
    setoid_rewrite replay_disk_vssync_comm.
    auto.
    solve_hashmap_subset.
    
    (* crashes *)
    rewrite <- H1; cancel.
    rewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.

    eapply map_valid_equal; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    erewrite mapeq_elements; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    rewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.

    eapply map_valid_equal; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    erewrite mapeq_elements; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    rewrite PermDiskLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    eapply MapFacts.Equal_trans; eauto.
    apply MapFacts.Equal_sym.
    eapply extract_blocks_map_subset_trans; auto.

    eapply map_valid_equal; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    erewrite mapeq_elements; eauto.
    eapply extract_blocks_map_subset_trans; auto.
    eapply handles_valid_subset_trans; eauto.
    solve_hashmap_subset.    
  Qed.

  End UnfoldProof4.




  (********* dwrite/dsync for a list of address/value pairs *)

  Definition dwrite_vecs xp avl ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- If (bool_dec (overlap (map fst avl) oms) true) {
      ms <- apply xp ms;
      Ret ms
    } else {
      Ret ms
    };
    cs' <- BUFCACHE.write_vecs (DataStart xp) avl (MSCache ms');
    Ret (mk_memstate (MSInLog ms') cs').


  Definition dsync_vecs xp al ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs' <- BUFCACHE.sync_vecs_now (DataStart xp) al cs;
    Ret (mk_memstate oms cs').


  (****************** crash and recovery *)

  Lemma map_valid_replay_mem_synced_list : forall x0 x3 x4 l',
    map_valid x0 x4 ->
    possible_crash_list x4 l' ->
    Map.Equal x0 (replay_mem x3 vmap0) ->
    map_valid (replay_mem x3 vmap0) (synced_list l').
  Proof.
    intros.
    eapply map_valid_equal; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite synced_list_length.
    erewrite <- possible_crash_list_length; eauto.
  Qed.

  Hint Rewrite selN_combine repeat_selN' Nat.min_id synced_list_length : lists.

  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints lists)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with lists .. ]).

  Ltac simplen' := repeat match goal with
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : context[Nat.min ?a ?a] |- _ ] => rewrite Nat.min_id in H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : equal_unless_in _ _ _ |- _ ] => apply equal_unless_in_length_eq in H
    | [H : possible_crash_list _ _ |- _ ] => apply possible_crash_list_length in H
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac simplen :=  auto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with lists); simpl; eauto; try omega.

  Ltac map_rewrites :=
    match goal with
    | [ H : Map.Equal (replay_mem ?x ?y) _ |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal (MapFacts.Equal_sym H))
    | [ H : Map.Equal _ (replay_mem ?x ?y) |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal H)
    | [ H : Map.Equal _  (replay_mem ?x ?y)
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements (MapFacts.Equal_sym H))
    | [ H : Map.Equal (replay_mem ?x ?y) _
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements H)
    end.

  Ltac t :=
    repeat map_rewrites;
    try match goal with
      | [ H : goodSize _ ?a |- goodSize _ ?b ] => simplen
      | [ H : map_valid ?a _ |- map_valid ?a _ ] =>
          solve [ eapply (length_eq_map_valid _ H); simplen ]
      | [ |- map_valid (replay_mem _ _) (synced_list _) ] =>
          try solve [ eapply map_valid_replay_mem_synced_list; eauto ]
    end.

  Lemma equal_unless_in_possible_crash : forall l a b c,
    equal_unless_in l (synced_list a) b ->
    possible_crash_list b c ->
    forall i, ~ In i l -> selN a i $0 = selN c i $0.
  Proof.
    unfold equal_unless_in, possible_crash_list, synced_list.
    intros; simpl in *; autorewrite with lists in *; intuition.
    destruct (lt_dec i (length b)).

    destruct (H4 i l0).
    rewrite <- H0.
    rewrite <- H3 by auto.
    rewrite selN_combine; simplen.

    contradict H0.
    rewrite <- H3 by auto.
    rewrite selN_combine by simplen; simpl.
    rewrite repeat_selN; simplen.
    repeat rewrite selN_oob; simplen.
  Qed.

  Lemma equal_unless_in_updN : forall B l a (b : B) v d d',
    ~ KIn (a, b) l ->
    equal_unless_in (a :: map fst l) d d' ->
    equal_unless_in (map fst l) (updN d a (v, nil)) (updN d' a (v, nil)).
  Proof.
    unfold equal_unless_in, synced_list; intuition; simpl in *.
    simplen.
    destruct (lt_dec a0 (length d)).
    destruct (Nat.eq_dec a a0); simplen.
    repeat rewrite selN_updN_ne by auto.
    rewrite <- H2; simplen; tauto.
    repeat rewrite selN_oob; simplen.
  Qed.

  Lemma equal_unless_in_sym : forall l a b,
    equal_unless_in l a b <-> equal_unless_in l b a.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.

  Lemma equal_unless_in_refl : forall l a,
    equal_unless_in l a a.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.

  Lemma equal_unless_in_replay_disk' : forall l a b,
    KNoDup l ->
    equal_unless_in (map fst l) a b ->
    replay_disk l a = replay_disk l b.
  Proof.
    induction l; intuition; simpl.
    eapply list_selN_ext; intros.
    simplen.
    apply H0; auto.

    inversion H; simpl in *; subst.
    eapply IHl; auto.
    eapply equal_unless_in_updN; eauto.
  Qed.

  Lemma equal_unless_in_replay_disk : forall a b m,
    equal_unless_in (map_keys m) b a ->
    replay_disk (Map.elements m) a = replay_disk (Map.elements m) b.
  Proof.
    intros.
    eapply equal_unless_in_replay_disk'; eauto.
    apply equal_unless_in_sym; auto.
  Qed.

  Lemma list2nmem_replay_disk_crash_xform : forall ents vsl vl (F : rawpred),
    KNoDup ents ->
    possible_crash_list vsl vl ->
    F (list2nmem (replay_disk ents vsl)) ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).
  Proof.
    induction ents; simpl; intros.
    eapply list2nmem_crash_xform; eauto.
    inversion H; destruct a; simpl in *; subst.
    rewrite synced_list_updN.
    eapply IHents; eauto.
    apply possible_crash_list_updN; auto.
  Qed.


  Lemma crash_xform_list2nmem_replay_disk : forall F ents vsl vl,
    crash_xform F (list2nmem (replay_disk ents vsl)) ->
    possible_crash_list vsl vl ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).
  Proof.
    induction ents; simpl; intros.
    erewrite <- crash_xform_list2nmem_list_eq; eauto.
    destruct a; simpl in *.
    rewrite synced_list_updN.
    eapply IHents; eauto.
    apply possible_crash_list_updN; auto.
  Qed.


  Lemma map_valid_replay_mem_app : forall a ents l' x0 x1,
     Map.Equal x0 (replay_mem a vmap0) ->
     map_valid x0 x1 ->
     possible_crash_list x1 l' ->
     log_valid ents (replay_disk (Map.elements (elt:=valu) x0) x1) ->
     map_valid (replay_mem (a ++ ents) vmap0) (synced_list l').
  Proof.
      intros.
      eapply map_valid_equal.
      apply MapFacts.Equal_sym.
      apply replay_mem_app; auto.
      apply MapFacts.Equal_refl.
      apply map_valid_replay_mem'.
      destruct H2; split; intros; auto.
      specialize (H3 _ _ H4); destruct H3.
      simplen.
      eapply map_valid_equal; eauto.
      unfold map_valid; intros.
      destruct (H0 _ _ H3); simplen.
  Qed.

  Lemma in_vsmerge_incl_trans : forall v vs vs',
    In v (vsmerge vs) ->
    fst vs = fst vs' ->
    incl (snd vs) (snd vs') ->
    In v (vsmerge vs').
  Proof.
    unfold vsmerge; simpl in *; intuition simpl in *; subst.
    left; auto.
    right.
    eapply incl_tran; eauto.
    apply incl_refl.
  Qed.

  Lemma possible_crash_vsupd_vecs_listupd : forall F m x st l avl,
    (F * arrayS st l)%pred m ->
    possible_crash m x ->
    possible_crash (listupd m st (vsupd_vecs l avl)) x.
  Proof.
    unfold possible_crash; intuition.
    specialize (H0 a).
    destruct (listupd_sel_cases (vsupd_vecs l avl) a st m ($0, nil)).
    denote listupd as Hx; destruct Hx as [Hx Heq]; rewrite Heq; intuition.

    intuition; denote listupd as Hx; rewrite Hx.
    eapply arrayN_selN_subset with (a := a) (def := ($0, nil)) in H;
    repeat deex; try congruence.
    erewrite <- vsupd_vecs_length; eauto.

    eapply arrayN_selN_subset with (a := a) (def := ($0, nil)) in H; auto.
    right; repeat deex; repeat eexists; eauto.
    replace vs0 with vs in * by congruence.
    apply vsupd_vecs_selN_vsmerge_in; auto.
    eapply in_vsmerge_incl_trans; eauto.
    erewrite <- vsupd_vecs_length; eauto.
  Qed.

  Lemma dwrite_vecs_xcrash_ok : forall cs d raw xp F avl m n n' log hm,
    overlap (map fst avl) m <> true ->
    map_valid m d ->
    Map.Equal m (replay_mem log vmap0) ->
    goodSize addrlen (length d) ->
    ((DLog.rep xp (DLog.Synced n' log) hm * F) * 
      arrayS (DataStart xp) (vsupd_vecs d (firstn n avl)))%pred raw ->
    crash_xform (BUFCACHE.rep cs raw) =p=> 
      crash_xform (exists ms na, 
      << F, rep: xp (Synced na (vsupd_vecs (replay_disk (Map.elements m) d) avl)) ms hm >>).
  Proof.
    intros.
    rewrite BUFCACHE.crash_xform_rep.
    unfold rep, map_replay, synced_rep; xform_norm.
    cancel; xform_normr.
    rewrite <- BUFCACHE.crash_xform_rep_r.
    cancel.

    eassign (listupd raw (DataStart xp) (vsupd_vecs d avl)).
    denote arrayN as Ha; eapply arrayN_listupd_subset with (l := (vsupd_vecs d avl)) in Ha.

    pred_apply; cancel.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    rewrite replay_disk_vsupd_vecs_nonoverlap.
    repeat rewrite vsupd_vecs_length; auto.
    apply not_true_is_false; auto.
    repeat rewrite vsupd_vecs_length; auto.
    erewrite <- firstn_skipn with (l := avl) (n := n).
    rewrite vsupd_vecs_app.
    eapply possible_crash_vsupd_vecs_listupd; eauto.
  Qed.


  Lemma dwrite_vecs_xcrash_ok_empty : forall cs d raw xp F avl m n n' log hm,
    Map.Empty m ->
    Map.Equal m (replay_mem log vmap0) ->
    goodSize addrlen (length d) ->
    ((DLog.rep xp (DLog.Synced n' log) hm * F) * 
      arrayS (DataStart xp) (vsupd_vecs d (firstn n avl)))%pred raw ->
    crash_xform (BUFCACHE.rep cs raw) =p=> 
        crash_xform (exists ms na, 
        << F, rep: xp (Synced na (vsupd_vecs (replay_disk (Map.elements m) d) avl)) ms hm >>).
  Proof.
    intros.
    eapply dwrite_vecs_xcrash_ok; eauto.
    rewrite overlap_empty; auto.
    apply map_valid_empty; auto.
  Qed.


  Lemma crash_xform_applying : forall xp d mm hm,
    crash_xform (rep xp (Applying d) mm hm) =p=>
      exists na d' mm', (rep xp (Synced na d') mm' hm) *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    unfold rep, synced_rep, unsync_rep, map_replay; intros.
    xform_norml.
    - rewrite DLog.xform_rep_synced.
      rewrite crash_xform_arrayN_subset.
      cancel; eauto. simplen.
      eapply length_eq_map_valid; eauto. simplen.

      eapply list2nmem_replay_disk_crash_xform; eauto.
      erewrite <- equal_unless_in_replay_disk; eauto.
      unfold diskIs; auto.

    - rewrite DLog.xform_rep_truncated.
      rewrite crash_xform_arrayN_subset.
      cancel; eauto; try solve [simplen].

      eapply length_eq_map_valid; eauto; simplen.
      eapply list2nmem_replay_disk_crash_xform; eauto.
      rewrite replay_disk_twice; auto.
      unfold diskIs; auto.

      apply MapFacts.Equal_refl.
      apply map_valid_map0.
      eapply list2nmem_replay_disk_crash_xform; eauto.
      unfold diskIs; cbn; auto.
  Qed.


  Lemma crash_xform_synced : forall xp nr d ms hm,
    crash_xform (rep xp (Synced nr d) ms hm) =p=>
      exists d' ms' nr', rep xp (Synced nr' d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    intros.
    rewrite synced_applying.
    xform_norm.
    rewrite crash_xform_applying; cancel.
  Qed.


  Lemma crash_xform_applying_applying : forall xp d ms hm,
    crash_xform (rep xp (Applying d) ms hm) =p=>
      exists d' ms', rep xp (Applying d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    intros.
    rewrite crash_xform_applying; eauto.
    norml; unfold stars; simpl.
    rewrite synced_applying; cancel.
  Qed.

  Lemma crash_xform_flushing : forall xp d ents ms hm,
    crash_xform (rep xp (Flushing d ents) ms hm) =p=>
      exists d' ms',
        (exists nr, rep xp (Synced nr d') ms' hm *
          ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
           [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]])) \/
        (rep xp (Rollback d') ms' hm *
          [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]]).
  Proof.
    unfold rep, synced_rep, unsync_rep, map_replay; intros.
    xform_norml.

    - rewrite crash_xform_arrayN_subset.
      rewrite DLog.xform_rep_synced.
      cancel.
      or_l; cancel; eauto; try solve [simplen].
      or_l; cancel.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      eapply length_eq_map_valid; eauto; simplen.

    - rewrite crash_xform_arrayN_subset.
      rewrite DLog.xform_rep_extended.
      cancel.

      or_l; cancel; eauto; try solve [simplen].
      or_l; cancel.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      eapply length_eq_map_valid; eauto; simplen.

      or_l; cancel; eauto; try solve [simplen].
      or_r; cancel.
      eassign (replay_mem (Map.elements ms ++ ents) vmap0).
      erewrite replay_disk_replay_mem; auto.
      rewrite replay_mem_app'.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      rewrite replay_mem_app'.
      symmetry.
      apply replay_mem_app; auto.
      eapply map_valid_replay_mem_synced_list.
      eassign x0.
      3: apply MapFacts.Equal_refl.
      rewrite replay_mem_app'.
      eapply map_valid_replay_mem'; eauto.
      eapply log_valid_replay; eauto.
      auto.

      or_r; cancel; eauto; try solve [simplen].
      eapply length_eq_map_valid; eauto; simplen.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.

  Lemma crash_xform_recovering' : forall xp d ms hm,
    crash_xform (rep xp (Recovering d) ms hm) =p=>
      exists d' ms',
        ((exists nr, rep xp (Synced nr d') ms' hm) \/
          rep xp (Rollback d') ms' hm) *
        [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    unfold rep, synced_rep, map_replay; intros.
    xform_norml.
    rewrite DLog.xform_rep_recovering, crash_xform_arrayN_subset.
    cancel.
    or_r; cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.

    or_l; cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.

  Lemma crash_xform_rollback : forall xp d ms hm,
    crash_xform (rep xp (Rollback d) ms hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    unfold rep, synced_rep; intros.
    xform_norm.
    rewrite DLog.xform_rep_rollback, crash_xform_arrayN_subset.
    cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    unfold map_replay in *; subst.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.

  Lemma crash_xform_before : forall xp d hm,
    crash_xform (would_recover_before xp d hm) =p=>
      exists d' ms' na, rep xp (Synced na d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    unfold would_recover_before; intros.
    xform_norm.
    rewrite crash_xform_applying; cancel.
    rewrite crash_xform_synced; cancel.
  Qed.


  Definition recover_either_pred xp d ents hm :=
    (exists d' ms',
      (exists nr, rep xp (Synced nr d') ms' hm *
        ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]])) \/
      (rep xp (Rollback d') ms' hm *
        [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]]))%pred.

  Lemma crash_xform_either : forall xp d ents hm,
    crash_xform (would_recover_either xp d ents hm) =p=>
                  recover_either_pred xp d ents hm.
  Proof.
    unfold would_recover_either, recover_either_pred; intros.
    xform_norm.
    rewrite crash_xform_synced by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
    rewrite crash_xform_synced by eauto; cancel.
    or_l; cancel.
    or_r; cancel.
    rewrite crash_xform_flushing by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
    or_l; cancel.
    or_r; cancel.
    rewrite crash_xform_applying by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
    rewrite crash_xform_recovering' by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
  Qed.

  Lemma crash_xform_recovering : forall xp d ms ents hm,
    crash_xform (rep xp (Recovering d) ms hm) =p=>
      recover_either_pred xp d ents hm.
  Proof.
    unfold recover_either_pred; intros.
    rewrite crash_xform_recovering'.
    cancel.
    or_l; cancel.
    or_l; cancel.
  Qed.

  Lemma either_pred_either : forall xp d hm ents,
    recover_either_pred xp d ents hm =p=>
    exists d', would_recover_either xp d' ents hm.
  Proof.
    unfold recover_either_pred, would_recover_either.
    intros; xform_norm; cancel.
    erewrite rep_rollback_pimpl. cancel.
  Qed.

  Lemma recover_idem : forall xp d ents hm,
    crash_xform (recover_either_pred xp d ents hm) =p=>
                 recover_either_pred xp d ents hm.
  Proof.
    intros.
    unfold recover_either_pred.
    xform_norm.

    rewrite crash_xform_synced; cancel.
    or_l; cancel.
    or_l; cancel.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite crash_xform_synced; cancel.
    or_l; cancel.
    or_r; cancel.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite crash_xform_rollback; cancel.
    or_r; cancel.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.


  Theorem recover_ok: forall xp cs,
    {< F raw d ents,
    PRE:hm
      BUFCACHE.rep cs raw *
      [[ (F * recover_either_pred xp d ents hm)%pred raw ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists raw',
      BUFCACHE.rep (MSCache ms') raw' *
      [[(exists d' na, F * rep xp (Synced na d') (MSInLog ms') hm' *
        ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]]
      ))%pred raw' ]]
    XCRASH:hm'
      exists cs' raw' ms', BUFCACHE.rep cs' raw' *
      [[ (exists d', F * rep xp (Recovering d') ms' hm' *
         ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]]
        ))%pred raw' ]]
    >} recover xp cs.
  Proof.
    unfold recover, recover_either_pred, rep.
    prestep. norm'l. unfold stars; cbn.
    denote or as Hx. apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H;
    denote (Map.Equal _ _) as Heq.
    safecancel. eassign F_. cancel. or_l; cancel.
    unfold synced_rep; auto. auto.

    denote or as Hx. apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H.

    (* Synced, case 1: We crashed to the old disk. *)
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    prestep. norm. cancel.
    intuition simpl; auto.
    pred_apply. cancel.
    or_l; cancel.
    rewrite <- Heq; auto.
    rewrite <- Heq; auto.
    cancel.
    xcrash; eauto.
    rewrite DLog.rep_synced_pimpl; cancel.
    or_l; cancel.

    (* Synced, case 2: We crashed to the new disk. *)
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    or_r; cancel.
    rewrite <- Heq; auto.
    rewrite <- Heq; auto.
    norm'l.
    xcrash; eauto.
    rewrite DLog.rep_synced_pimpl; cancel.
    or_r; cancel.
    denote or as Hx. apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H.
    xcrash; eauto.
    or_l; cancel.
    xcrash; eauto.
    or_r; cancel.

    (* Rollback *)
    safecancel.
    eassign F_; cancel.
    or_r; cancel.
    unfold synced_rep; auto. auto.
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    prestep. norm. cancel.
    intuition simpl; auto.
    pred_apply. cancel.
    or_l; cancel.
    rewrite <- Heq; auto.
    rewrite <- Heq; auto.
    norm'l.
    xcrash; eauto.
    rewrite DLog.rep_synced_pimpl; cancel.
    or_l; cancel.
    xcrash; eauto.
    or_l; cancel.

    Unshelve. exact valu. all: eauto. all: econstructor; eauto.
  Qed.


  Theorem dwrite_vecs_ok : forall xp avl ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ Forall (fun e => fst e < length d) avl /\ sync_invariant F ]]
    POST:hm' RET:ms' exists na',
      << F, rep: xp (Synced na' (vsupd_vecs d avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >> \/
      exists na' ms',
      << F, rep: xp (Synced na' (vsupd_vecs d avl)) ms' hm' >>
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs, would_recover_before.
    step.

    (* case 1: apply happens *)
    step.
    prestep.
    unfold rep at 1.
    unfold synced_rep, map_replay in *.
    cancel; auto.
    erewrite <- replay_disk_length.
    eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    repeat rewrite replay_disk_empty; auto.

    (* crashes for case 1 *)
    norm'l. unfold stars; cbn.
    xcrash.
    or_r.
    rewrite dwrite_vecs_xcrash_ok_empty; eauto.
    xform_norm; cancel.
    xform_normr; cancel.
    eassign x2; eassign (x1_1, x1_2); eauto.
    pred_apply; eauto.
    pred_apply; rewrite firstn_oob; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.

    xcrash.
    or_l; cancel.
    xform_normr; cancel.

    (* case 2: no apply *)
    denote rep as Hx; unfold rep, synced_rep, map_replay in Hx.
    destruct_lift Hx.
    step.
    erewrite <- replay_disk_length; eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    erewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    apply replay_disk_vsupd_vecs_nonoverlap; auto.
    apply not_true_is_false; auto.

    (* crashes for case 2 *)
    xcrash.
    or_r.
    rewrite dwrite_vecs_xcrash_ok; eauto.
    xform_norm; cancel.
    xform_normr; cancel.
    eassign x2; eassign (x1_1, x1_2); eauto.
    pred_apply; eauto.
    pred_apply; rewrite firstn_oob; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.



  Theorem dsync_vecs_ok: forall xp al ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ Forall (fun e => e < length d) al /\ sync_invariant F ]]
    POST:hm' RET:ms' exists na',
      << F, rep: xp (Synced na' (vssync_vecs d al)) ms' hm' >>
    CRASH:hm' exists na' ms',
      << F, rep: xp (Synced na' d) ms' hm' >>
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs, rep, synced_rep, map_replay.
    step.
    subst; erewrite <- replay_disk_length; eauto.

    step.
    erewrite DLog.rep_hashmap_subset; eauto.
    rewrite vssync_vecs_length; auto.
    apply map_valid_vssync_vecs; auto.
    apply replay_disk_vssync_vecs_comm.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (flush _ _ _) _) => apply flush_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.

End MLog.

