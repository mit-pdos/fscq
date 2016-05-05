Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Hashmap.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Classes.SetoidTactics.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import WordAuto.
Require Import Cache.
Require Import Idempotent.
Require Import ListUtils.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MemLog.
Require Import DiskLogHash.
Require Import MapUtils.
Require Import ListPred.
Require Import LogReplay.
Require Import DiskSet.

Import ListNotations.

Set Implicit Arguments.



Module GLog.

  Import AddrMap LogReplay ReplaySeq LogNotations.


  (************* state and rep invariant *)

  Record mstate := mk_mstate {
    MSVMap  : valumap;
    (* collapsed updates for all committed but unflushed txns,
        necessary for fast read() operation
     *)
    MSTxns  : txnlist;
    (* list of all unflushed txns, the order should match the
       second part of diskset. (first element is the latest)
    *)

    MSMLog  : MLog.mstate;
    (* lower-level states *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate vm ts ll : memstate := 
    (mk_mstate vm ts (MLog.MSInLog ll), (MLog.MSCache ll)).

  Definition MSCache (ms : memstate) := snd ms.
  Definition MSLL (ms : memstate) := MLog.mk_memstate (MSMLog (fst ms)) (snd ms).

  Inductive state :=
  | Cached   (ds : diskset)
  | Flushing (ds : diskset) (n : addr)
  | Rollback (d : diskstate)
  | Recovering (d : diskstate)
  .

  Definition vmap_match vm ts :=
    Map.Equal vm (fold_right replay_mem vmap0 ts).

  Definition ents_valid xp d ents :=
    log_valid ents d /\ length ents <= LogLen xp.

  Definition dset_match xp ds ts :=
    Forall (ents_valid xp (fst ds)) ts /\ ReplaySeq ds ts.

  Definition rep xp st ms hm :=
  let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
  (match st with
    | Cached ds =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp ds ts ]] * exists nr,
      MLog.rep xp (MLog.Synced nr (fst ds)) mm hm
    | Flushing ds n =>
      [[ dset_match xp ds ts /\ n <= length ts ]] *
      MLog.would_recover_either xp (nthd n ds) (selR ts n nil) hm
    | Rollback d =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp (d, nil) ts ]] *
      MLog.rep xp (MLog.Rollback d) mm hm
    | Recovering d =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp (d, nil) ts ]] *
      MLog.rep xp (MLog.Recovering d) mm hm
  end)%pred.

  Definition would_recover_any xp ds hm :=
    (exists ms n, rep xp (Flushing ds n) ms hm)%pred.

  Lemma cached_recover_any: forall xp ds ms hm,
    rep xp (Cached ds) ms hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep.
    intros. norm.
    rewrite nthd_0; cancel.
    apply MLog.synced_recover_either.
    intuition. eauto.
  Qed.

  Lemma cached_recovering: forall xp ds ms hm,
    rep xp (Cached ds) ms hm =p=>
      exists n ms', rep xp (Recovering (nthd n ds)) ms' hm.
  Proof.
    unfold rep.
    intros. norm.
    rewrite nthd_0; cancel.
    rewrite MLog.rep_synced_pimpl.
    eassign (mk_mstate vmap0 nil (MSMLog ms)).
    auto.
    intuition simpl; auto.
    unfold vmap_match; simpl; congruence.
    rewrite nthd_0.
    unfold dset_match; intuition.
    apply Forall_nil.
    constructor.
  Qed.

  Lemma flushing_recover_any: forall xp n ds ms hm,
    rep xp (Flushing ds n) ms hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep; intros; cancel.
  Qed.

  Lemma rollback_recover_any: forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=> would_recover_any xp (d, nil) hm.
  Proof.
    unfold would_recover_any, rep; intros.
    norm. unfold stars; simpl.
    rewrite nthd_0; cancel.
    apply MLog.rollback_recover_either.
    intuition. eauto.
  Qed.

  Lemma rollback_recovering: forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=> rep xp (Recovering d) ms hm.
  Proof.
    unfold rep; intros.
    cancel.
    rewrite MLog.rep_rollback_pimpl.
    auto.
  Qed.

  Lemma rep_hashmap_subset : forall xp ms hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st ms hm
        =p=> rep xp st ms hm'.
  Proof.
    unfold rep; intros.
    destruct st; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.would_recover_either_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
  Qed.


  (************* program *)

  Definition read T xp a (ms : memstate) rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    match Map.find a vm with
    | Some v =>  rx ^(ms, v)
    | None =>
        let^ (mm', v) <- MLog.read xp a mm;
        rx ^(mk_memstate vm ts mm', v)
    end.

  (* Submit a committed transaction.
     It might fail if the transaction is too big to fit into the log.
     We handle the anomaly here so that flushall() can always succeed.
     This keep the interface compatible with current Log.v, in which
     only commit() can fail, and the caller can choose to abort.
  *)
  Definition submit T xp ents ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    let vm' := replay_mem ents vm in
    If (le_dec (length ents) (LogLen xp)) {
      rx ^(mk_memstate vm' (ents :: ts) mm, true)
    } else {
      rx ^(ms, false)
    }.

  Definition flushall_nomerge T xp ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    let^ (mm) <- ForN i < length ts
    Hashmap hm
    Ghost [ F ds crash ]
    Loopvar [ mm ]
    Continuation lrx
    Invariant
        exists nr,
        << F, MLog.rep: xp (MLog.Synced nr (nthd i ds)) mm hm >>
    OnCrash crash
    Begin
      (* r = false is impossible, flushall should always succeed *)
      let^ (mm, r) <- MLog.flush xp (selN ts (length ts - i - 1) nil) mm;
      lrx ^(mm)
    Rof ^(mm);
    rx (mk_memstate vmap0 nil mm).

  Definition flushall T xp ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (le_dec (Map.cardinal vm) (LogLen xp)) {
      let^ (mm, r) <- MLog.flush xp (Map.elements vm) mm;
      rx (mk_memstate vmap0 nil mm)
    } else {
      ms <- flushall_nomerge xp ms;
      rx ms
    }.

  Definition dwrite' T (xp : log_xparams) a v ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite xp a v mm;
    rx (mk_memstate vm ts mm').

  Definition dsync' T xp a ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync xp a mm;
    rx (mk_memstate vm ts mm').

  Definition dwrite T (xp : log_xparams) a v ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (MapFacts.In_dec vm a) {
      ms <- flushall xp ms;
      ms <- dwrite' xp a v ms;
      rx ms
    } else {
      ms <- dwrite' xp a v ms;
      rx ms
    }.

  Definition dsync T (xp : log_xparams) a ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (MapFacts.In_dec vm a) {
      ms <- flushall xp ms;
      ms <- dsync' xp a ms;
      rx ms
    } else {
      ms <- dsync' xp a ms;
      rx ms
    }.

  Definition dwrite_vecs' T (xp : log_xparams) avs ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite_vecs xp avs mm;
    rx (mk_memstate vm ts mm').

  Definition dsync_vecs' T xp al ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync_vecs xp al mm;
    rx (mk_memstate vm ts mm').

  Definition dwrite_vecs T (xp : log_xparams) avs ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (bool_dec (overlap (map fst avs) vm) true) {
      ms <- flushall xp ms;
      ms <- dwrite_vecs' xp avs ms;
      rx ms
    } else {
      ms <- dwrite_vecs' xp avs ms;
      rx ms
    }.

  Definition dsync_vecs T (xp : log_xparams) al ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (bool_dec (overlap al vm) true) {
      ms <- flushall xp ms;
      ms <- dsync_vecs' xp al ms;
      rx ms
    } else {
      ms <- dsync_vecs' xp al ms;
      rx ms
    }.

  Definition recover T xp cs rx : prog T :=
    mm <- MLog.recover xp cs;
    rx (mk_memstate vmap0 nil mm).

  Definition init T xp cs rx : prog T :=
    mm <- MLog.init xp cs;
    rx (mk_memstate vmap0 nil mm).


  Arguments MLog.rep: simpl never.
  Hint Extern 0 (okToUnify (MLog.rep _ _ _ _) (MLog.rep _ _ _ _)) => constructor : okToUnify.



  (************* auxilary lemmas *)

  Lemma diskset_ptsto_bound_latest : forall F xp a vs ds ts,
    dset_match xp ds ts ->
    (F * a |-> vs)%pred (list2nmem ds!!) ->
    a < length (fst ds).
  Proof.
    intros.
    apply list2nmem_ptsto_bound in H0.
    erewrite <- replay_seq_latest_length; auto.
    apply H.
  Qed.

  Lemma diskset_vmap_find_none : forall ds ts vm a v vs xp F,
    dset_match xp ds ts ->
    vmap_match vm ts ->
    Map.find a vm = None ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    selN (fst ds) a ($0, nil) = (v, vs).
  Proof.
    unfold vmap_match, dset_match.
    intros ds ts; destruct ds; revert l.
    induction ts; intuition; simpl in *;
      denote ReplaySeq as Hs;inversion Hs; subst; simpl.
    denote ptsto as Hx; rewrite singular_latest in Hx by easy; simpl in Hx.
    erewrite surjective_pairing at 1.
    erewrite <- list2nmem_sel; eauto; simpl; auto.

    rewrite H0 in H1.
    eapply IHts.
    split; eauto.
    eapply Forall_cons2; eauto.
    apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono; eauto.

    rewrite latest_cons in *.
    eapply ptsto_replay_disk_not_in'; [ | | eauto].
    eapply map_find_replay_mem_not_in; eauto.
    denote Forall as Hx; apply Forall_inv in Hx; apply Hx.
  Qed.

  Lemma replay_seq_replay_mem : forall ds ts xp,
    ReplaySeq ds ts ->
    Forall (ents_valid xp (fst ds)) ts ->
    replay_disk (Map.elements (fold_right replay_mem vmap0 ts)) (fst ds) = latest ds.
  Proof.
    induction 1; simpl in *; intuition.
    rewrite latest_cons; subst.
    unfold latest in *; simpl in *.
    rewrite <- IHReplaySeq by (eapply Forall_cons2; eauto).
    rewrite replay_disk_replay_mem; auto.
    inversion H1; subst.
    eapply log_valid_length_eq.
    unfold ents_valid in *; intuition; eauto.
    rewrite replay_disk_length; auto.
  Qed.

  Lemma diskset_vmap_find_ptsto : forall ds ts vm a w v vs F xp,
    dset_match xp ds ts ->
    vmap_match vm ts ->
    Map.find a vm = Some w ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    w = v.
  Proof.
    unfold vmap_match, dset_match; intuition.
    eapply replay_disk_eq; eauto.
    eexists; rewrite H0.
    erewrite replay_seq_replay_mem; eauto.
  Qed.

  Lemma dset_match_ext : forall ents ds ts xp,
    dset_match xp ds ts ->
    log_valid ents ds!! ->
    length ents <= LogLen xp ->
    dset_match xp (pushd (replay_disk ents ds!!) ds) (ents :: ts).
  Proof.
    unfold dset_match, pushd, ents_valid; intuition; simpl in *.
    apply Forall_cons; auto; split; auto.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_latest_length; eauto.
    constructor; auto.
  Qed.

  Lemma vmap_match_nil : vmap_match vmap0 nil.
  Proof.
      unfold vmap_match; simpl; apply MapFacts.Equal_refl.
  Qed.

  Lemma dset_match_nil : forall d xp, dset_match xp (d, nil) nil.
  Proof.
      unfold dset_match; split; [ apply Forall_nil | constructor ].
  Qed.

  Lemma dset_match_length : forall ds ts xp,
    dset_match xp ds ts -> length ts = length (snd ds).
  Proof.
    intros.
    erewrite replay_seq_length; eauto.
    apply H.
  Qed.

  Lemma dset_match_log_valid_selN : forall ds ts i n xp,
    dset_match xp ds ts ->
    log_valid (selN ts i nil) (nthd n ds).
  Proof.
    unfold dset_match, ents_valid; intuition; simpl in *.
    destruct (lt_dec i (length ts)).
    eapply Forall_selN with (i := i) in H0; intuition.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_nthd_length; eauto.
    rewrite selN_oob by omega.
    unfold log_valid, KNoDup; intuition; inversion H.
  Qed.

  Lemma dset_match_ent_length_exfalso : forall xp ds ts i,
    length (selN ts i nil) > LogLen xp ->
    dset_match xp ds ts ->
    False.
  Proof.
    unfold dset_match, ents_valid; intuition.
    destruct (lt_dec i (length ts)).
    eapply Forall_selN with (i := i) (def := nil) in H1; intuition.
    eapply le_not_gt; eauto.
    rewrite selN_oob in H; simpl in H; omega.
  Qed.


  Lemma ents_valid_length_eq : forall xp d d' ts,
    Forall (ents_valid xp d ) ts ->
    length d = length d' ->
    Forall (ents_valid xp d') ts.
  Proof.
    unfold ents_valid in *; intros.
    rewrite Forall_forall in *; intuition.
    eapply log_valid_length_eq; eauto.
    apply H; auto.
    apply H; auto.
  Qed.

  Lemma dset_match_nthd_S : forall xp ds ts n,
    dset_match xp ds ts ->
    n < length ts ->
    replay_disk (selN ts (length ts - n - 1) nil) (nthd n ds) = nthd (S n) ds.
  Proof.
    unfold dset_match; intuition.
    repeat erewrite replay_seq_nthd; eauto.
    erewrite skipn_sub_S_selN_cons; simpl; eauto.
  Qed.

  Lemma recover_before_any : forall xp ds ts hm,
    dset_match xp ds ts ->
    MLog.would_recover_before xp ds!! hm =p=>
    would_recover_any xp ds hm.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r. eassign (length (snd ds)).
    rewrite nthd_oob by auto; cancel.
    eassign (mk_mstate vmap0 ts vmap0); simpl.
    apply MLog.recover_before_either.
    intuition.
    simpl; erewrite dset_match_length; eauto; simpl; auto.
  Qed.

  Lemma recover_before_any_fst : forall xp ds ts hm,
    dset_match xp ds ts ->
    MLog.would_recover_before xp (fst ds) hm =p=>
    would_recover_any xp ds hm.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite nthd_0.
    eassign (mk_mstate vmap0 ts vmap0); simpl.
    rewrite MLog.recover_before_either.
    cancel.
    intuition.
  Qed.

  Lemma synced_recover_any : forall xp ds nr ms ts hm,
    dset_match xp ds ts ->
    MLog.rep xp (MLog.Synced nr ds!!) ms hm =p=>
    would_recover_any xp ds hm.
  Proof.
    intros.
    rewrite MLog.synced_recover_before.
    eapply recover_before_any; eauto.
  Qed.

  Lemma recover_latest_any : forall xp ds hm ts,
    dset_match xp ds ts ->
    would_recover_any xp (ds!!, nil) hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    apply dset_match_length in H0; simpl in *.
    eassign (mk_mstate vmap0 ts (MSMLog ms)).
    rewrite nthd_oob by (simpl; omega); simpl.
    rewrite nthd_oob; simpl.
    rewrite singular_latest by auto; simpl.
    rewrite length_nil with (l := (MSTxns ms)); auto.
    rewrite selR_oob by (simpl; omega).
    rewrite selR_oob; eauto.
    erewrite dset_match_length; eauto.
    simpl; auto.
    auto.
    auto.
  Qed.


  (************* correctness theorems *)

  Theorem read_ok: forall xp ms a,
    {< F ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds!! ::: exists F', (F' * a |-> vs) ]]]
    POST:hm' RET:^(ms', r)
      << F, rep: xp (Cached ds) ms' hm' >> * [[ r = fst vs ]]
    CRASH:hm'
      exists ms', << F, rep: xp (Cached ds) ms' hm' >>
    >} read xp a ms.
  Proof.
    unfold read, rep.
    prestep.
    cancel.

    (* case 1 : return from vmap *)
    step.
    eapply diskset_vmap_find_ptsto; eauto.
    pimpl_crash; cancel.

    (* case 2: read from MLog *)
    cancel.
    eexists; apply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_latest; eauto.

    step; subst.
    erewrite fst_pair; eauto.
    eapply diskset_vmap_find_none; eauto.
    pimpl_crash; cancel.
    eassign (mk_mstate (MSVMap ms_1) (MSTxns ms_1) ms'_1); cancel.
    all: auto.
  Qed.


  Theorem submit_ok: forall xp ents ms,
    {< F ds,
    PRE:hm
        << F, rep: xp (Cached ds) ms hm >> *
        [[ log_valid ents ds!! ]]
    POST:hm' RET:^(ms', r)
        ([[ r = false /\ length ents > LogLen xp ]] *
          << F, rep: xp (Cached ds) ms' hm' >>)
     \/ ([[ r = true  ]] *
          << F, rep: xp (Cached (pushd (replay_disk ents (latest ds)) ds)) ms' hm' >>)
    CRASH:hm'
      exists ms', << F, rep: xp (Cached ds) ms' hm' >>
    >} submit xp ents ms.
  Proof.
    unfold submit, rep.
    step.
    step.
    or_r; cancel.

    unfold vmap_match in *; simpl.
    denote! (Map.Equal _ _) as Heq.
    rewrite Heq; apply MapFacts.Equal_refl.
    apply dset_match_ext; auto.
    step.
    Unshelve.  exact valu. all: exact vmap0.
  Qed.



  Local Hint Resolve vmap_match_nil dset_match_nil.
  Opaque MLog.flush.

  Theorem flushall_nomerge_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >>
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall_nomerge xp ms.
  Proof.
    unfold flushall_nomerge, would_recover_any, rep.
    prestep.
    cancel.
    rewrite nthd_0; cancel.

    - safestep.
      eapply dset_match_log_valid_selN; eauto.
      safestep.

      (* flush() returns true *)
      erewrite dset_match_nthd_S by eauto; cancel.
      eexists.

      (* flush() returns false, this is impossible *)
      exfalso; eapply dset_match_ent_length_exfalso; eauto.

      (* crashes *)
      subst; repeat xcrash_rewrite.
      xform_norm; cancel.
      xform_normr. safecancel.
      eassign (mk_mstate vmap0 (MSTxns ms_1) vmap0); simpl.
      rewrite selR_inb by eauto; cancel.
      all: simpl; auto; omega.

    - safestep.
      rewrite nthd_oob by (erewrite dset_match_length; eauto).
      cancel.

    - cancel.
      xcrash_rewrite.
      (* manually construct an RHS-like pred, but replace hm'' with hm *)
      instantiate (1 := (exists raw cs, BUFCACHE.rep cs raw *
        [[ (F * exists ms n, [[ dset_match xp ds (MSTxns ms) /\ n <= length (MSTxns ms) ]] *
             MLog.would_recover_either xp (nthd n ds) (selR (MSTxns ms) n nil) hm)%pred raw ]])%pred ).
      xform_norm; cancel.
      xform_normr; safecancel.
      apply MLog.would_recover_either_hashmap_subset.
      all: eauto.

    Unshelve. all: constructor.
  Qed.


  Hint Extern 1 ({{_}} progseq (flushall_nomerge _ _) _) => apply flushall_nomerge_ok : prog.

  Opaque flushall_nomerge.

  Theorem flushall_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >>
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall xp ms.
  Proof.
    unfold flushall.
    safestep.

    prestep; denote rep as Hx; unfold rep in Hx; destruct_lift Hx.
    cancel.
    admit.
    prestep; unfold rep; safecancel.
    admit.
    denote (length _) as Hf; contradict Hf.
    setoid_rewrite <- Map.cardinal_1; omega.

    xcrash.
    unfold would_recover_any, rep.
    admit.

    step.
  Admitted.


  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (submit _ _ _) _) => apply submit_ok : prog.
  Hint Extern 1 ({{_}} progseq (flushall _ _) _) => apply flushall_ok : prog.


  Lemma forall_ents_valid_length_eq : forall xp d d' ts,
    Forall (ents_valid xp d) ts ->
    length d' = length d ->
    Forall (ents_valid xp d') ts.
  Proof.
    unfold ents_valid; intros.
    rewrite Forall_forall in *.
    intros.
    specialize (H _ H1); intuition.
    eapply log_valid_length_eq; eauto.
  Qed.

  Lemma vmap_match_notin : forall ts vm a,
    Map.find a vm = None ->
    vmap_match vm ts ->
    Forall (fun e => ~ In a (map fst e)) ts.
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    constructor; simpl in *.
    eapply map_find_replay_mem_not_in.
    rewrite <- H0; auto.

    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono.
    rewrite <- H0; auto.
  Qed.

  Lemma dset_match_dsupd_notin : forall xp ds a v ts vm,
    Map.find a vm = None ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dsupd ds a v) ts.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply length_updN.
    apply replay_seq_dsupd_notin; auto.
    eapply vmap_match_notin; eauto.
  Qed.


  Theorem dwrite'_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Map.find a (MSVMap (fst ms)) = None ]] *
      [[[ fst ds ::: (Fd * a |-> vs) ]]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached ds') ms' hm' >> *
      [[  ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
      \/ exists ms' d',
      << F, rep: xp (Cached (d', nil)) ms' hm' >> *
      [[  d' = updN (fst ds) a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge vs)) ]]]
    >} dwrite' xp a v ms.
  Proof.
    unfold dwrite', rep.
    step.
    safestep.
    3: eauto.
    cancel.
    eapply dset_match_dsupd_notin; eauto.

    (* crashes *)
    subst; repeat xcrash_rewrite.
    xform_norm.
    or_l; cancel.
    xform_normr; cancel.
    rewrite recover_before_any_fst by eauto; cancel.

    or_r; cancel.
    xform_normr; cancel.
    xform_normr; cancel.
    eassign (mk_mstate vmap0 nil x_1); simpl; cancel.
    all: simpl; eauto.
  Qed.


  Theorem dsync'_ok: forall xp a ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Map.find a (MSVMap (fst ms)) = None ]] *
      [[[ fst ds ::: (Fd * a |-> vs) ]]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached ds') ms' hm' >> *
      [[  ds' = dsupd ds a (fst vs, nil) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync' xp a ms.
  Proof.
    unfold dsync'; intros.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    unfold vssync; simpl.
    erewrite <- list2nmem_sel; eauto; eauto.
    eapply dset_match_dsupd_notin; eauto.

    (* crashes *)
    xcrash.
    rewrite MLog.synced_recover_before.
    rewrite recover_before_any_fst; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (dsync' _ _ _) _) => apply dsync'_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite' _ _ _ _) _) => apply dwrite'_ok : prog.

  Theorem dwrite_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached (dsupd ds' a (v, vsmerge vs))) ms' hm' >> *
      [[ ds' = ds \/ ds' = (ds!!, nil) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
      \/ (exists ms', 
      << F, rep: xp (Cached (updN ds!! a (v, vsmerge vs), nil)) ms' hm' >>)
      \/ (exists ms', 
      << F, rep: xp (Cached (updN (fst ds) a (v, vsmerge vs), nil)) ms' hm' >>)
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.

    erewrite fst_pair by reflexivity.
    cancel.
    eauto.
    substl (MSVMap a0); eauto.
    simpl; pred_apply; cancel.
    step.

    cancel.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.
    eapply recover_latest_any; eauto.

    or_r; or_l; cancel.
    do 2 (xform_norm; cancel).

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    prestep; unfold rep; cancel.
    apply MapFacts.not_find_in_iff; auto.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_latest; eauto.

    step.
    erewrite diskset_vmap_find_none; eauto; auto.
    apply MapFacts.not_find_in_iff; auto.
    erewrite <- diskset_vmap_find_none with (v := vs_cur); eauto; auto.
    apply MapFacts.not_find_in_iff; auto.

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    or_r; or_r; cancel.
    do 2 (xform_norm; cancel).
    erewrite diskset_vmap_find_none; eauto.
    apply MapFacts.not_find_in_iff; auto.
    auto.
    erewrite <- diskset_vmap_find_none with (v := vs_cur); eauto.
    apply MapFacts.not_find_in_iff; auto.
  Qed.

  Theorem dsync_ok: forall xp a ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached (dsupd ds' a (fst vs, nil))) ms' hm' >> *
      [[ ds' = ds \/ ds' = (ds!!, nil) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync xp a ms.
  Proof.
    unfold dsync, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.

    erewrite fst_pair by reflexivity.
    cancel.
    eauto.
    substl (MSVMap a0); eauto.
    simpl; pred_apply; cancel.
    step.

    cancel.
    repeat xcrash_rewrite; xform_norm.
    cancel; xform_normr; cancel.
    eapply recover_latest_any; eauto.

    prestep; unfold rep; cancel.
    apply MapFacts.not_find_in_iff; auto.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_latest; eauto.

    step.
    erewrite diskset_vmap_find_none; eauto; auto.
    apply MapFacts.not_find_in_iff; auto.
    denote dset_match as Hx.
    erewrite diskset_vmap_find_none in Hx; eauto.
    apply MapFacts.not_find_in_iff; auto.
  Qed.


  Lemma vmap_match_nonoverlap : forall ts vm al,
    overlap al vm = false ->
    vmap_match vm ts ->
    Forall (fun e => disjoint al (map fst e)) ts.
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    rewrite H0 in H; simpl in *.
    constructor; simpl in *.
    eapply nonoverlap_replay_mem_disjoint; eauto.
    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_nonoverlap_mono; eauto.
  Qed.

  Lemma dset_match_dsupd_vecs_nonoverlap : forall xp avl vm ds ts,
    overlap (map fst avl) vm = false ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dsupd_vecs ds avl) ts.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply vsupd_vecs_length.
    apply replay_seq_dsupd_vecs_disjoint; auto.
    eapply vmap_match_nonoverlap; eauto.
  Qed.

  Lemma dset_match_dssync_vecs_nonoverlap : forall xp al vm ds ts,
    overlap al vm = false ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dssync_vecs ds al) ts.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply vssync_vecs_length.
    apply replay_seq_dssync_vecs_disjoint; auto.
    eapply vmap_match_nonoverlap; eauto.
  Qed.

  Theorem dwrite_vecs'_ok: forall xp avl ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ overlap (map fst avl) (MSVMap (fst ms)) = false ]] *
      [[ Forall (fun e => fst e < length (fst ds)) avl ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      exists ms',
      << F, rep: xp (Cached (vsupd_vecs (fst ds) avl, nil)) ms' hm' >>
    >} dwrite_vecs' xp avl ms.
  Proof.
    unfold dwrite_vecs'.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    eapply dset_match_dsupd_vecs_nonoverlap; eauto.

    xcrash.
    or_l; xform_norm; cancel.
    xform_normr; cancel.
    rewrite recover_before_any_fst by eauto; cancel.

    or_r; xform_norm; cancel.
    xform_normr; cancel.
    eassign (mk_mstate vmap0 nil x0_1); simpl; cancel.
    all: simpl; eauto.
  Qed.

  Theorem dsync_vecs'_ok: forall xp al ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ overlap al (MSVMap (fst ms)) = false ]] *
      [[ Forall (fun e => e < length (fst ds)) al ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dssync_vecs ds al)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync_vecs' xp al ms.
  Proof.
    unfold dsync_vecs'.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    eapply dset_match_dssync_vecs_nonoverlap; eauto.

    xcrash.
    rewrite MLog.synced_recover_before.
    eapply recover_before_any_fst; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (dwrite_vecs' _ _ _) _) => apply dwrite_vecs'_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync_vecs' _ _ _) _) => apply dsync_vecs'_ok : prog.

  Theorem dwrite_vecs_ok: forall xp avl ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Forall (fun e => fst e < length (ds!!)) avl ]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached (dsupd_vecs ds' avl)) ms' hm' >> *
      [[ ds' = ds \/ ds' = (ds!!, nil) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
      \/ (exists ms', 
      << F, rep: xp (Cached (vsupd_vecs ds!! avl, nil)) ms' hm' >>)
      \/ (exists ms', 
      << F, rep: xp (Cached (vsupd_vecs (fst ds) avl, nil)) ms' hm' >>)
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.

    erewrite fst_pair by reflexivity.
    cancel.
    eauto.
    substl (MSVMap a).
    apply overlap_empty; apply map_empty_vmap0.
    eauto.
    step.

    cancel.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.
    eapply recover_latest_any; eauto.

    or_r; or_l; cancel.
    do 2 (xform_norm; cancel).

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    prestep; unfold rep; cancel.
    apply not_true_iff_false; auto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    unfold dset_match in *; intuition eauto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    or_r; or_r; cancel.
    do 2 (xform_norm; cancel).
  Qed.


  Theorem dsync_vecs_ok: forall xp al ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Forall (fun e => e < length (ds!!)) al ]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached (dssync_vecs ds' al)) ms' hm' >> *
      [[ ds' = ds \/ ds' = (ds!!, nil) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.

    erewrite fst_pair by reflexivity.
    cancel.
    eauto.
    substl (MSVMap a).
    apply overlap_empty; apply map_empty_vmap0.
    eauto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.
    cancel; xform_normr; cancel.
    eapply recover_latest_any; eauto.

    prestep; unfold rep; cancel.
    apply not_true_is_false; auto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    unfold dset_match in *; intuition eauto.
    step.
  Qed.


  Definition recover_any_pred xp ds hm :=
    ( exists d n ms, [[ n <= length (snd ds) ]] *
      (rep xp (Cached (d, nil)) ms hm \/
        rep xp (Rollback d) ms hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]])%pred.

  Theorem crash_xform_any : forall xp ds hm,
    crash_xform (would_recover_any xp ds hm) =p=>
                 recover_any_pred  xp ds hm.
  Proof.
    unfold would_recover_any, recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_either.
    unfold MLog.recover_either_pred; xform_norm.

    - norm. cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      or_l; cancel.
      eassign x0; intuition; simpl.
      erewrite <- dset_match_length; eauto.

    - destruct (Nat.eq_dec x0 (length (MSTxns x))); subst.
      norm. cancel.
      or_l; cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      auto.
      eassign (length (snd ds)); intuition; simpl.
      pred_apply.
      rewrite selR_oob by auto; simpl.
      erewrite <- dset_match_length; eauto.

      norm. cancel.
      or_l; cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      auto.
      eassign (S x0); intuition; simpl.
      erewrite <- dset_match_length by eauto; omega.
      erewrite <- dset_match_nthd_S by (eauto; omega).
      pred_apply.
      rewrite selR_inb by omega; auto.

    - norm. cancel.
      or_r; cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      auto.
      eassign x0.
      intuition.
      erewrite <- dset_match_length by eauto; omega.
  Qed.

  Lemma crash_xform_recovering : forall xp d mm hm,
    crash_xform (rep xp (Recovering d) mm hm) =p=>
                 recover_any_pred xp (d, nil) hm.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_recovering.
    instantiate (1:=nil).
    unfold MLog.recover_either_pred.
    norm.
    unfold stars; simpl.
    or_l; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    auto.
    intuition simpl; eauto.
    or_l; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    auto.
    intuition simpl; eauto.
    or_r; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    auto.
    intuition simpl; eauto.
  Qed.

  Lemma crash_xform_cached : forall xp ds ms hm,
    crash_xform (rep xp (Cached ds) ms hm) =p=>
      exists d ms', rep xp (Cached (d, nil)) ms' hm *
        [[[ d ::: (crash_xform (diskIs (list2nmem (fst ds)))) ]]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_synced; norm.
    eassign (mk_mstate vmap0 nil ms'); simpl.
    cancel.
    intuition.
  Qed.

  Lemma crash_xform_rollback : forall xp d ms hm,
    crash_xform (rep xp (Rollback d) ms hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' hm *
        [[[ d' ::: (crash_xform (diskIs (list2nmem d))) ]]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_rollback.
    cancel.
    eassign (mk_mstate vmap0 nil ms'); eauto.
    all: auto.
  Qed.


  Lemma any_pred_any : forall xp ds hm,
    recover_any_pred xp ds hm =p=>
    exists d, would_recover_any xp (d, nil) hm.
  Proof.
    unfold recover_any_pred; intros.
    xform_norm.
    rewrite cached_recover_any; cancel.
    rewrite rollback_recover_any; cancel.
  Qed.


  Lemma recover_idem : forall xp ds hm,
    crash_xform (recover_any_pred xp ds hm) =p=>
                 recover_any_pred xp ds hm.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    - rewrite MLog.crash_xform_synced.
      norm.
      eassign (mk_mstate (MSVMap x1) (MSTxns x1) ms'); cancel.
      or_l; cancel.
      replace d' with x in *.
      intuition simpl; eauto.
      apply list2nmem_inj.
      eapply crash_xform_diskIs_eq; eauto.
      intuition.
      erewrite Nat.min_l.
      eassign x0.
      eapply crash_xform_diskIs_trans; eauto.
      auto.

    - rewrite MLog.crash_xform_rollback.
      norm.
      eassign (mk_mstate (MSVMap x1) (MSTxns x1) ms'); cancel.
      or_r; cancel.
      denote (dset_match) as Hdset; inversion Hdset as (_, H').
      inversion H'.
      auto.
      intuition simpl; eauto.
      eapply crash_xform_diskIs_trans; eauto.
  Qed.


  Theorem recover_ok: forall xp cs,
    {< F raw ds,
    PRE:hm
      BUFCACHE.rep cs raw *
      [[ (F * recover_any_pred xp ds hm)%pred raw ]]
    POST:hm' RET:ms' exists raw',
      BUFCACHE.rep (MSCache ms') raw' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Cached (d, nil)) (fst ms') hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
      )%pred raw' ]]
    XCRASH:hm'
      exists raw' cs' mm', BUFCACHE.rep cs' raw' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Recovering d) mm' hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
          )%pred raw' ]]
    >} recover xp cs.
  Proof.
    unfold recover, recover_any_pred, rep.
    prestep. norm'l.
    denote or as Hx.
    apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H; cancel.

    (* Cached *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_l; cancel.
    eassign F. cancel.
    or_l; cancel.

    safestep. eauto.
    instantiate (1:=nil); cancel.

    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate vmap0 nil x1); eauto.
    intuition simpl; eauto.
    cancel.
    intuition simpl; eauto.

    (* Rollback *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_r; cancel.

    safestep. eauto.
    instantiate (1:=nil); cancel.

    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate vmap0 nil x1); eauto.
    intuition simpl; eauto.
    cancel.
    intuition simpl; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.

End GLog.

