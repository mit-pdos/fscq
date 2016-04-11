Require Import Arith.
Require Import Bool.
Require Import List.
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
Require Import DiskLog.
Require Import MapUtils.
Require Import ListPred.
Require Import LogReplay.
Require Import NEList.

Import ListNotations.

Set Implicit Arguments.



Module GLog.

  Import AddrMap LogReplay.


  (**
    diskset, like valuset, represents a non-empty sequence of disk states.
    the fst part is the oldest disk, and the snd part is a list of subsequent disks.
    Unlike valuset, the snd list should be ordered, and a new diskstate is always
    prepended to the head of the list.
      (disk_0, dist_n :: [... ; disk 1] )
  *)

  Definition diskset  := nelist diskstate.

  (* list of transactions *)
  Definition txnlist  := list DLog.contents.

  (** ReplaySeq: any prefix of a diskset is the result of replaying 
   *  the corresponding prefix of transactions
   *)
  Inductive ReplaySeq : diskset -> txnlist -> Prop :=
    | RSeqNil  : forall d0, ReplaySeq (d0, nil) nil
    | RSeqCons : forall d0 d t ds ts,
          d = replay_disk t (hd d0 ds) ->
          ReplaySeq (d0, ds) ts -> 
          ReplaySeq (d0, (d :: ds)) (t :: ts).

  Lemma replay_seq_length : forall ds ts,
    ReplaySeq ds ts -> length (snd ds) = length ts.
  Proof.
    induction 1; simpl; firstorder.
  Qed.

  Lemma repaly_seq_latest : forall ds ts,
    ReplaySeq ds ts ->
    latest ds = fold_right replay_disk (fst ds) ts.
  Proof.
    induction 1; simpl in *; intros; firstorder.
    rewrite <- IHReplaySeq; firstorder.
  Qed.

  Lemma replay_seq_selN : forall n ds ts,
    ReplaySeq ds ts ->
    n < length (snd ds) ->
    selN (snd ds) n (fst ds) = fold_right replay_disk (fst ds) (skipn n ts).
  Proof.
    induction n; simpl; intros; auto.
    destruct ds.
    apply repaly_seq_latest in H; rewrite <- H.
    destruct l; intuition.
    pose proof (replay_seq_length H).
    inversion H; auto; subst; simpl in *.
    specialize (IHn (d0, ds0)).
    apply IHn; simpl; auto; omega.
  Qed.

  Lemma replay_seq_nthd : forall n ds ts,
    ReplaySeq ds ts ->
    nthd n ds = fold_right replay_disk (fst ds) (skipn (length ts - n) ts).
  Proof.
    unfold nthd; intros.
    destruct n; simpl.
    rewrite selN_oob, skipn_oob by omega; auto.
    erewrite <- replay_seq_length by eauto.
    destruct (lt_dec (length (snd ds)) (S n)).
    replace (length (snd ds) - S n) with 0 by omega; simpl.
    rewrite <- repaly_seq_latest by auto.
    unfold latest; destruct ds; simpl.
    destruct l0; firstorder.
    apply replay_seq_selN; auto; omega.
  Qed.

  Lemma fold_right_replay_disk_length : forall l d,
    length (fold_right replay_disk d l) = length d.
  Proof.
    induction l; simpl; auto; intros.
    rewrite replay_disk_length; auto.
  Qed.

  Lemma replay_seq_latest_length : forall ds ts,
    ReplaySeq ds ts ->
    length (latest ds) = length (fst ds).
  Proof.
    intros.
    erewrite repaly_seq_latest; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.

  Lemma replay_seq_nthd_length : forall ds ts n,
    ReplaySeq ds ts ->
    length (nthd n ds) = length (fst ds).
  Proof.
    intros.
    erewrite replay_seq_nthd; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.



  (************* state and rep invariant *)

  Record memstate := mk_memstate {
    MSVMap  : valumap;
    (* collapsed updates for all committed but unflushed txns,
        necessary for fast read() operation
     *)
    MSTxns  : txnlist;
    (* list of all unflushed txns, the order should match the
       second part of diskset. (first element is the latest)
    *)
    MSMLog  : MLog.memstate
    (* lower-level state *)
  }.

  Inductive state :=
  | Cached   (ds : diskset)
  | Flushing (ds : diskset) (n : addr)
  .

  Definition vmap_match vm ts :=
    Map.Equal vm (fold_right replay_mem vmap0 ts).

  Definition ents_valid xp d ents :=
    log_valid ents d /\ length ents <= LogLen xp.

  Definition dset_match xp ds ts :=
    Forall (ents_valid xp (fst ds)) ts /\ ReplaySeq ds ts.

  Definition rep xp F st ms :=
  let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
  (match st with
    | Cached ds =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp ds ts ]] * exists nr,
      MLog.rep xp F (MLog.Synced nr (fst ds)) mm
    | Flushing ds n =>
      [[ dset_match xp ds ts /\ n <= length ts ]] *
      MLog.would_recover_either xp F (nthd n ds) (selR ts n nil)
  end)%pred.

  Definition would_recover_any xp F n ds :=
    (exists ms, rep xp F (Flushing ds n) ms)%pred.

  Definition recover_any_pred xp F n ds ms :=
    crash_xform (rep xp F (Flushing ds n) ms).

  Lemma cached_recover_any: forall xp F ds ms,
    rep xp F (Cached ds) ms =p=> would_recover_any xp F 0 ds.
  Proof.
    unfold would_recover_any, rep.
    intros; cancel.
    rewrite nthd_0.
    apply MLog.synced_recover_either.
    eauto.
  Qed.

  Lemma flushing_recover_any: forall xp F n ds ms,
    rep xp F (Flushing ds n) ms =p=> would_recover_any xp F n ds.
  Proof.
    unfold would_recover_any, rep; intros; cancel.
  Qed.


  (************* program *)

  Definition read T xp a ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
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
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    let vm' := replay_mem ents vm in
    If (le_dec (length ents) (LogLen xp)) {
      rx ^(mk_memstate vm' (ents :: ts) mm, true)
    } else {
      rx ^(ms, false)
    }.

  Definition flushall T xp ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    let^ (mm) <- ForN i < length ts
    Ghost [ F ds crash ]
    Loopvar [ mm ]
    Continuation lrx
    Invariant
        exists nr,
        MLog.rep xp F (MLog.Synced nr (nthd i ds)) mm
    OnCrash crash
    Begin
      (* r = false is impossible, flushall should always succeed *)
      let^ (mm, r) <- MLog.flush xp (selN ts (length ts - i - 1) nil) mm;
      lrx ^(mm)
    Rof ^(mm);
    rx (mk_memstate vmap0 nil mm).

  Definition dwrite T (xp : log_xparams) a v ms rx : prog T :=
    ms <- flushall xp ms;
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    mm' <- MLog.dwrite xp a v mm;
    rx (mk_memstate vm ts mm').

  Definition dsync T xp a ms rx : prog T :=
    ms <- flushall xp ms;
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    mm' <- MLog.dsync xp a mm;
    rx (mk_memstate vm ts mm').

  Definition read_raw T a ms rx : prog T :=
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    let^ (mm', r) <- MLog.read_raw a mm;
    rx ^(mk_memstate vm ts mm', r).

  Definition dwrite_vecs T (xp : log_xparams) avs ms rx : prog T :=
    ms <- flushall xp ms;
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    mm' <- MLog.dwrite_vecs xp avs mm;
    rx (mk_memstate vm ts mm').

  Definition dsync_vecs T xp al ms rx : prog T :=
    ms <- flushall xp ms;
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    mm' <- MLog.dsync_vecs xp al mm;
    rx (mk_memstate vm ts mm').

  Definition recover T xp cs rx : prog T :=
    mm <- MLog.recover xp cs;
    rx (mk_memstate vmap0 nil mm).


  Arguments MLog.rep: simpl never.
  Hint Extern 0 (okToUnify (MLog.rep _ _ _ _ _) (MLog.rep _ _ _ _ _)) => constructor : okToUnify.



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
    fst (selN (fst ds) a ($0, nil)) = v.
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


  Lemma skipn_sub_S_selN_cons : forall A (l : list A) n def,
    n < length l ->
    skipn (length l - S n) l = selN l (length l - n - 1) def :: (skipn (length l - n) l).
  Proof.
    intros.
    replace (length l - n) with (S (length l - n - 1)) at 2 by omega.
    rewrite <- skipn_selN_skipn by omega.
    f_equal; omega.
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

  Lemma recover_before_any : forall xp F ds ts,
    dset_match xp ds ts ->
    MLog.would_recover_before xp F ds!! =p=>
    would_recover_any xp F (length (snd ds)) ds.
  Proof. 
    unfold would_recover_any, rep; cancel.
    rewrite nthd_oob by auto.
    apply MLog.recover_before_either.
    eassign (mk_memstate vmap0 ts (MLog.mk_memstate vmap0 (BUFCACHE.cache0 0))); simpl.
    intuition.
    simpl; erewrite dset_match_length; eauto; simpl; auto.
  Qed.

  Lemma synced_recover_any : forall xp F ds nr ms ts,
    dset_match xp ds ts ->
    MLog.rep xp F (MLog.Synced nr ds!!) ms =p=>
    would_recover_any xp F (length (snd ds)) ds.
  Proof.
    intros.
    rewrite MLog.synced_recover_before.
    eapply recover_before_any; eauto.
  Qed.

  Lemma nthd_cons_inb : forall T d0 ds (d : T) n,
    n <= length ds ->
    nthd n (d0, d :: ds) = nthd n (d0, ds).
  Proof.
    unfold nthd; intuition; simpl.
    destruct n.
    rewrite Nat.sub_0_r; auto.
    destruct (length ds - n) eqn:?.
    omega.
    replace (length ds - S n) with n0 by omega; auto.
  Qed.


  (************* correctness theorems *)

  Theorem read_ok: forall xp ms a,
    {< F ds vs,
    PRE
      rep xp F (Cached ds) ms *
      [[[ ds!! ::: exists F', (F' * a |-> vs) ]]]
    POST RET:^(ms', r)
      rep xp F (Cached ds) ms' * [[ r = fst vs ]]
    CRASH
      exists ms', rep xp F (Cached ds) ms'
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
    eapply diskset_vmap_find_none; eauto.
    pimpl_crash; norm.
    eassign (mk_memstate (MSVMap ms) (MSTxns ms) ms').
    cancel.
    intuition.
  Qed.


  Theorem read_raw_ok: forall xp ms a,
    {< F d vs,
    PRE
      rep xp (F * a |-> vs) (Cached d) ms
    POST RET:^(ms', r)
      rep xp (F * a |-> vs) (Cached d) ms' * [[ r = fst vs ]]
    CRASH
      exists ms', rep xp (F * a |-> vs) (Cached d) ms'
    >} read_raw a ms.
  Proof.
    unfold read_raw, rep.
    safestep.
    step.
    pimpl_crash; norml; cancel.
    eassign (mk_memstate (MSVMap ms) (MSTxns ms) ms').
    cancel.
    all: eauto.
  Qed.


  Theorem submit_ok: forall xp ents ms,
    {< F ds,
    PRE
      rep xp F (Cached ds) ms *
      [[ log_valid ents ds!! ]]
    POST RET:^(ms', r)
      [[ r = false ]] * 
        rep xp F (Cached ds) ms' * [[ length ents > LogLen xp ]]
      \/
      [[ r = true  ]] *
        rep xp F (Cached (pushd (replay_disk ents (latest ds)) ds)) ms'
    CRASH
      exists ms', rep xp F (Cached ds) ms'
    >} submit xp ents ms.
  Proof.
    unfold submit, rep.
    step.
    step.
    or_r; cancel.

    unfold vmap_match in *; simpl.
    rewrite H; apply MapFacts.Equal_refl.
    apply dset_match_ext; auto.
    step.
  Qed.



  Local Hint Resolve vmap_match_nil dset_match_nil.

  Theorem flushall_ok: forall xp ms,
    {< F ds,
    PRE
      rep xp F (Cached ds) ms
    POST RET:ms'
      rep xp F (Cached (ds!!, nil)) ms' *
      [[ MSTxns ms' = nil /\ MSVMap ms' = vmap0 ]]
    CRASH exists n,
      would_recover_any xp F n ds
    >} flushall xp ms.
  Proof.
    unfold flushall, would_recover_any, rep.
    prestep.
    cancel.
    rewrite nthd_0; cancel.

    - safestep.
      eapply dset_match_log_valid_selN; eauto.
      prestep; norm.

      (* flush() returns true *)
      erewrite dset_match_nthd_S by eauto; cancel.
      intuition.

      (* flush() returns false, this is impossible *)
      exfalso; eapply dset_match_ent_length_exfalso; eauto.
      exfalso; eapply dset_match_ent_length_exfalso; eauto.

      (* crashes *)
      subst; pimpl_crash. norm.
      rewrite selR_inb by eauto; cancel.
      simpl; intuition; eauto.

    - prestep; norm.
      rewrite nthd_oob by (erewrite dset_match_length; eauto).
      cancel. intuition.
    - pimpl_crash. norm. cancel.
      intuition; eauto.

    Unshelve. all: easy.
  Qed.



  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (read_raw _ _) _) => apply read_raw_ok : prog.
  Hint Extern 1 ({{_}} progseq (submit _ _ _) _) => apply submit_ok : prog.
  Hint Extern 1 ({{_}} progseq (flushall _ _) _) => apply flushall_ok : prog.


  Theorem dwrite_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE
      rep xp F (Cached ds) ms *
      [[[ ds!! ::: (Fd * a |-> vs) ]]]
    POST RET:ms' exists d',
      rep xp F (Cached (d', nil)) ms' *
      [[  d' = updN ds!! a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    CRASH
      (exists n, would_recover_any xp F n ds)
      \/ exists ms' d',
      rep xp F (Cached (d', nil)) ms' *
      [[  d' = updN ds!! a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite, rep.
    step.
    unfold rep; cancel.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    subst; substl (MSTxns r_); eauto.

    (* crashes *)
    cancel.
    or_l.
    rewrite recover_before_any by eauto; cancel.
    unfold rep; or_r; cancel.
    eassign (mk_memstate vmap0 nil a0); simpl; cancel.
    all: simpl; eauto.
    cancel; or_l; cancel.
  Qed.


  Theorem dsync_ok: forall xp a ms,
    {< F Fd ds vs,
    PRE
      rep xp F (Cached ds) ms *
      [[[ ds!! ::: (Fd * a |-> vs) ]]]
    POST RET:ms' exists d',
      rep xp F (Cached (d', nil)) ms' *
      [[[ d' ::: (Fd * a |-> (fst vs, nil)) ]]] *
      [[  d' = vssync ds!! a ]]
    CRASH
      (exists n, would_recover_any xp F n ds) \/
      exists ms' d',
      rep xp F (Cached (d', nil))  ms' *
      [[[ d' ::: (Fd * a |-> (fst vs, nil)) ]]] *
      [[ d' = vssync ds!! a ]]
    >} dsync xp a ms.
  Proof.
    unfold dsync.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    subst; substl (MSTxns r_); eauto.

    (* crashes *)
    cancel.
    or_l.
    rewrite synced_recover_any by eauto; cancel.
    unfold rep; or_r; cancel.
    eassign (mk_memstate vmap0 nil ms'); simpl; cancel.
    all: simpl; eauto.
    cancel; or_l; cancel.
  Qed.


  Theorem dwrite_vecs_ok: forall xp avl ms,
    {< F ds,
    PRE
      rep xp F (Cached ds) ms *
      [[ Forall (fun e => fst e < length ds!!) avl ]]
    POST RET:ms'
      rep xp F (Cached (vsupd_vecs ds!! avl, nil)) ms'
    XCRASH
      (exists n, would_recover_any xp F n ds) \/
      exists ms', 
      rep xp F (Cached (vsupd_vecs ds!! avl, nil)) ms'
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    subst; substl (MSTxns r_); eauto.

    subst; apply H1; rewrite H3.
    xform_norm.
    or_l; rewrite recover_before_any by eauto.
    xform_norm; cancel.
    or_r; unfold rep; xform_norm; cancel.
    xform_norm.
    eassign (mk_memstate vmap0 nil x); simpl.
    xform_normr; eauto.
    all: simpl; auto.

    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    or_l; cancel.
  Qed.


  Theorem dsync_vecs_ok: forall xp al ms,
    {< F ds,
    PRE
      rep xp F (Cached ds) ms *
      [[ Forall (fun e => e < length ds!!) al ]]
    POST RET:ms'
      rep xp F (Cached (vssync_vecs ds!! al, nil)) ms'
    XCRASH
      exists n, would_recover_any xp F n ds
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    subst; substl (MSTxns r_); eauto.

    subst; apply H1; rewrite H3.
    xform_norm.
    rewrite synced_recover_any by eauto; cancel.
  Qed.


(*
  Definition recover_any_pred xp cs F ds :=
    (exists n, [[ n < length (snd ds) ]] *
    (MLog.recover_either_pred xp cs F
      (diskIs (list2nmem (nthd n ds)))
      (diskIs (list2nmem (nthd (S n) ds)))))%pred.
*)

  Theorem recover_ok: forall xp cs F,
    {< ds n,
    PRE
      recover_any_pred xp F n ds (mk_memstate vmap0 nil (MLog.mk_memstate vmap0 cs))
    POST RET:ms' exists d n, [[ n <= length (snd ds) ]] *
      rep xp F (Cached (d, nil)) ms' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    CRASH
      recover_any_pred xp F n ds (mk_memstate vmap0 nil (MLog.mk_memstate vmap0 cs))
    >} recover xp cs.
  Proof.
    unfold recover, recover_any_pred, rep.
    step.
    prestep. norm. cancel.
  Admitted.


(*
  Theorem cached_recover_any_pred : forall xp ds ms (F FD : pred),
    FD (list2nmem (fst ds)) ->
    crash_xform (rep xp F (Cached ds) ms) =p=>
    exists cs, recover_any_pred xp cs (crash_xform F) FD FD.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.synced_either_pred; eauto.
    cancel.
    exists (l, nil); exists 0; intros; intuition.
  Qed.


  Theorem would_recover_any_any_pred : forall xp ds n (F FD1 FD2 : pred),
    FD1 (list2nmem (nthd n ds)) ->
    FD2 (list2nmem (nthd (S n) ds)) ->
    crash_xform (would_recover_any xp F n ds) =p=>
    exists cs, recover_any_pred xp cs (crash_xform F) FD1 FD2.
  Proof.
    unfold would_recover_any, recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.would_recover_either_either_pred.
    cancel.
    exists ds; exists n; intros; intuition.
    eauto.
    destruct (Nat.eq_dec n (length (MSTxns x))); subst.
    rewrite selR_oob; simpl; auto.
    rewrite nthd_oob in H0. rewrite nthd_oob; auto.
    erewrite dset_match_length; eauto.
    erewrite dset_match_length; eauto.
    erewrite <- dset_match_nthd_S in H0 by (eauto; omega).
    rewrite selR_inb; auto; omega.
  Qed.


  Theorem recover_idem : forall xp cs F Fold Fnew,
    crash_xform (recover_any_pred xp cs F Fold Fnew) =p=>
      exists cs', recover_any_pred xp cs' (crash_xform F) Fold Fnew.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.recover_idem; cancel.
    do 2 eexists; eauto.
  Qed.
*)

  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.

End GLog.

