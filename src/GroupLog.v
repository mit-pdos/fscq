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

  Definition diskset  := (diskstate * list diskstate)%type.

  Definition latest (ds : diskset) := hd (fst ds) (snd ds).

  Definition latest_cons : forall d0 d ds, latest (d0, d :: ds) = d.
  Proof.
    firstorder.
  Qed.

  Notation " ds '!!'" := (latest ds) (at level 1).

  (* return the n-th disk in the diskset *)
  Definition nthd n (ds : diskset) := selN (snd ds) (length (snd ds) - n) (fst ds).

  Lemma nthd_0 : forall ds, nthd 0 ds = fst ds.
  Proof.
    unfold nthd; intros; rewrite selN_oob; auto; omega.
  Qed.

  Lemma nthd_oob : forall ds n, n >= length (snd ds) -> nthd n ds = latest ds.
  Proof.
    unfold nthd, latest; intros; destruct ds; simpl in *.
    replace (length l - n) with 0 by omega.
    destruct l; firstorder.
  Qed.

  (* append a new diskstate to a diskset *)
  Definition pushd (d : diskstate) (ds : diskset) : diskset :=
      (fst ds, d :: snd ds).

  (* pop out n oldest disks for a diskset *)
  Definition popn (n : nat) (ds : diskset) : diskset :=
      (nthd n ds, cuttail n (snd ds)).

  Lemma popn_0 : forall ds,
    popn 0 ds = ds.
  Proof.
    unfold popn; intros.
    rewrite nthd_0, cuttail_0.
    rewrite surjective_pairing; auto.
  Qed.

  Lemma popn_oob : forall ds n,
    n >= length (snd ds) -> popn n ds = (ds!!, nil).
  Proof.
    unfold popn; intros.
    rewrite nthd_oob by omega.
    rewrite cuttail_oob by omega; auto.
  Qed.



  (* does the diskset contains a single element? *)
  Definition Singular (ds : diskset) := snd ds = nil.

  Lemma singular_latest : forall ds, Singular ds -> latest ds = fst ds.
  Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.

  Lemma singular_nthd : forall ds n, Singular ds -> nthd n ds = fst ds.
  Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.

  Lemma popn_oob_singular : forall ds n,
    n >= length (snd ds) -> Singular (popn n ds) .
  Proof.
    unfold popn; intros.
    rewrite cuttail_oob by omega; auto.
    constructor.
  Qed.




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

  Lemma popn_popn : forall ds m n,
    popn m (popn n ds) = popn (n + m) ds.
  Proof.
    unfold popn; intros; simpl.
    rewrite cuttail_cuttail; f_equal.
    unfold nthd; simpl.
    rewrite cuttail_length.
    destruct (le_dec n (length (snd ds))).
    replace (length (snd ds) - (n + m)) with (length (snd ds) - n - m) by omega.
    unfold cuttail.
    destruct (lt_dec (length (snd ds) - n - m) (length (snd ds) - n)).
    rewrite selN_firstn at 1; auto.
    apply selN_inb; omega.
    rewrite selN_oob.
    f_equal; omega.
    rewrite firstn_length; apply Nat.min_case_strong; omega.
    rewrite cuttail_oob by omega.
    simpl; f_equal; omega.
  Qed.

  Lemma cuttail_tail : forall A (l : list A) a n,
    cuttail (S n) (l ++ [a]) = cuttail n l.
  Proof.
    unfold cuttail; intros.
    rewrite app_length; simpl.
    replace (length l + 1 - S n) with (length l - n) by omega.
    rewrite firstn_app_l; auto; omega.
  Qed.

  Lemma popn_tail : forall n d0 d ds,
    popn (S n) (d0, ds ++ [d]) = popn n (d, ds).
  Proof.
    intros.
    replace (S n) with (1 + n) by omega.
    rewrite <- popn_popn.
    unfold popn at 2; simpl.
    rewrite cuttail_tail, cuttail_0.
    unfold nthd; simpl.
    rewrite app_length; simpl.
    rewrite selN_app2 by omega.
    replace (length ds + 1 - 1 - length ds) with 0 by omega; simpl; auto.
  Qed.



  Lemma replay_seq_popn_cuttail : forall ds ts n,
    ReplaySeq ds ts ->
    ReplaySeq (popn n ds) (cuttail n ts).
  Proof.
    intros ds ts; destruct ds; revert ts l d.
    induction ts using rev_ind; induction l using rev_ind; simpl; intros.
    rewrite popn_oob, cuttail_oob by (simpl; omega); auto.
    inversion H; subst.
    exfalso; eapply app_cons_not_nil; eauto.
    inversion H; subst.
    exfalso; eapply app_cons_not_nil; eauto.

    destruct n.
    rewrite popn_0, cuttail_0; auto.
    rewrite cuttail_tail.
    rewrite popn_tail.
    apply IHts.

  Admitted.




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
  | Flushing (ds : diskset)
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
    | Flushing ds =>
      [[ dset_match xp ds ts ]] *
      MLog.would_recover_either xp F (fst ds) (last ts nil)
  end)%pred.



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
        MLog.rep xp F (MLog.Synced nr (nthd i ds)) mm *
        [[ dset_match xp (popn i ds) (cuttail i ts) ]]
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
    let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
    mm' <- MLog.dsync xp a mm;
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


  Lemma dset_match_popn_cuttail : forall xp n ds ts,
    dset_match xp ds ts ->
    dset_match xp (popn n ds) (cuttail n ts).
  Proof.
    unfold dset_match; intros; intuition.
    apply forall_firstn.
    eapply ents_valid_length_eq; eauto; simpl.
    erewrite replay_seq_nthd_length; eauto.
    apply replay_seq_popn_cuttail; auto.
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
    instantiate (ms'0 := mk_memstate (MSVMap ms) (MSTxns ms) ms').
    cancel.
    intuition.
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
      rep xp F (Cached (ds!!, nil)) ms'
    CRASH exists ms' n,
      rep xp F (Flushing (popn n ds)) ms'
    >} flushall xp ms.
  Proof.
    unfold flushall, rep.
    prestep.
    cancel.
    rewrite nthd_0; cancel.
    rewrite popn_0, cuttail_0; auto.

    - safestep.
      eapply dset_match_log_valid_selN; eauto.
      prestep; norm.

      (* flush() returns true *)
      erewrite dset_match_nthd_S by eauto; cancel.
      intuition.
      apply dset_match_popn_cuttail; eauto.

      (* flush() returns false, this is impossible *)
      exfalso; eapply dset_match_ent_length_exfalso; eauto.
      exfalso; eapply dset_match_ent_length_exfalso; eauto.

      (* crashes *)
      subst; pimpl_crash. norm.
      instantiate (ms' := mk_memstate vmap0 (cuttail m (MSTxns ms)) a).
      simpl; rewrite last_cuttail_selN by auto; cancel.
      simpl; intuition; eauto.

    - prestep; norm.
      rewrite nthd_oob by (erewrite dset_match_length; eauto).
      cancel. intuition.
    - pimpl_crash; cancel.
      rewrite popn_0; eauto.

    Unshelve. all: easy.
  Qed.



  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (submit _ _ _) _) => apply submit_ok : prog.
  Hint Extern 1 ({{_}} progseq (flushall _ _) _) => apply flushall_ok : prog.



End GLog.

