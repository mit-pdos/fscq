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
  Definition pushd (d : diskstate) (ds : diskset) := (fst ds, d :: snd ds).

  (* pop out n oldest disks for a diskset *)
  Definition popn (n : nat) (ds : diskset) := (nthd n ds, cuttail n (snd ds)).



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

  (* list of transactions *)
  Definition txnlist  := list DLog.contents.

  (** RelapySeq: any prefix of a diskset is the result of replaying 
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
  | Flushing (ds : diskset)
  .

  Definition vmap_match vm ts :=
    Map.Equal vm (fold_right replay_mem vmap0 ts).

  Definition ents_valid d ents :=
    log_valid ents d.

  Definition dset_match ds ts :=
    Forall (ents_valid (fst ds)) ts /\ ReplaySeq ds ts.

  Definition rep xp F st ms :=
  let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
  (exists nr,
  match st with
    | Cached ds =>
      [[ vmap_match vm ts ]] *
      [[ dset_match ds ts ]] *
      MLog.rep xp F nr (MLog.Synced (fst ds)) mm
    | Flushing ds =>
      [[ dset_match ds ts ]] *
      ( MLog.rep xp F nr (MLog.Applying (fst ds)) mm \/
        MLog.rep xp F nr (MLog.Flushing (fst ds) (last ts nil)) mm)
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
    let^ (mm') <- ForN i < length ts
    Ghost [ F crash ]
    Loopvar [ tt ]
    Continuation lrx
    Invariant F
    OnCrash crash
    Begin
      let^ (mm, r) <- MLog.flush xp (selN ts (length ts - i - 1) nil) mm;
      If (bool_dec r true) {
        lrx ^(mm)
      } else {
        rx ms  (* impossible case, flushall should always succeed *)
      }
    Rof ^(mm);
    rx (mk_memstate vmap0 nil mm').

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


  (* destruct memstate *)
  Ltac dems := eauto; repeat match goal with
  | [ H : @eq memstate ?ms (mk_memstate _ _ _) |- _ ] =>
     is_var ms; destruct ms; inversion H; subst; simpl
  | [ |- Map.Empty vmap0 ] => apply Map.empty_1
  | [ |- map_valid vmap0 _ ] => apply map_valid_map0
  end; eauto.


  (************* auxilary lemmas *)

  Lemma diskset_ptsto_bound_latest : forall F a vs ds ts,
    dset_match ds ts ->
    (F * a |-> vs)%pred (list2nmem ds!!) ->
    a < length (fst ds).
  Proof.
    intros.
    apply list2nmem_ptsto_bound in H0.
    erewrite <- replay_seq_latest_length; auto.
    apply H.
  Qed.

  Lemma diskset_vmap_find_none : forall ds ts vm a v vs F,
    dset_match ds ts ->
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


  Lemma replay_seq_replay_mem : forall ds ts,
    ReplaySeq ds ts ->
    Forall (ents_valid (fst ds)) ts ->
    replay_disk (Map.elements (fold_right replay_mem vmap0 ts)) (fst ds) = latest ds.
  Proof.
    induction 1; simpl in *; intuition.
    rewrite latest_cons; subst.
    unfold latest in *; simpl in *.
    rewrite <- IHReplaySeq by (eapply Forall_cons2; eauto).
    rewrite replay_disk_replay_mem; auto.
    inversion H1; subst.
    eapply log_valid_length_eq; eauto.
    rewrite replay_disk_length; auto.
  Qed.

  Lemma diskset_vmap_find_ptsto : forall ds ts vm a w v vs F,
    dset_match ds ts ->
    vmap_match vm ts ->
    Map.find a vm = Some w ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    w = v.
  Proof.
    unfold vmap_match, dset_match; intuition.
    eapply replay_disk_eq; eauto.
    eexists; rewrite H0.
    rewrite replay_seq_replay_mem; eauto.
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




End GLog.

