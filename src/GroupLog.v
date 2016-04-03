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

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.



Module GLog.


  (**
    diskset, like valuset, represents a non-empty sequence of disk states.
    the fst part is the oldest disk, and the snd part is a list of subsequent disks.
    Unlike valuset, the snd list should be ordered, and a new diskstate is always
    prepended to the head of the list.
      (disk_0, dist_n :: [... ; disk 1] )
  *)

  Definition diskset  := (diskstate * list diskstate)%type.

  Definition latest (ds : diskset) := hd (fst ds) (snd ds).

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
          d = MLog.replay_disk t (hd d0 ds) ->
          ReplaySeq (d0, ds) ts -> 
          ReplaySeq (d0, (d :: ds)) (t :: ts).

  Lemma replay_seq_length : forall ds ts,
    ReplaySeq ds ts -> length (snd ds) = length ts.
  Proof.
    induction 1; simpl; firstorder.
  Qed.

  Lemma repaly_seq_latest : forall ds ts,
    ReplaySeq ds ts ->
    latest ds = fold_right MLog.replay_disk (fst ds) ts.
  Proof.
    induction 1; simpl in *; intros; firstorder.
    rewrite <- IHReplaySeq; firstorder.
  Qed.

  Lemma replay_seq_selN : forall n ds ts,
    ReplaySeq ds ts ->
    n < length (snd ds) ->
    selN (snd ds) n (fst ds) = fold_right MLog.replay_disk (fst ds) (skipn n ts).
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
    nthd n ds = fold_right MLog.replay_disk (fst ds) (skipn (length ts - n) ts).
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
    Map.Equal vm (fold_right MLog.replay_mem vmap0 ts).

  Definition ents_valid d ents :=
    KNoDup ents /\ MLog.log_valid ents d.

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
    let vm' := MLog.replay_mem ents vm in
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
  | [ |- MLog.map_valid vmap0 _ ] => apply MLog.map_valid_map0
  end; eauto.

  Hint Resolve KNoDup_map_elements.
  Hint Resolve MapProperties.eqke_equiv.


  (************* auxilary lemmas *)


  (************* correctness theorems *)


End GLog.

