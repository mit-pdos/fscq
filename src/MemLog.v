Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapList.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Log.
Require Import Pred.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import GenSep.

(* XXX parameterize by length and stick in Word.v *)
Module Addr_as_OT <: UsualOrderedType.
  Definition t := addr.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := @wlt addrlen.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    apply wlt_lt in H; apply wlt_lt in H0.
    apply lt_wlt.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros.
    apply wlt_lt in H.
    intro He; subst; omega.
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    unfold lt, eq.
    destruct (wlt_dec x y); [ apply LT; auto | ].
    destruct (weq x y); [ apply EQ; auto | ].
    apply GT. apply le_neq_lt; auto.
  Defined.

  Definition eq_dec := @weq addrlen.
End Addr_as_OT.

Module Map := FMapList.Make(Addr_as_OT).

Import ListNotations.
Set Implicit Arguments.

Definition memstate := Map.t valu.
Definition ms_empty := Map.empty valu.

Definition diskstate := list valu.

Inductive logstate :=
| NoTransaction (cur : diskstate)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old : diskstate) (cur : diskstate)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| FlushedTxn (old : diskstate) (cur : diskstate)
(* A transaction has been flushed to the log, but not committed yet. *)
| CommittedTxn (cur : diskstate)
(* A transaction has committed but the log has not been applied yet. *).

Record xparams := {
  (* The actual data region is everything that's not described here *)
  LogHeader : addr; (* Store the header here *)
  LogCommit : addr; (* Store true to apply after crash. *)

  LogStart : addr; (* Start of log region on disk *)
  LogLen : addr  (* Maximum number of entries in log; length but still use addr type *)
}.


Module MEMLOG.

  Definition header_type := Rec.RecF ([("length", Rec.WordF addrlen)]).
  Definition header := Rec.data header_type.
  Definition mk_header (len : nat) : header := ($ len, tt).

  Theorem header_sz_ok : Rec.len header_type <= valulen.
  Proof.
    rewrite valulen_is. simpl. firstorder. (* this could be much faster, say with reflection *)
  Qed.

  Theorem plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
  Proof.
    apply le_plus_minus_r; apply header_sz_ok.
  Qed.

  Definition header_to_valu (h : header) : valu.
    set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
    rewrite plus_minus_header in r.
    refine r.
  Defined.
  Arguments header_to_valu : simpl never.

  Definition valu_to_header (v : valu) : header.
    apply Rec.of_word.
    rewrite <- plus_minus_header in v.
    refine (split1 _ _ v).
  Defined.

  Definition header_valu_id : forall h,
    valu_to_header (header_to_valu h) = h.
  Proof.
    unfold valu_to_header, header_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- plus_minus_header.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    unfold zext.
    rewrite split1_combine.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.

  Definition addr_per_block := valulen / addrlen.
  Definition descriptor_type := Rec.ArrayF (Rec.WordF addrlen) addr_per_block.
  Definition descriptor := Rec.data descriptor_type.
  Theorem descriptor_sz_ok : valulen = Rec.len descriptor_type.
    simpl. unfold addr_per_block. rewrite valulen_is. reflexivity.
  Qed.

  Definition descriptor_to_valu (d : descriptor) : valu.
    rewrite descriptor_sz_ok.
    apply Rec.to_word; auto.
  Defined.
  Arguments descriptor_to_valu : simpl never.

  Definition valu_to_descriptor (v : valu) : descriptor.
    rewrite descriptor_sz_ok in v.
    apply Rec.of_word; auto.
  Defined.

  Theorem valu_descriptor_id : forall v,
    descriptor_to_valu (valu_to_descriptor v) = v.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Rec.to_of_id.
    rewrite <- descriptor_sz_ok.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    trivial.
  Defined.

  Definition indomain' (a : addr) (m : diskstate) := wordToNat a < length m.

  (* Check that the state is well-formed *)
  Definition valid_entries m (ms : memstate) :=
    forall a v, Map.MapsTo a v ms -> indomain' a m.

  Definition valid_size xp (ms : memstate) :=
    Map.cardinal ms <= wordToNat (LogLen xp).

  (* Replay the state in memory *)
  Fixpoint replay (ms : memstate) (m : diskstate) : diskstate :=
    Map.fold (fun a v m' => upd m' a v) ms m.

  (** On-disk representation of the log *)
  Definition log_rep xp m (ms : memstate) : pred :=
     ((LogHeader xp) |-> header_to_valu (mk_header (Map.cardinal ms)) *
      [[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      (* For now, support just one descriptor block, at the start of the log. *)
      [[ Map.cardinal ms <= addr_per_block ]] *
      exists rest, (LogStart xp) |-> descriptor_to_valu (map fst (Map.elements ms) ++ rest) *
      array (LogStart xp ^+ $1) (map snd (Map.elements ms)) $1 *
      (* XXX use array for this too (with an exis)? *)
      LOG.avail_region (LogStart xp ^+ $1 ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms))%pred.

  Definition data_rep (old : diskstate) : pred :=
    diskIs (list2mem old).

  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred valu :=
    [[ cur = replay ms old ]]%pred.

  Definition rep xp (st: logstate) (ms: memstate) :=
    match st with
    | NoTransaction m =>
      (LogCommit xp) |-> $0
    * [[ ms = ms_empty ]]
    * data_rep m
    * (LogHeader xp) |->?
    * LOG.avail_region (LogStart xp) (wordToNat (LogLen xp) + 1)
    | ActiveTxn old cur =>
      (LogCommit xp) |-> $0
    * data_rep old (* Transactions are always completely buffered in memory. *)
    * log_rep xp old ms_empty
    * cur_rep old ms cur
    * [[ valid_entries old ms ]]
    | FlushedTxn old cur =>
      (LogCommit xp) |-> $0
    * [[ ms = ms_empty ]]
    * data_rep old
    * exists log, log_rep xp old log
    * cur_rep old log cur
    | CommittedTxn cur =>
      (LogCommit xp) |-> $1
    * [[ ms = ms_empty ]]
    * exists old, data_rep old
    * exists log, log_rep xp old log
    * cur_rep old log cur
    end%pred.

  Definition init T xp rx : prog T :=
    Write (LogCommit xp) $0 ;;
    rx tt.

  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _) (data_rep _)) => constructor : okToUnify.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep, Map.cardinal.

  Theorem init_ok : forall xp,
    {< old,
    PRE    data_rep old *
           LOG.avail_region (LogStart xp) (1 + wordToNat (LogLen xp)) *
           (LogCommit xp) |->? *
           (LogHeader xp) |->?
    POST:r rep xp (NoTransaction old) ms_empty
    CRASH  any
    >} init xp.
  Proof.
    unfold init; log_unfold.
    intros.
    hoare; try apply pimpl_any.

    instantiate (a := valu_to_descriptor w1).
    rewrite valu_descriptor_id.
    cancel.

    constructor.

    unfold valid_size. log_unfold. simpl. omega.
  Qed.

  Definition begin T xp rx : prog T :=
    Write (LogHeader xp) (header_to_valu (mk_header 0)) ;;
    rx ms_empty.

  Theorem begin_ok: forall xp,
    {< m,
    PRE    rep xp (NoTransaction m) ms_empty
    POST:r rep xp (ActiveTxn m m) r
    CRASH  rep xp (NoTransaction m) ms_empty \/ rep xp (ActiveTxn m m) ms_empty
    >} begin xp.
  Proof.
    unfold begin; log_unfold.
    hoare.
  Qed.

  Definition abort T xp (ms:memstate) rx : prog T :=
    Write (LogHeader xp) (header_to_valu (mk_header 0)) ;;
    rx tt.

  Theorem abort_ok : forall xp ms,
    {< m1 m2,
    PRE    rep xp (ActiveTxn m1 m2) ms
    POST:r rep xp (NoTransaction m1) ms_empty
    CRASH  rep xp (ActiveTxn m1 m2) ms \/ rep xp (NoTransaction m1) ms_empty
    >} abort xp ms.
  Proof.
    unfold abort; log_unfold.
    hoare.
  Qed.
  Lemma replay_add : forall a v ms m,
    replay (Map.add a v ms) m = Prog.upd (replay ms m) a v.
  Proof.
    intros.
    apply functional_extensionality.
    admit.
  Qed.

  Definition write T (xp : xparams) (ms : memstate) a v rx : prog T :=
    rx (Map.add a v ms).

  Theorem write_ok : forall xp ms a v,
    {< m1 m2 F' v0,
    PRE      rep xp (ActiveTxn m1 m2) ms * [[ (a |-> v0 * F')%pred m2 ]]
    POST:ms' exists m', rep xp (ActiveTxn m1 m') ms' *
             [[(a |-> v * F')%pred m' ]]
    CRASH    exists m' ms', rep xp (ActiveTxn m1 m') ms'
    >} write xp ms a v.
  Proof.
    unfold write; log_unfold.
    hoare; subst.
    admit. (* XXX valid_entries Map.add *)

    rewrite replay_add.
    eapply ptsto_upd; eauto.
    replace (replay ms m) with m0 by (apply functional_extensionality; eauto).
    eauto.
  Qed.

  Definition read T (xp : xparams) ms a rx : prog T :=
    match Map.find a ms with
    | Some v =>
      rx v
    | None =>
      v <- Read a;
      rx v
    end.

  Theorem read_ok: forall xp ms a,
    {< m1 m2 v,
    PRE    rep xp (ActiveTxn m1 m2) ms *
           [[ m2 @ a |-> v ]]
    POST:r rep xp (ActiveTxn m1 m2) ms *
           [[ r = v ]]
    CRASH  rep xp (ActiveTxn m1 m2) ms
    >} read xp ms a.
  Proof.
    unfold read; log_unfold.
    intros.
    case_eq (Map.find a ms); hoare.

    (*
    eapply pimpl_ok.
    auto with prog.
    norm.
    cancel.
    intuition.
    rewrite <- minus_n_O.
    rewrite firstn_length.
    instantiate (1:=v); congruence.
    unfold stars; simpl.
    norm.
    cancel.
    intuition.
    unfold stars; simpl.
    step.
    step.
    eapply replay_last_val; eauto. rewrite <- plus_n_O in *; auto.

    step.
    apply replay_last_irrel; auto. omega.

    assert (indomain a m1) as Ham1.
    eapply Log.indomain_replay; eauto.
    eexists; eauto.
    destruct Ham1.
    step.
    step.
    rewrite <- plus_n_O in *.
    rewrite Nat.sub_diag in *.
    simpl in *.
    congruence.
    step.
*)
  Qed.

  Definition flush T xp (ms:memstate) rx : prog T :=
    If (lt_dec (wordToNat (LogLen xp)) (Map.cardinal ms)) {
      rx false
    } else {
      Write (LogHeader xp) (header_to_valu (mk_header (Map.cardinal ms)));;
      Write (LogStart xp) (descriptor_to_valu (map fst (Map.elements ms)));;
      For i < $ (Map.cardinal ms)
      Ghost crash
      Loopvar _ <- tt
      Continuation lrx
      Invariant array (LogStart xp ^+ $1) (firstn (wordToNat i) (map snd (Map.elements ms))) $1
      OnCrash crash
      Begin
        Write (LogStart xp ^+ $1 ^+ i) (sel (map snd (Map.elements ms)) i $0);;
        lrx tt
      Rof;;
      rx true
    }.

  Theorem flush_ok : forall xp ms,
    {< m1 m2,
    PRE    rep xp (ActiveTxn m1 m2) ms
    POST:r ([[ r = true ]] * rep xp (FlushedTxn m1 m2) ms_empty) \/
           ([[ r = false ]] * rep xp (ActiveTxn m1 m2) ms)
    CRASH  any (* XXX this won't work *)
    >} flush xp ms.
  Proof.
    unfold flush; log_unfold.
    hoare.
    
  Qed.
  Hint Extern 1 ({{_}} progseq (flush _ _) _) => apply flush_ok : prog.

  Definition apply T xp ms rx : prog T :=
    For i < $ (Map.cardinal ms)
    Ghost crash cur
    Loopvar _ <- tt
    Continuation lrx
    Invariant
      (LogCommit xp) |-> $1
      * exists old, data_rep old
      * (replay (firstn (wordToNat i) (Map.elements ms)))
      * cur_rep old log cur
      * [[ forall a, cur a = replay (skipn (wordToNat i) log) old a ]]
    OnCrash
      rep xp (NoTransaction cur) \/
      rep xp (CommittedTxn cur)
    Begin
    rx tt.

  Definition commit T xp (ms:memstate) rx : prog T :=
    flush xp ms;;
    Write (LogCommit xp) $1;;
    apply xp ms;;
    rx tt.

  Theorem commit_ok: forall xp ms,
    {< m1 m2,
     PRE    rep xp (ActiveTxn m1 m2) ms
     POST:r rep xp (NoTransaction m2) ms_empty
     CRASH  any (* XXX *)
    >} commit xp ms.
  Proof.
    unfold commit; log_unfold.
    intros.
    eapply pimpl_ok2.
    eauto with prog.
    intros; simpl.
    norm.
    log_unfold.
    cancel.
    intuition; eauto.
    hoare_unfold log_unfold.
    apply pimpl_any.
  Qed.

  Definition read_log T xp rx : prog T :=
    rx ms_empty.

  Definition recover T xp rx : prog T :=
    v <- Read (LogCommit xp);
    If (weq v $1) {
      apply xp;;
      Write (LogCommit xp) $0;;
      Write (LogHeader xp) (header_to_valu (mk_header 0));;
      rx tt
    } else {
      Write (LogHeader xp) (header_to_valu (mk_header 0));;
      rx tt
    }.

  Hint Extern 0 (okToUnify (LOG.rep _ _) (LOG.rep _ _)) => constructor : okToUnify.

  Theorem recover_ok: forall xp,
    {< (exists m F, rep xp (NoTransaction m) ms_empty * F
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rx tt >> rec ]]
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]])
    \/ (exists m m' ms F, rep xp (ActiveTxn m m') ms * F
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rx tt >> rec ]]
        * [[ {{ rep xp (ActiveTxn m m') ms * F
             \/ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]])
    \/ (exists m F, rep xp (CommittedTxn m) ms_empty * F
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rx tt >> rec ]]
        * [[ {{ rep xp (CommittedTxn m) ms_empty * F
             \/ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]])
    >} recover xp rx >> rec.
  Proof.
    unfold recover, rep.
    step.
    apply stars_or_left.
    cancel; step.
    apply stars_or_right; apply stars_or_left.
    cancel; step.
    apply stars_or_right; apply stars_or_right.
    cancel; step.
  Qed.

  Lemma firstn_length: forall T (l:list T),
    firstn (length l) l = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  Lemma replay_last_val: forall ms m i a v, i < length ms
    -> LOG.replay (firstn (length ms - i) ms) m a = Some v
    -> fst (nth i (rev ms) LOG.logentry_zero) = a
    -> snd (nth i (rev ms) LOG.logentry_zero) = v.
  Proof.
    induction ms.
    - simpl; intros; omega.
    - intros m i.
      case_eq (eq_nat_dec i (length ms)).
      + intro Hi.
        simpl rev. rewrite app_nth2; rewrite rev_length.
        intros. subst i. rewrite Nat.sub_diag in *.
        simpl nth in *.
        simpl length in *.
        rewrite Nat.sub_succ_l in *.
        rewrite Nat.sub_diag in *.
        destruct a.
        simpl in *.
        subst.
        rewrite upd_eq in *; congruence.
        omega.
        omega.
      + simpl length. intros Hi _ a' v' Hi2.
        simpl rev. rewrite app_nth1; [|rewrite rev_length; omega].
        rewrite Nat.sub_succ_l; [|omega].
        destruct a; simpl.
        apply IHms.
        omega.
  Qed.

  Lemma replay_last_irrel: forall ms m i a v, i < length ms
    -> fst (nth i (rev ms) LOG.logentry_zero) <> a
    -> LOG.replay (firstn (length ms - i) ms) m a = Some v
    -> LOG.replay (firstn (length ms - S i) ms) m a = Some v.
  Proof.
    induction ms.
    - simpl; intros; omega.
    - simpl length.
      intros.
      case_eq (eq_nat_dec i (length ms)); intros.
      + subst i. rewrite Nat.sub_diag in *. simpl.
        simpl rev in *.
        rewrite app_nth2 in *; rewrite rev_length in *; [|omega].
        rewrite Nat.sub_succ_l in *; [|omega].
        rewrite Nat.sub_diag in *.
        destruct a; simpl in *.
        rewrite upd_ne in *; auto.
      + rewrite Nat.sub_succ_l in *; try omega.
        destruct a; simpl.
        apply IHms.
        omega.
        simpl rev in *; rewrite app_nth1 in *; [|rewrite rev_length; omega].
        auto.
        auto.
  Qed.

End MEMLOG.
