Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapList.
Require Import FMapFacts.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
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
Require Import WordAuto.

(* XXX parameterize by length and stick in Word.v *)
Module Addr_as_OT <: UsualOrderedType.
  Definition t := addr.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := @wlt addrlen.

  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
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
    rewrite valulen_is. apply leb_complete. compute. trivial.
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
  Qed.

  Theorem descriptor_valu_id : forall d,
    Rec.well_formed d -> valu_to_descriptor (descriptor_to_valu d) = d.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite descriptor_sz_ok.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    apply Rec.of_to_id; auto.
  Qed.

  Definition indomain' (a : addr) (m : diskstate) := wordToNat a < length m.

  (* Check that the state is well-formed *)
  Definition valid_entries m (ms : memstate) :=
    forall a v, Map.MapsTo a v ms -> indomain' a m.

  Definition valid_size xp (ms : memstate) :=
    Map.cardinal ms <= wordToNat (LogLen xp).

  (* Replay the state in memory *)
  Definition replay' V (l : list (addr * V)) (m : list V) : list V :=
    fold_left (fun m' p => upd m' (fst p) (snd p)) l m.

  Definition replay (ms : memstate) (m : diskstate) : diskstate :=
    replay' (Map.elements ms) m.

  Definition avail_region start len : @pred valu :=
    (exists l, [[ length l = len ]] * array start l $1)%pred.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start len =p=>
       start |->? * avail_region (start ^+ $1) (len - 1).
  Proof.
    destruct len; intros; try omega.
    unfold avail_region.
    admit.
  Qed.

  (** On-disk representation of the log *)
  Definition log_rep xp m (ms : memstate) : pred :=
     ((LogHeader xp) |-> header_to_valu (mk_header (Map.cardinal ms)) *
      [[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest, (LogStart xp) |-> descriptor_to_valu (map fst (Map.elements ms) ++ rest) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      array (LogStart xp ^+ $1) (map snd (Map.elements ms)) $1 *
      avail_region (LogStart xp ^+ $1 ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms))%pred.

  Definition data_rep (xp: xparams) (m: diskstate) : pred :=
    array $0 m $1.

  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred valu :=
    [[ cur = replay ms old ]]%pred.

  Definition rep xp (st: logstate) (ms: memstate) :=
    (* For now, support just one descriptor block, at the start of the log. *)
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
    match st with
    | NoTransaction m =>
      (LogCommit xp) |-> $0
    * [[ ms = ms_empty ]]
    * data_rep xp m
    * (LogHeader xp) |->?
    * avail_region (LogStart xp) (1 + wordToNat (LogLen xp))
    | ActiveTxn old cur =>
      (LogCommit xp) |-> $0
    * data_rep xp old (* Transactions are always completely buffered in memory. *)
    * (LogHeader xp) |->?
    * avail_region (LogStart xp) (1 + wordToNat (LogLen xp))
    * cur_rep old ms cur
    * [[ valid_entries old ms ]]
    | FlushedTxn old cur =>
      (LogCommit xp) |-> $0
    * data_rep xp old
    * log_rep xp old ms
    * cur_rep old ms cur
    | CommittedTxn cur =>
      (LogCommit xp) |-> $1
    * exists old, data_rep xp old
    * log_rep xp old ms
    * cur_rep old ms cur
    end)%pred.

  Definition init T xp rx : prog T :=
    Write (LogCommit xp) $0 ;;
    rx tt.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep, valid_size, Map.cardinal.

  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _ _) (data_rep _)) => constructor : okToUnify.

  Theorem init_ok : forall xp,
    {< old,
    PRE    [[ wordToNat (LogLen xp) <= addr_per_block ]] *
           data_rep xp old *
           avail_region (LogStart xp) (1 + wordToNat (LogLen xp)) *
           (LogCommit xp) |->? *
           (LogHeader xp) |->?
    POST:r rep xp (NoTransaction old) ms_empty
    CRASH  any
    >} init xp.
  Proof.
    unfold init; log_unfold.
    intros.
    hoare; apply pimpl_any.
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

    unfold valid_entries; intuition; inversion H0.
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
    replay (Map.add a v ms) m = upd (replay ms m) a v.
  Proof.
    intros.
    (* XXX move proof from Scratch.v *)
    admit.
  Qed.

  Definition write T (xp : xparams) (ms : memstate) a v rx : prog T :=
    rx (Map.add a v ms).

  Lemma valid_entries_add : forall a v ms m,
    valid_entries m ms -> indomain' a m -> valid_entries m (Map.add a v ms).
  Proof.
    unfold valid_entries in *.
    intros.
    destruct (weq a a0).
    subst; auto.
    eapply H.
    eapply Map.add_3; eauto.
  Qed.

  Theorem write_ok : forall xp ms a v,
    {< m1 m2 F' v0,
    PRE      rep xp (ActiveTxn m1 m2) ms * [[ (F' * a |-> v0)%pred (list2mem m2) ]]
    POST:ms' exists m', rep xp (ActiveTxn m1 m') ms' *
             [[(F' * a |-> v)%pred (list2mem m') ]]
    CRASH    exists m' ms', rep xp (ActiveTxn m1 m') ms'
    >} write xp ms a v.
  Proof.
    unfold write; log_unfold.
    hoare; subst.

    apply valid_entries_add; eauto.
    unfold indomain'.
    admit.

    rewrite replay_add.
    eapply list2mem_upd; eauto.
  Qed.

  Definition read T (xp: xparams) ms a rx : prog T :=
    match Map.find a ms with
    | Some v =>
      rx v
    | None =>
      v <- ArrayRead $0 a $1;
      rx v
    end.

  Lemma replay_sel : forall a v ms m def,
    Map.MapsTo a v ms -> sel (replay ms m) a def = v.
  Proof.
    admit.
  Qed.

  Theorem read_ok: forall xp ms a,
    {< m1 m2 v,
    PRE    rep xp (ActiveTxn m1 m2) ms *
           [[ list2mem m2 @ a |-> v ]]
    POST:r rep xp (ActiveTxn m1 m2) ms *
           [[ r = v ]]
    CRASH  rep xp (ActiveTxn m1 m2) ms
    >} read xp ms a.
  Proof.
    unfold read; log_unfold.
    intros.

    case_eq (Map.find a ms); hoare.
    subst.

    unfold diskptsto in H5.
    apply Map.find_2 in H.
    eapply replay_sel in H.
    unfold list2mem in H5.
    erewrite sel_map in H5.
    inversion H5.
    rewrite <- H.
    instantiate (def := $0).
    reflexivity.

    destruct (lt_dec (wordToNat a) (length (replay ms d))); auto.
    admit.

    admit.

    admit.
  Qed.

  Definition flush T xp (ms:memstate) rx : prog T :=
    If (lt_dec (wordToNat (LogLen xp)) (Map.cardinal ms)) {
      rx false
    } else {
      Write (LogHeader xp) (header_to_valu (mk_header (Map.cardinal ms)));;
      Write (LogStart xp) (descriptor_to_valu (map fst (Map.elements ms)));;
      For i < $ (Map.cardinal ms)
      Ghost old crash
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (LogCommit xp) |-> $0
        * data_rep xp old
        * (LogHeader xp) |-> header_to_valu (mk_header (Map.cardinal ms))
        * (LogStart xp) |-> descriptor_to_valu (map fst (Map.elements ms))
        * array (LogStart xp ^+ $1) (firstn (wordToNat i) (map snd (Map.elements ms))) $1
        * avail_region (LogStart xp ^+ $1 ^+ i) (wordToNat (LogLen xp) - wordToNat i)
      OnCrash crash
      Begin
        Write (LogStart xp ^+ $1 ^+ i) (sel (map snd (Map.elements ms)) i $0);;
        lrx tt
      Rof;;
      rx true
    }.

  Theorem firstn_map : forall A B l n (f: A -> B),
    firstn n (map f l) = map f (firstn n l).
  Proof.
    admit.
  Qed.

  Lemma array_inc_firstn : forall a l i,
    $ (a + wordToNat i) |-> sel l i (natToWord valulen 0) * array ($ a) (firstn (wordToNat i) l) $1 =p=>
    array ($ a) (firstn (wordToNat i + 1) l) $1.
  Proof.
    intros.
    admit.
  Qed.

  Ltac word2nat_clear := try clear_norm_goal; repeat match goal with
    | [ H : forall _, {{ _ }} _ |- _ ] => clear H
    | [ H : _ =p=> _ |- _ ] => clear H
    end.

(*
  Hint Extern 1 (avail_region _ _ =!=> _) =>
    word2nat_clear; apply avail_region_shrink_one; word2nat_auto : norm_hint_left.
*)

  Fixpoint zeroes sz n :=
    match n with
    | 0 => []
    | S n' => natToWord sz n :: zeroes sz n'
    end.

  Theorem flush_ok : forall xp ms,
    {< m1 m2,
    PRE    rep xp (ActiveTxn m1 m2) ms
    POST:r ([[ r = true ]] * rep xp (FlushedTxn m1 m2) ms) \/
           ([[ r = false ]] * rep xp (ActiveTxn m1 m2) ms)
    CRASH  rep xp (ActiveTxn m1 m2) ms
    >} flush xp ms.
  Proof.
    unfold flush; log_unfold; unfold avail_region.
    intros.
    assert (goodSize addrlen (wordToNat (LogLen xp))) by (apply wordToNat_bound).

    step.
    step.
    step.
    eapply pimpl_ok2.
    eauto with prog.
    simpl.
    intros.
    rewrite isolate_fwd with (a := LogStart xp) (i := $0).
    cancel.
    eapply pimpl_ok2.
    eauto with prog.
    cancel.
    word2nat_clear. word2nat_simpl. rewrite plus_0_r.
    rewrite wordToNat_natToWord_idempotent'.
    rewrite wordToNat_natToWord_idempotent'.
    simpl.
    cancel.
    hnf. apply leb_complete. reflexivity.
    hnf. apply leb_complete. reflexivity.
    admit.
    eapply pimpl_ok2.
    eauto with prog.
    intros.
    simpl.
    norm'l.
    unfold stars.
    simpl.
    rewrite isolate_fwd with (a := LogStart xp ^+ $ (1) ^+ m) (i := $0).
    cancel.
    step.
    word2nat_clear. word2nat_simpl.
    simpl wordToNat.
    simpl.
    rewrite <- plus_assoc.
    rewrite plus_ovf_l.
    cancel.
    admit.
    word2nat_clear.
    destruct l0; word2nat_auto; simpl in *; omega.
    cancel.
    word2nat_clear.
    instantiate (default0 := $0).
    instantiate (default := $0).
    instantiate (a0 := descriptor_to_valu (map fst (Map.elements ms)) :: firstn (wordToNat m) (map snd (Map.elements ms)) ++ l0).
    admit.
    admit.
    word2nat_clear. word2nat_auto.
    step.
    apply stars_or_left.
    cancel.
    instantiate (a := zeroes addrlen (addr_per_block - length (Map.this ms))).
    rewrite firstn_oob.
    cancel.
    admit.
    unfold Map.elements, Map.Raw.elements.
    word2nat_clear. rewrite map_length.
    word2nat_auto.
    rewrite app_length.
    rewrite map_length.
    unfold Map.elements, Map.Raw.elements.
    admit.
    rewrite Forall_forall. intros. trivial.
    word2nat_auto.
    cancel.
    instantiate (l := zeroes valulen (S (wordToNat (LogLen xp)))).
    admit.
    cancel.
    instantiate (a0 := l).
    admit.
    auto.
    instantiate (w := $0).
    word2nat_auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush _ _) _) => apply flush_ok : prog.

  Definition apply T xp ms rx : prog T :=
    For i < $ (Map.cardinal ms)
    Ghost cur
    Loopvar _ <- tt
    Continuation lrx
    Invariant
      (LogCommit xp) |-> $1
      * log_rep xp cur ms
      * exists old, data_rep xp old
      * [[ replay' (skipn (wordToNat i) (Map.elements ms)) old = cur ]]
    OnCrash
      rep xp (NoTransaction cur) ms_empty \/
      rep xp (CommittedTxn cur) ms
    Begin
      ArrayWrite $0 (sel (map fst (Map.elements ms)) i $0) $1 (sel (map snd (Map.elements ms)) i $0);;
      lrx tt
    Rof;;
    Write (LogCommit xp) $0;;
    rx tt.

  Theorem apply_ok: forall xp ms,
    {< m,
    PRE    rep xp (CommittedTxn m) ms
    POST:r rep xp (NoTransaction m) ms_empty
    CRASH  rep xp (NoTransaction m) ms_empty \/
           rep xp (CommittedTxn m) ms
    >} apply xp ms.
  Proof.
    unfold apply; log_unfold.
    hoare.
    admit.
    admit.
    admit.
    eapply pimpl_or_r. right.
    cancel.
    admit.
    (* Somewhat subtle: if replaying the entire log on [d0] is equal to replaying a suffix on [d],
       then replaying the entire log on [d] is also equal. *)
    admit.
    eapply pimpl_or_r. right.
    cancel.
    admit.
    admit.
    admit.
    eapply pimpl_or_r. right.
    cancel.
    admit.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply _ _) _) => apply apply_ok : prog.

  Definition commit T xp (ms:memstate) rx : prog T :=
    ok <- flush xp ms;
    If (bool_dec ok true) {
      Write (LogCommit xp) $1;;
      apply xp ms;;
      rx true
    } else {
      rx false
    }.

  Theorem commit_ok: forall xp ms,
    {< m1 m2,
     PRE    rep xp (ActiveTxn m1 m2) ms
     POST:r ([[ r = true ]] * rep xp (NoTransaction m2) ms_empty) \/
            ([[ r = false ]] * rep xp (ActiveTxn m1 m2) ms)
     CRASH  rep xp (ActiveTxn m1 m2) ms \/
            rep xp (CommittedTxn m2) ms \/
            rep xp (NoTransaction m2) ms_empty
    >} commit xp ms.
  Proof.
    unfold commit.
    hoare_unfold log_unfold.
    (* XXX make [hoare_unfold] unfold before [cancel] so it can handle all these goals *)
    log_unfold; cancel.
    eapply pimpl_or_r; right.
    eapply pimpl_or_r; right.
    abstract cancel.
    log_unfold; cancel.
    eapply pimpl_or_r; right.
    eapply pimpl_or_r; left.
    abstract cancel.
    eapply pimpl_or_r; left.
    cancel.
    admit.
    log_unfold; cancel.
    eapply pimpl_or_r; left.
    cancel.
  Qed.

  Module MapProperties := WProperties Map.

  Definition read_log T (xp: xparams) rx : prog T :=
    d <- Read (LogStart xp);
    let desc := valu_to_descriptor d in
    h <- Read (LogHeader xp);
    let len := (valu_to_header h) :-> "length" in
    log <- For i < len
    Ghost cur log_on_disk
    Loopvar log_prefix <- []
    Continuation lrx
    Invariant
      (LogCommit xp) |-> $1
      * log_rep xp cur log_on_disk
      * [[ log_prefix = firstn (wordToNat i) (Map.elements log_on_disk) ]]
      * data_rep xp cur
    OnCrash
      rep xp (CommittedTxn cur) log_on_disk
    Begin
      v <- ArrayRead (LogStart xp ^+ $1) i $1;
      lrx (log_prefix ++ [(sel desc i $0, v)])
    Rof;
    rx (MapProperties.of_list log).

  Theorem read_log_ok: forall xp,
    {< m ms,
    PRE    rep xp (CommittedTxn m) ms
    POST:r [[ r = ms ]] * rep xp (CommittedTxn m) ms
    CRASH  rep xp (CommittedTxn m) ms
    >} read_log xp.
  Proof.
    unfold read_log; log_unfold.
    hoare.
    rewrite header_valu_id in H0. unfold mk_header, Rec.recget' in H0. simpl in H0.
    rewrite map_length.
    word2nat_clear. unfold Map.elements, Map.Raw.elements. word2nat_auto.
    rewrite descriptor_valu_id.
    admit.
    hnf. intuition.
    admit.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_log _) _) => apply read_log_ok : prog.

  Definition recover T xp rx : prog T :=
    v <- Read (LogCommit xp);
    If (weq v $1) {
      ms <- read_log xp;
      apply xp ms;;
      rx tt
    } else {
      rx tt
    }.

  Definition log_intact xp m ms :=
    ((rep xp (NoTransaction m) ms) \/
     (exists m', rep xp (ActiveTxn m m') ms) \/
     (exists m', rep xp (FlushedTxn m m') ms) \/
     (rep xp (CommittedTxn m) ms))%pred.

  Theorem recover_ok: forall xp,
    {< m ms,
    PRE     log_intact xp m ms
    POST:r  rep xp (NoTransaction m) ms_empty
    CRASH   log_intact xp m ms
    >} recover xp.
  Proof.
    unfold recover; log_unfold.
    intros; eapply pimpl_ok2; [ eauto with prog | ].
    unfold log_intact; log_unfold.
    cancel.
    step.
    step.
    instantiate (a := nil).
    instantiate (a0 := ms_empty).
    apply natToWord_discriminate in H6; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    apply natToWord_discriminate in H6; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    apply natToWord_discriminate in H6; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    step.
    cancel.
    apply stars_or_left.
    cancel.
    step.
    step.
    instantiate (a := nil).
    instantiate (a0 := ms_empty).
    apply natToWord_discriminate in H7; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    apply natToWord_discriminate in H7; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    apply natToWord_discriminate in H7; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    step.
    cancel.
    apply stars_or_right.
    apply stars_or_left.
    cancel.
    step.
    step.
    apply natToWord_discriminate in H6; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    apply natToWord_discriminate in H6; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    apply natToWord_discriminate in H6; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial].
    step.
    admit.
    cancel.
    apply stars_or_right.
    apply stars_or_right.
    apply stars_or_left.
    cancel.
    step.
    eapply pimpl_ok2.
    eauto with prog.
    log_unfold.
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ]; log_unfold; subst; cancel.
    subst; cancel.
    subst; auto.
    subst; auto.
    subst; auto.
    step.
    cancel.
    apply stars_or_right.
    apply stars_or_left.
    cancel.
    congruence.
    admit.
    apply stars_or_right.
    apply stars_or_right.
    apply stars_or_right.
    cancel.
    cancel.
    apply stars_or_right.
    apply stars_or_right.
    apply stars_or_right.
    cancel.
    step.
    cancel.
    apply stars_or_right.
    apply stars_or_right.
    apply stars_or_right.
    instantiate (a := nil).
    instantiate (a0 := ms_empty).
    instantiate (a1 := any).
    instantiate (a2 := any).
    instantiate (a3 := any).
    cancel.
  Qed.


  Definition read_array T xp ms a i stride rx : prog T :=
    read xp ms (a ^+ i ^* stride) rx.

  Definition write_array T xp ms a i stride v rx : prog T :=
    write xp ms (a ^+ i ^* stride) v rx.

  Theorem read_array_ok : forall xp ms a i stride,
    {< mbase m vs,
    PRE    rep xp (ActiveTxn mbase m) ms *
           [[ exists F', (array a vs stride * F')%pred (list2mem m) ]] *
           [[ wordToNat i < length vs ]]
    POST:r [[ r = sel vs i $0 ]] * rep xp (ActiveTxn mbase m) ms
    CRASH  rep xp (ActiveTxn mbase m) ms
    >} read_array xp ms a i stride.
  Proof.
    intros.
    apply pimpl_ok2 with (fun done crash => exists F mbase m vs, rep xp (ActiveTxn mbase m) ms * F
     * [[ exists F',
          (array a (firstn (wordToNat i) vs) stride
           * (a ^+ i ^* stride) |-> sel vs i $0
           * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F')%pred (list2mem m) ]]
     * [[ wordToNat i < length vs ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn mbase m) ms * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx (sel vs i $0) ]]
     * [[ rep xp (ActiveTxn mbase m) ms * F =p=> crash ]])%pred.
    unfold read_array.
    eapply pimpl_ok2.
    apply read_ok.
    cancel.
    hnf. unfold list2mem.
    erewrite sel_map.
    instantiate (default' := $0).
    f_equal.
    admit.
    step.
    admit.
    cancel.

    cancel.
    eapply pimpl_trans.
    eapply pimpl_sep_star; [ apply pimpl_refl |].
    apply isolate_fwd; eauto.
    cancel.
    auto.
    step.

    cancel.
  Qed.

  Theorem write_array_ok : forall xp ms a i stride v,
    {< mbase m vs F',
    PRE      rep xp (ActiveTxn mbase m) ms
           * [[ (array a vs stride * F')%pred (list2mem m) ]]
           * [[ wordToNat i < length vs ]]
    POST:ms' exists m', rep xp (ActiveTxn mbase m') ms'
           * [[ (array a (Array.upd vs i v) stride * F')%pred (list2mem m') ]]
    CRASH  exists m' ms', rep xp (ActiveTxn mbase m') ms'
    >} write_array xp ms a i stride v.
  Proof.
    intros.
    apply pimpl_ok2 with (fun done crash => exists F mbase m vs F',
       rep xp (ActiveTxn mbase m) ms * F
     * [[ (array a (firstn (wordToNat i) vs) stride
           * (a ^+ i ^* stride) |-> sel vs i $0
           * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F')%pred (list2mem m) ]]
     * [[ wordToNat i < length vs ]]
     * [[ forall ms',
          {{ fun done' crash' =>
          exists m', rep xp (ActiveTxn mbase m') ms' * F
           * [[ (array a (Array.upd vs i v) stride * F')%pred (list2mem m') ]]
           * [[ done' = done ]] * [[ crash' = crash ]] }} rx ms' ]]
     * [[ forall m' ms', rep xp (ActiveTxn mbase m') ms' * F =p=> crash ]])%pred.
    unfold write_array.
    eapply pimpl_ok2.
    apply write_ok.
    cancel.

    step.
    eapply pimpl_trans; [| apply isolate_bwd ].
    instantiate (1:=i).
    autorewrite with core.
    cancel.
    autorewrite with core.
    cancel.
    autorewrite with core; assumption.

    norm.
    cancel.
    auto.

    cancel.
    eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl
                                                | apply isolate_fwd; eauto ] | ].
    cancel.

    eauto.

    instantiate (default:=$0).
    step.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _ _) _) => apply write_array_ok : prog.

End MEMLOG.
