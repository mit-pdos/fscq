Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapAVL.
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

Module Map := FMapAVL.Make(Addr_as_OT).

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

(*
| FlushedUnsyncTxn (old : diskstate) (cur : diskstate)
(* A transaction has been flushed to the log, but not sync'ed or
 * committed yet. *)
*)

| FlushedTxn (old : diskstate) (cur : diskstate)
(* Like FlushedUnsyncTxn above, except that we sync'ed the log.
 *)

| CommittedUnsyncTxn (old : diskstate) (cur : diskstate)

| CommittedTxn (cur : diskstate)
(* A transaction has committed but the log has not necessarily been applied yet. *)


| AppliedUnsyncTxn (cur : diskstate)
(* A transaction has been committed and applied but not yet flushed. *)

| AppliedTxn (cur : diskstate)
(* A transaction has been committed, applied, and flushed. *).

Record xparams := {
  (* The actual data region is everything that's not described here *)
  LogHeader : addr; (* Store the header here *)
  LogCommit : addr; (* Store true to apply after crash. *)

  LogDescriptor : addr; (* Start of descriptor region in log *)
  LogData : addr; (* Start of data region in log *)
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
  Proof.
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

  Definition avail_region start len : @pred addr (@weq addrlen) valuset :=
    (exists l, [[ length l = len ]] * array start l $1)%pred.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start len =p=>
       start |->? * avail_region (start ^+ $1) (len - 1).
  Proof.
    destruct len; intros; try omega.
    unfold avail_region.
    norm'l; unfold stars; simpl.
    destruct l; simpl in *; try congruence.
    cancel.
  Qed.

  Fixpoint repeat T n (t: T) :=
    match n with
    | 0 => nil
    | S n' => t :: repeat n' t
    end.

  Lemma repeat_length: forall T n t, length (@repeat T n t) = n.
  Proof.
    induction n; intros; simpl; auto.
  Qed.

  Definition synced_list m: list valuset := List.combine m (repeat (length m) nil).

  Definition data_rep (xp: xparams) (m: list valuset) : @pred addr (@weq addrlen) valuset :=
    array $0 m $1.

  (** On-disk representation of the log *)
  Definition log_rep xp m (ms : memstate) : @pred addr (@weq addrlen) valuset :=
     ((LogHeader xp) |=> (header_to_valu (mk_header (Map.cardinal ms))) *
      [[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest,
      (LogDescriptor xp) |=> (descriptor_to_valu (map fst (Map.elements ms) ++ rest)) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      array (LogData xp) (synced_list (map snd (Map.elements ms))) $1 *
      avail_region (LogData xp ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms))%pred.


  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred addr (@weq addrlen) valuset :=
    [[ cur = replay ms old ]]%pred.

  (** XXX update comment
   * This specialized variant of [ptsto] is used for the [CommittedTxn] state.
   *
   * Because we don't want to flush on every block during apply, we want to
   * use [ptsto_cur] for parts of the disk that are being modified during log
   * apply.  But using [ptsto_cur] for the entire data portion of the disk is
   * too loose: this implies that even blocks that are not being modified by
   * the log could be in flux.  So if we crash, some unrelated block might
   * change its value, and replaying the log will do nothing to recover from
   * this change.
   *
   * Instead, we want to say that any blocks that are present in [ms] can be
   * in flux (i.e., use [ptsto_cur]), and all other blocks cannot be in flux
   * (i.e., use [ptsto_synced]).
   *)
  Definition nil_unless_in (ms: list addr) (l: list (list valu)) :=
    forall a, ~ In a ms -> sel l a nil = nil.

  Definition equal_unless_in T (ms: list addr) (m1: list T) (m2: list T) (def: T) :=
    forall a, ~ In a ms -> sel m1 a def = sel m2 a def.

  Definition rep xp (st: logstate) (ms: memstate) :=
    (* For now, support just one descriptor block, at the start of the log. *)
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
     (* The log shouldn't overflow past the end of disk *)
     [[ goodSize addrlen (# (LogData xp) + # (LogLen xp)) ]] *
    match st with
    | NoTransaction m =>
      (LogCommit xp) |=> $0
    * [[ ms = ms_empty ]]
    * data_rep xp (synced_list m)
    * (LogHeader xp) |->?
    * (LogDescriptor xp) |->?
    * avail_region (LogData xp) (wordToNat (LogLen xp))

    | ActiveTxn old cur =>
      (LogCommit xp) |=> $0
    * data_rep xp (synced_list old) (* Transactions are always completely buffered in memory. *)
    * (LogHeader xp) |->?
    * (LogDescriptor xp) |->?
    * avail_region (LogData xp) (wordToNat (LogLen xp))
    * cur_rep old ms cur
    * [[ valid_entries old ms ]]

(*
    | FlushedUnsyncTxn old cur =>
      (LogCommit xp) |=> $0
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur
*)

    | FlushedTxn old cur =>
      (LogCommit xp) |=> $0
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur

    | CommittedUnsyncTxn old cur =>
      (LogCommit xp) |-> ($1, $0 :: nil)
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur

    | CommittedTxn cur =>
      (LogCommit xp) |=> $1
    * exists old d, data_rep xp d
      (* If something's in the transaction, it doesn't matter what state it's in on disk *)
    * [[ equal_unless_in (map fst (Map.elements ms)) (synced_list old) d ($0, nil) ]]
    * log_rep xp old ms
    * cur_rep old ms cur

    | AppliedUnsyncTxn cur =>
      (LogCommit xp) |=> $1
    * exists old old_unflushed, data_rep xp (List.combine cur old_unflushed)
    * [[ nil_unless_in (map fst (Map.elements ms)) old_unflushed ]]
    * log_rep xp old ms
    * cur_rep old ms cur

    | AppliedTxn cur =>
      (LogCommit xp) |-> ($0, $1 :: nil)
    * data_rep xp (synced_list cur)
    * exists old, log_rep xp old ms
    * cur_rep old ms cur

    end)%pred.


  Definition init T xp rx : prog T :=
    Write (LogCommit xp) $0;;
    Sync (LogCommit xp);;
    rx tt.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep, valid_size, synced_list.

  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _ _) (data_rep _)) => constructor : okToUnify.

  Definition log_uninitialized xp old :=
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
     [[ goodSize addrlen (# (LogData xp) + # (LogLen xp)) ]] *
     data_rep xp (synced_list old) *
     avail_region (LogData xp) (wordToNat (LogLen xp)) *
     (LogCommit xp) |->? *
     (LogDescriptor xp) |->? *
     (LogHeader xp) |->?)%pred.

  Theorem init_ok : forall xp,
    {< old,
    PRE    log_uninitialized xp old
    POST:r rep xp (NoTransaction old) ms_empty
    CRASH  log_uninitialized xp old
    >} init xp.
  Proof.
    unfold init, log_uninitialized; log_unfold.
    intros.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _) _) => apply init_ok : prog.

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

    unfold valid_entries; intuition; inversion H.
  Qed.

  Hint Extern 1 ({{_}} progseq (begin _) _) => apply begin_ok : prog.

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

  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.

  Lemma replay_add : forall a v ms m,
    replay (Map.add a v ms) m = upd (replay ms m) a v.
  Proof.
    intros.
    (* XXX move proof from Scratch.v *)
    admit.
  Qed.

  Definition write T (xp : xparams) a v (ms : memstate) rx : prog T :=
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

  Lemma replay_length : forall ms m,
    length (replay ms m) = length m.
  Proof.
    admit.
  Qed.

  Theorem write_ok : forall xp ms a v,
    {< m1 m2 F' v0,
    PRE      rep xp (ActiveTxn m1 m2) ms * [[ (F' * a |-> v0)%pred (list2mem m2) ]]
    POST:ms' exists m', rep xp (ActiveTxn m1 m') ms' *
             [[(F' * a |-> v)%pred (list2mem m') ]]
    CRASH    exists m' ms', rep xp (ActiveTxn m1 m') ms'
    >} write xp a v ms.
  Proof.
    unfold write; log_unfold.
    hoare; subst.

    apply valid_entries_add; eauto.
    unfold indomain'.
    erewrite <- replay_length.
    (* XXX probably want to make a version of [list2mem_ptsto_bounds] that takes two lists
       and a hypothesis that their lengths are equal *)
    eapply list2mem_ptsto_bounds; eauto.

    rewrite replay_add.
    eapply list2mem_upd; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.

  Definition read T (xp: xparams) a ms rx : prog T :=
    match Map.find a ms with
    | Some v =>
      rx v
    | None =>
      v <- ArrayRead $0 a $1;
      rx v
    end.

  Lemma replay_sel : forall a v ms m def,
    indomain' a m -> Map.MapsTo a v ms -> sel (replay ms m) a def = v.
  Proof.
    admit.
  Qed.

  Lemma replay_sel_other : forall a ms m def,
    ~ Map.In a ms -> selN (replay ms m) (wordToNat a) def = selN m (wordToNat a) def.
  Proof.
    admit.
  Qed.

  Theorem read_ok: forall xp ms a,
    {< m1 m2 v,
    PRE    rep xp (ActiveTxn m1 m2) ms *
           [[ exists F, (F * a |-> v) (list2mem m2) ]]
    POST:r rep xp (ActiveTxn m1 m2) ms *
           [[ r = v ]]
    CRASH  rep xp (ActiveTxn m1 m2) ms
    >} read xp a ms.
  Proof.
    unfold read; log_unfold.
    intros.

    case_eq (Map.find a ms); hoare.
    subst.

    eapply list2mem_sel with (def := $0) in H1.
    apply Map.find_2 in H.
    eapply replay_sel in H.
    rewrite <- H.
    rewrite H1.
    reflexivity.
    unfold valid_entries in H8.
    eapply H8; eauto.

    rewrite combine_length_eq.
    erewrite <- replay_length.
    eapply list2mem_inbound; eauto.
    rewrite repeat_length; auto.
    unfold sel; rewrite selN_combine.
    simpl.
    eapply list2mem_sel with (def := $0) in H1.
    rewrite H1.
    unfold sel.
    rewrite replay_sel_other. trivial.
    intuition.
    hnf in H4.
    destruct H4.
    apply Map.find_1 in H4.
    congruence.
    rewrite repeat_length; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.

  Definition flush T xp (ms:memstate) rx : prog T :=
    If (lt_dec (wordToNat (LogLen xp)) (Map.cardinal ms)) {
      rx false
    } else {
      (* Write... *)
      Write (LogHeader xp) (header_to_valu (mk_header (Map.cardinal ms)));;
      Write (LogDescriptor xp) (descriptor_to_valu (map fst (Map.elements ms)));;
      For i < $ (Map.cardinal ms)
      Ghost old crash
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (LogCommit xp) |=> $0
        * data_rep xp (synced_list old)
        * (LogHeader xp) |~> header_to_valu (mk_header (Map.cardinal ms))
        * (LogDescriptor xp) |~> descriptor_to_valu (map fst (Map.elements ms))
        * exists l', [[ length l' = # i ]] 
        * array (LogData xp) (firstn (# i) (List.combine (map snd (Map.elements ms)) l')) $1
        * avail_region (LogData xp ^+ i) (# (LogLen xp) - # i)
      OnCrash crash
      Begin
        Write (LogData xp ^+ i) (sel (map snd (Map.elements ms)) i $0);;
        lrx tt
      Rof;;
      (* ... and sync *)
      Sync (LogHeader xp);;
      Sync (LogDescriptor xp);;
      For i < $ (Map.cardinal ms)
      Ghost old crash
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (LogCommit xp) |=> $0
        * data_rep xp (synced_list old)
        * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal ms))
        * (LogDescriptor xp) |=> descriptor_to_valu (map fst (Map.elements ms))
        * array (LogData xp) (firstn (# i) (synced_list (map snd (Map.elements ms)))) $1
        * exists l', [[ length l' = Map.cardinal ms - # i ]]
        * array (LogData xp ^+ i) (List.combine (skipn (# i) (map snd (Map.elements ms))) l') $1
        * avail_region (LogData xp ^+ $ (Map.cardinal ms)) (# (LogLen xp) - Map.cardinal ms)
      OnCrash crash
      Begin
        Sync (LogData xp ^+ i);;
        lrx tt
      Rof;;
      rx true
    }.

  Theorem firstn_map : forall A B l n (f: A -> B),
    firstn n (map f l) = map f (firstn n l).
  Proof.
    admit.
  Qed.

  Lemma array_inc_firstn : forall a (l: list valuset) (i: addr) x,
    $ (a + # i) |-> x * array ($ a) (firstn (# i) l) $1 =p=>
    array ($ a) (firstn (# i + 1) (firstn (# i) l ++ [x])) $1.
  Proof.
    intros.
    admit.
  Qed.

  Lemma combine_one: forall A B (a: A) (b: B), [(a, b)] = List.combine [a] [b].
  Proof.
    intros; auto.
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

  (* XXX sometimes [step] instantiates too many evars *)
  Ltac step' :=
    intros;
    try cancel;
    remember_xform;
    ((eapply pimpl_ok2; [ solve [ eauto with prog ] | ])
     || (eapply pimpl_ok2_cont; [ solve [ eauto with prog ] | | ])
     || (eapply pimpl_ok3; [ solve [ eauto with prog ] | ])
     || (eapply pimpl_ok3_cont; [ solve [ eauto with prog ] | | ])
     || (eapply pimpl_ok2; [
          match goal with
          | [ |- {{ _ }} ?a _ ] => is_var a
          end; solve [ eapply nop_ok ] | ]));
    intros; subst;
    repeat destruct_type unit;  (* for returning [unit] which is [tt] *)
    try ( cancel ; try ( progress autorewrite_fast ; cancel ) );
    apply_xform cancel;
(*  try cancel; try autorewrite_fast; *)
(*  intuition eauto; *)
    try omega;
    try congruence.
(*  eauto. *)

  Hint Rewrite app_length firstn_length skipn_length combine_length map_length replay_length repeat_length length_upd : lengths.

  Ltac solve_lengths' :=
    repeat (progress (autorewrite with lengths; repeat rewrite Nat.min_l by solve_lengths'; repeat rewrite Nat.min_r by solve_lengths'));
    repeat rewrite Map.cardinal_1 in *;
    simpl; try word2nat_solve.

  Ltac solve_lengths := intros; word2nat_clear; simpl; word2nat_simpl; word2nat_rewrites; unfold valuset in *; solve_lengths'.

  Lemma upd_prepend_length: forall l a v, length (upd_prepend l a v) = length l.
  Proof.
    intros; unfold upd_prepend.
    solve_lengths.
  Qed.
  Hint Rewrite upd_prepend_length : lengths.

  Ltac assert_lte a b := let H := fresh in assert (a <= b)%word as H by
      (word2nat_simpl; repeat rewrite wordToNat_natToWord_idempotent'; word2nat_solve); clear H.

  Ltac array_sort' :=
    eapply pimpl_trans; rewrite emp_star; [ apply pimpl_refl |];
    repeat rewrite <- sep_star_assoc;
    repeat match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      assert_lte a2 a1;
      try (assert_lte a1 a2; fail 1); (* don't swap forever if two terms are equal *)
      rewrite (sep_star_assoc p (array a1 l1 s));
      rewrite (sep_star_comm (array a1 l1 s)); rewrite <- (sep_star_assoc p (array a2 l2 s))
    end;
    eapply pimpl_trans; rewrite <- emp_star; [ apply pimpl_refl |].

  Ltac array_sort :=
    word2nat_clear; word2nat_auto; [ array_sort' | .. ].

  Lemma singular_array: forall T a (v: T),
    a |-> v =p=> array a [v] $1.
  Proof.
    intros. cancel.
  Qed.

  Lemma array_app: forall T (l1 l2: list T) a1 a2,
    a2 = a1 ^+ $ (length l1) ->
    array a1 l1 $1 * array a2 l2 $1 <=p=> array a1 (l1 ++ l2) $1.
  Proof.
    induction l1.
    (* XXX make word2nat_auto handle all these *)
    intros; word2nat_auto; simpl in *; rewrite Nat.add_0_r in *; word2nat_auto; split; cancel.
    intros; simpl; rewrite sep_star_assoc. rewrite IHl1. auto.
    word2nat_auto; simpl in *; word2nat_auto.
  Qed.

  Lemma equal_arrays: forall T (l1 l2: list T) a,
    l1 = l2 -> array a l1 $1 =p=> array a l2 $1.
  Proof.
    cancel.
  Qed.

  Ltac array_match :=
    repeat rewrite singular_array;
    array_sort;
    repeat (rewrite array_app; [ | solve_lengths ]); [ repeat rewrite <- app_assoc | .. ];
    try apply pimpl_refl;
    try apply equal_arrays.


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

    step.
    step.
    step.
    step.
    step'.
    word2nat_clear; word2nat_auto. rewrite Nat.add_0_r.
    word2nat_auto.
    cancel.
    instantiate (a4 := nil).
    auto.
    destruct l; simpl in *; try discriminate; solve_lengths.
    eapply pimpl_ok2.
    eauto with prog.
    intros.
    simpl.
    norm'l.
    unfold stars.
    simpl.
    rewrite isolate_fwd with (a := LogData xp ^+ m) (i := $0) by solve_lengths.
    cancel.
    step.
    array_match.
    rewrite firstn_plusone_selN with (def := ($0, nil)).
    instantiate (a2 := l2 ++ [valuset_list (sel l3 $0 ($0, nil))]).
    instantiate (a3 := skipn 1 l3).
    admit. (* list manipulation *)
    solve_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.
    destruct l3; simpl in *; try discriminate; solve_lengths.

    pimpl_crash.
    (* XXX prevent [cancel] from canceling the wrong things here *)
    norm; intuition.
    delay_one.
    delay_one.
    cancel_one.
    cancel_one.
    cancel_one.
    cancel_one.
    cancel_one.
    delay_one.
    unfold stars; simpl;
    try match goal with
    | [ |- emp * _ =p=> _ ] => eapply pimpl_trans; [ apply star_emp_pimpl |]
    end.
    array_match.
    destruct l3; simpl in *; try discriminate; solve_lengths.
    step'.
    step'.
    step'.
    word2nat_clear. word2nat_auto.
    rewrite plus_0_r.
    rewrite firstn_oob.
    word2nat_auto.
    cancel.
    solve_lengths.
    solve_lengths.
    solve_lengths.

    step'.
    rewrite isolate_fwd with (a := LogData xp ^+ m) (i := $0).
    word2nat_clear; word2nat_auto.
    rewrite Nat.mul_0_l.
    rewrite plus_0_r.
    unfold sel.
    rewrite selN_combine.
    (* XXX for some reason, [cancel] dies here... *)
    norm.
    delay_one.
    delay_one.
    cancel_one.
    delay_one.
    delay_one.
    delay_one.
    delay_one.
    delay_one.
    delay_one.
    delay_one.
    unfold stars at 2 3; simpl; apply finish_frame.
    intuition.
    solve_lengths.
    solve_lengths.

    step'.
    word2nat_clear; word2nat_auto.
    cancel.
    instantiate (a := skipn 1 l6).
    array_match.
    admit. (* list manipulation *)
    word2nat_clear.
    destruct l6; simpl in *; abstract word2nat_auto.
    auto.

    cancel.
    instantiate (a0 := firstn # (m) (List.combine (map snd (Map.elements (elt:=valu) ms))
        (repeat (length (map snd (Map.elements (elt:=valu) ms))) [])) ++
      List.combine (skipn # (m) (map snd (Map.elements (elt:=valu) ms))) l5 ++
      repeat (# (LogLen xp) - Map.cardinal (elt:=valu) ms) ($0, nil)).
    admit. (* array match *)
    simpl.
    solve_lengths.

    step'.
    apply stars_or_left.
    cancel.
    instantiate (a := repeat (addr_per_block - length (Map.elements ms)) $0).
    rewrite firstn_oob.
    cancel.
    admit. (* empty array; append zeroes to argument of descriptor_to_valu *)
    solve_lengths.
    solve_lengths.
    rewrite Forall_forall; intuition.

    cancel.
    instantiate (l := repeat (# (LogLen xp)) ($0, nil)).
    solve_lengths.

    cancel.
    instantiate (a0 := (descriptor_to_valu (map fst (Map.elements (elt:=valu) ms)), l3) ::
      (firstn (Map.cardinal (elt:=valu) ms) (List.combine (map snd (Map.elements (elt:=valu) ms)) l1)) ++
      l2).
    admit. (* array match *)
    solve_lengths.

    cancel.
    instantiate (a0 := (descriptor_to_valu (map fst (Map.elements (elt:=valu) ms)), l3) ::
      (firstn (Map.cardinal (elt:=valu) ms) (List.combine (map snd (Map.elements (elt:=valu) ms)) l1)) ++
      l2).
    admit. (* array match *)
    solve_lengths.

    cancel.
    instantiate (l := repeat (# (LogLen xp)) ($0, nil)).
    solve_lengths.

    cancel.
    instantiate (a0 := l).
    admit. (* array match, more or less *)
    solve_lengths.

    instantiate (Goal9 := $0).
    instantiate (Goal11 := nil).
    instantiate (v := ($0, nil)).
    instantiate (v0 := ($0, nil)).
    instantiate (y := ($0, nil)).
    instantiate (y0 := ($0, nil)).

    solve_lengths.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush _ _) _) => apply flush_ok : prog.


  Definition apply_unsync T xp ms rx : prog T :=
    For i < $ (Map.cardinal ms)
    Ghost cur
    Loopvar _ <- tt
    Continuation lrx
    Invariant
      (LogCommit xp) |=> $1
      * log_rep xp cur ms
      * exists d, data_rep xp d
      * [[ replay' (skipn (wordToNat i) (Map.elements ms)) (map fst d) = cur ]]
      * [[ equal_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur (map fst d) $0 ]]
      * [[ nil_unless_in (map fst (Map.elements ms)) (map snd d) ]]
    OnCrash
      rep xp (CommittedTxn cur) ms
    Begin
      ArrayWrite $0 (sel (map fst (Map.elements ms)) i $0) $1 (sel (map snd (Map.elements ms)) i $0);;
      lrx tt
    Rof;;
    rx tt.

  Theorem apply_unsync_ok: forall xp ms,
    {< m,
    PRE    rep xp (CommittedTxn m) ms
    POST:r rep xp (AppliedUnsyncTxn m) ms
    CRASH  rep xp (CommittedTxn m) ms
    >} apply_unsync xp ms.
  Proof.
    unfold apply_unsync; log_unfold.
    hoare.
    admit.
    admit.
    admit.
    admit.
    rewrite <- H26.
    admit.
    admit.
    admit.
    admit.
    assert (goodSize addrlen (# (LogLen xp))) by (apply wordToNat_bound).
    rewrite skipn_oob in H23 by solve_lengths.
    rewrite skipn_oob in H24 by solve_lengths.
    admit.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply_unsync _ _) _) => apply apply_unsync_ok : prog.

  Definition apply_sync T xp ms rx : prog T :=
    For i < $ (Map.cardinal ms)
    Ghost cur
    Loopvar _ <- tt
    Continuation lrx
    Invariant
      (LogCommit xp) |=> $1
      * log_rep xp cur ms
      * exists cur_unflushed, data_rep xp (List.combine cur cur_unflushed)
      * [[ nil_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur_unflushed ]]
    OnCrash
      rep xp (AppliedUnsyncTxn cur) ms
    Begin
      ArraySync $0 (sel (map fst (Map.elements ms)) i $0) $1;;
      lrx tt
    Rof;;
    Write (LogCommit xp) $0;;
    rx tt.

  Theorem apply_sync_ok: forall xp ms,
    {< m,
    PRE    rep xp (AppliedUnsyncTxn m) ms
    POST:r rep xp (AppliedTxn m) ms
    CRASH  rep xp (AppliedUnsyncTxn m) ms \/ rep xp (AppliedTxn m) ms
    >} apply_sync xp ms.
  Proof.
    unfold apply_sync; log_unfold.
    hoare.
    admit.
    admit.
    instantiate (a0 := upd l1 (map fst (Map.elements ms) $[ m]) nil).
    admit.
    admit.
    admit.
    rewrite skipn_oob in H22 by solve_lengths.
    instantiate (y := $0).
    admit.
    apply pimpl_or_r; left; cancel.
    admit.
    admit.
    apply pimpl_or_r; left; cancel.
    admit.
 Qed.

  Hint Extern 1 ({{_}} progseq (apply_sync _ _) _) => apply apply_sync_ok : prog.

  Definition apply T xp ms rx : prog T :=
    apply_unsync xp ms;;
    apply_sync xp ms;;
    Sync (LogCommit xp);;
    rx tt.

  Theorem apply_ok: forall xp ms,
    {< m,
    PRE    rep xp (CommittedTxn m) ms
    POST:r rep xp (NoTransaction m) ms_empty
    CRASH  rep xp (CommittedTxn m) ms \/ rep xp (AppliedTxn m) ms \/ rep xp (NoTransaction m) ms_empty
    >} apply xp ms.
  Proof.
    unfold apply; log_unfold.
    hoare_unfold log_unfold.
    unfold avail_region; admit.
    apply pimpl_or_r; right; cancel; auto.
    apply pimpl_or_r; left; cancel; auto.
    apply pimpl_or_r; left; cancel; auto.
    (* true by [nil_unless_in _ l4] *) admit.
    apply pimpl_or_r; right; apply pimpl_or_r; left; cancel; auto.
    apply pimpl_or_r; left; cancel; auto.
    (* true by [equal_unless in _ ...l2... l3] and [replay ms l = replay ms l2] *) admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply _ _) _) => apply apply_ok : prog.

  Definition commit T xp (ms:memstate) rx : prog T :=
    ok <- flush xp ms;
    If (bool_dec ok true) {
      Write (LogCommit xp) $1;;
      Sync (LogCommit xp);;
      apply xp ms;;
      rx true
    } else {
      abort xp ms;;
      rx false
    }.


  Definition log_intact_either xp old cur :=
    (exists ms, rep xp (CommittedUnsyncTxn old cur) ms)%pred.

  (** The log is in a valid state which (after recovery) represents disk state [m] *)
  Definition log_intact xp m :=
    (exists ms, (rep xp (NoTransaction m) ms) \/
     (exists m', rep xp (ActiveTxn m m') ms) \/
     (rep xp (CommittedTxn m) ms) \/
     (rep xp (AppliedTxn m) ms))%pred.

  (** The log is in a valid state with (after recovery) represents either disk state [old] or [cur] *)
  Definition would_recover_either xp old cur :=
    (log_intact xp old \/ log_intact xp cur \/ log_intact_either xp old cur)%pred.

  Theorem commit_ok: forall xp ms,
    {< m1 m2,
     PRE    rep xp (ActiveTxn m1 m2) ms
     POST:r ([[ r = true ]] * rep xp (NoTransaction m2) ms_empty) \/
            ([[ r = false ]] * rep xp (NoTransaction m1) ms_empty)
     CRASH  would_recover_either xp m1 m2
    >} commit xp ms.
  Proof.
    unfold commit, would_recover_either, rep.
    step.
    unfold rep.
    cancel.
    cancel.
    shelve.
    unfold log_intact.
    cancel.
    cancel.
    Unshelve.
    step.
    unfold rep.
    step.
    shelve.

    (* we flushed, but crashed before the write of the commit record.
     * we need log_intact, but log_intact doesn't include flushedtxn 
     * daniel?   the left side is the post condition of flush, but doesn't imply
     * log_intact.
     *)


  Admitted.

(*
    hoare_unfold log_unfold.
    unfold equal_unless_in; intuition; auto.
    Ltac or_r := apply pimpl_or_r; right.
    Ltac or_l := apply pimpl_or_r; left.
    or_r; or_l; cancel.
    or_r; or_r; or_l; cancel.
    (* true by H17, H12 *) admit.
    auto.
    or_r; or_l; cancel.
    or_r; or_r; or_r; cancel.
    auto.
    or_l; cancel.
    or_l; cancel.
    admit.
  Qed.
*)

  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.

  Module MapProperties := WProperties Map.

  Definition read_log T (xp: xparams) rx : prog T :=
    d <- Read (LogDescriptor xp);
    let desc := valu_to_descriptor d in
    h <- Read (LogHeader xp);
    let len := (valu_to_header h) :-> "length" in
    log <- For i < len
    Ghost cur log_on_disk
    Loopvar log_prefix <- []
    Continuation lrx
    Invariant
      (LogCommit xp) |=> $1
      * exists old d, data_rep xp d
      * cur_rep old log_on_disk cur
      * log_rep xp old log_on_disk
        (* If something's in the transaction, it doesn't matter what state it's in on disk *)
      * [[ equal_unless_in (map fst (Map.elements log_on_disk)) (synced_list old) d ($0, nil) ]]
      * [[ log_prefix = firstn (wordToNat i) (Map.elements log_on_disk) ]]
    OnCrash
      rep xp (CommittedTxn cur) log_on_disk
    Begin
      v <- ArrayRead (LogData xp) i $1;
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
    rewrite header_valu_id in H. unfold mk_header, Rec.recget' in H. simpl in H.
    solve_lengths.
    (* true by [equal_unless_in _ ...d... l2] and [replay m l = replay m d] *) admit.
    rewrite header_valu_id in H. unfold mk_header, Rec.recget' in H. simpl in H.
    rewrite descriptor_valu_id. admit.
    hnf. intuition.
    admit.
    rewrite header_valu_id in *. unfold mk_header in *. admit.
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

  Hint Rewrite crash_xform_sep_star_dist crash_xform_or_dist crash_xform_exists_comm crash_xform_lift_empty 
    crash_invariant_ptsto : crash_xform.

  Hint Resolve crash_invariant_emp.

  Lemma crash_invariant_synced_array: forall l start stride,
    crash_xform (array start (List.combine l (repeat (length l) nil)) stride) =p=>
    array start (List.combine l (repeat (length l) nil)) stride.
  Proof.
    unfold array.
    induction l; intros; simpl; auto.
    autorewrite with crash_xform.
    cancel.
    auto.
  Qed.
  Hint Rewrite crash_invariant_synced_array : crash_xform.

  Ltac log_intact_unfold := unfold MEMLOG.would_recover_either, MEMLOG.log_intact, MEMLOG.log_intact_either.

  Ltac word_discriminate :=
    match goal with [ H: $ _ = $ _ |- _ ] => solve [
      apply natToWord_discriminate in H; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial]
    ] end.

  Ltac or_r := apply pimpl_or_r; right.
  Ltac or_l := apply pimpl_or_r; left.

  Theorem recover_ok: forall xp,
    {< m1 m2,
    PRE     crash_xform (would_recover_either xp m1 m2)
    POST:r  rep xp (NoTransaction m1) ms_empty \/ rep xp (NoTransaction m2) ms_empty
    CRASH   would_recover_either xp m1 m2
    >} recover xp.
  Proof.
    unfold recover; log_intact_unfold; log_unfold.
    intros.
    autorewrite with crash_xform.
    eapply pimpl_ok2; [ eauto with prog | ].
    intros; simpl.
    norm'l.
    unfold stars; simpl.
    rewrite sep_star_comm. rewrite <- emp_star.
    autorewrite with crash_xform.
    repeat rewrite sep_star_or_distr; repeat apply pimpl_or_l; norm'l; try word_discriminate;
      unfold stars; simpl; autorewrite with crash_xform.
    rewrite sep_star_comm; rewrite <- emp_star.
    repeat rewrite sep_star_or_distr; repeat apply pimpl_or_l; norm'l; unfold stars; simpl; autorewrite with crash_xform.
    + cancel.
      - step; step; try word_discriminate.
      - cancel.
        or_l; cancel.
      - step; step; try word_discriminate.
      - cancel.
        or_l; cancel.
    + cancel.
      - step; step; try word_discriminate.
        autorewrite with crash_xform.
        or_l; cancel.
      - cancel.
        autorewrite with crash_xform.
        or_l; cancel.
    + autorewrite with crash_xform.
      norm'l; unfold stars; simpl.
      autorewrite with crash_xform.
      cancel.
      - step.
        { eapply pimpl_ok2; [ eauto with prog | ]; intros.
          norm'l; unfold stars; simpl.
          autorewrite with crash_xform.
          log_unfold; rewrite crash_xform_array; cancel.
          + subst; cancel.
          + unfold equal_unless_in; intuition.
          + admit.
          + auto.
          + auto.
          + step_unfold log_unfold.
            - subst; eauto.
            - subst; eauto.
            - step.
              or_l; cancel.
              admit. (* by [possible_crash_list], [equal_unless_in], and [replay _ _ = replay _ _] hyps *)
            - or_l; cancel.
              or_r; or_r; or_l; cancel; auto.
              admit.
            - or_l; cancel.
              or_r; or_r; or_r; cancel; auto.
              admit.
            - or_l; cancel.
              or_l; cancel.
              admit.
          + cancel.
            or_l; cancel.
            or_r; or_r; or_l; cancel; auto.
            admit.
        }
        { step. }
      - autorewrite with crash_xform.
        cancel.
        or_l; cancel.
        rewrite crash_xform_array.
        or_r; or_r; or_l; cancel; auto.
        admit.
    + norm'l; unfold stars; simpl.
      autorewrite with crash_xform.
      cancel.
      - step; step; try word_discriminate.
        or_l; cancel.
        admit.
      - cancel.
        or_l; cancel.
        or_l; cancel.
        admit.
      - step; step_unfold log_unfold; try word_discriminate.
        { admit. }
        { step_unfold log_unfold; subst; eauto.
          + step.
            or_l; cancel.
            admit.
          + or_l; cancel.
            or_r; or_r; or_l; cancel; auto.
            admit.
          + or_l; cancel.
            or_r; or_r; or_r; cancel; auto.
            rewrite H16; auto.
          + or_l; cancel.
            or_l; cancel.
            rewrite H16; auto.
        }
        { or_l; cancel.
          or_r; or_r; or_l; cancel; auto.
          admit.
        }
      - cancel.
        or_l; cancel.
        or_r; or_r; or_l; cancel; auto.
        admit.
    + norm'l; unfold stars; simpl.
      autorewrite with crash_xform.
      cancel.
      - step; step; try word_discriminate.

  Admitted.

  Hint Extern 1 ({{_}} progseq (recover _) _) => apply recover_ok : prog.

  Definition read_array T xp a i stride ms rx : prog T :=
    read xp (a ^+ i ^* stride) ms rx.

  Definition write_array T xp a i stride v ms rx : prog T :=
    write xp (a ^+ i ^* stride) v ms rx.

  Theorem read_array_ok : forall xp ms a i stride,
    {< mbase m vs,
    PRE    rep xp (ActiveTxn mbase m) ms *
           [[ exists F', (array a vs stride * F')%pred (list2mem m) ]] *
           [[ wordToNat i < length vs ]]
    POST:r [[ r = sel vs i $0 ]] * rep xp (ActiveTxn mbase m) ms
    CRASH  rep xp (ActiveTxn mbase m) ms
    >} read_array xp a i stride ms.
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
    step.
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

  Theorem write_array_ok : forall xp a i stride v ms,
    {< mbase m vs F',
    PRE      rep xp (ActiveTxn mbase m) ms
           * [[ (array a vs stride * F')%pred (list2mem m) ]]
           * [[ wordToNat i < length vs ]]
    POST:ms' exists m', rep xp (ActiveTxn mbase m') ms'
           * [[ (array a (Array.upd vs i v) stride * F')%pred (list2mem m') ]]
    CRASH  exists m' ms', rep xp (ActiveTxn mbase m') ms'
    >} write_array xp a i stride v ms.
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
  Hint Extern 0 (okToUnify (rep _ _ ?a) (rep _ _ ?a)) => constructor : okToUnify.

End MEMLOG.



Global Opaque MEMLOG.write.

