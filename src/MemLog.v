Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Classes.SetoidTactics.
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
Require Import Cache.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

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

| FlushedUnsyncTxn (old : diskstate) (cur : diskstate)
(* A transaction has been flushed to the log, but not sync'ed or
 * committed yet. *)

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
  LogCache : Cache.xparams;

  DataStart : addr;
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

  Lemma descriptor_to_valu_zeroes: forall l n,
    descriptor_to_valu (l ++ repeat $0 n) = descriptor_to_valu l.
  Proof.
    unfold descriptor_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite descriptor_sz_ok.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    apply Rec.to_word_append_zeroes.
  Qed.

  Definition indomain' (a : addr) (m : diskstate) := wordToNat a < length m.

  (* Check that the state is well-formed *)
  Definition valid_entries m (ms : memstate) :=
    forall a v, Map.MapsTo a v ms -> indomain' a m.

  Definition valid_size xp (ms : memstate) :=
    Map.cardinal ms <= wordToNat (LogLen xp).

  (* Replay the state in memory *)
  Definition replay' V (l : list (addr * V)) (m : list V) : list V :=
    fold_right (fun p m' => upd m' (fst p) (snd p)) m l.

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

  Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).

  Definition data_rep (xp: xparams) (m: list valuset) : @pred addr (@weq addrlen) valuset :=
    array (DataStart xp) m $1.

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

  (* XXX DRY? *)
  Definition log_rep_unsynced xp m (ms : memstate) : @pred addr (@weq addrlen) valuset :=
     ((LogHeader xp) |~> (header_to_valu (mk_header (Map.cardinal ms))) *
      [[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest,
      (LogDescriptor xp) |~> (descriptor_to_valu (map fst (Map.elements ms) ++ rest)) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      exists unsynced,
      array (LogData xp) (List.combine (map snd (Map.elements ms)) unsynced) $1 *
      [[ length unsynced = Map.cardinal ms ]] *
      avail_region (LogData xp ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms))%pred.


  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred addr (@weq addrlen) valuset :=
    [[ cur = replay ms old ]]%pred.

  Definition nil_unless_in (ms: list addr) (l: list (list valu)) :=
    forall a, ~ In a ms -> sel l a nil = nil.

  Definition equal_unless_in T (ms: list addr) (m1: list T) (m2: list T) (def: T) :=
    length m1 = length m2 /\ forall n, (~ goodSize addrlen n \/ ~ In ($ n) ms) -> selN m1 n def = selN m2 n def.

  Definition rep_inner xp (st: logstate) (ms: memstate) :=
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

    | FlushedUnsyncTxn old cur =>
      (LogCommit xp) |=> $0
    * data_rep xp (synced_list old)
    * log_rep_unsynced xp old ms
    * cur_rep old ms cur

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

  Definition rep xp st mscs := (exists d,
    BUFCACHE.rep (snd mscs) d * [[ rep_inner xp st (fst mscs) d ]])%pred.

  (** The log is in a valid state which (after recovery) represents disk state [m] *)
  (* (Only states relevant for the public interface are included *)
  (* XXX remove, since [recover] deals with [would_recover_either] instead? *)
  Definition log_intact xp m :=
    (exists mscs,
     (rep xp (NoTransaction m) mscs) \/
     (exists m', rep xp (ActiveTxn m m') mscs) \/
     (rep xp (CommittedTxn m) mscs) \/
     (rep xp (AppliedTxn m) mscs))%pred.

  Definition init_cs T xp cs rx : prog T :=
    cs <- BUFCACHE.write (LogCache xp) (LogCommit xp) $0 cs;
    cs <- BUFCACHE.sync (LogCache xp) (LogCommit xp) cs;
    rx (ms_empty, cs).

  Ltac log_unfold := unfold rep, rep_inner, data_rep, cur_rep, log_rep, log_rep_unsynced, valid_size, synced_list.

  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _ _) (data_rep _)) => constructor : okToUnify.

  (* XXX actually okay? *)
  Local Hint Extern 0 (okToUnify (array (DataStart _) _ _) (array (DataStart _) _ _)) => constructor : okToUnify.

  Definition log_uninitialized xp old :=
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
     [[ goodSize addrlen (# (LogData xp) + # (LogLen xp)) ]] *
     data_rep xp (synced_list old) *
     avail_region (LogData xp) (wordToNat (LogLen xp)) *
     (LogCommit xp) |->? *
     (LogDescriptor xp) |->? *
     (LogHeader xp) |->?)%pred.

  Theorem init_cs_ok : forall xp cs,
    {< old d,
    PRE       BUFCACHE.rep cs d * [[ (log_uninitialized xp old) d ]]
    POST:mscs rep xp (NoTransaction old) mscs
    CRASH     exists cs' d', BUFCACHE.rep cs' d' * [[ log_uninitialized xp old d' ]]
    >} init_cs xp cs.
  Proof.
    unfold init_cs, log_uninitialized; log_unfold.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (init_cs _ _) _) => apply init_cs_ok : prog.

  Definition init T xp rx : prog T :=
    cs <- BUFCACHE.init (LogCache xp);
    let2 (ms, cs) <- init_cs xp cs;
    rx (ms, cs).

  Theorem init_ok : forall xp,
    {< old,
    PRE       log_uninitialized xp old
    POST:mscs rep xp (NoTransaction old) mscs
    CRASH     log_uninitialized xp old \/
              (exists cs' d', BUFCACHE.rep cs' d' * [[ log_uninitialized xp old d' ]])
    >} init xp.
  Proof.
    unfold init.
    (* XXX the hoare triple for [BUFCACHE.init] needs to be "frameless" *)
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _) _) => apply init_ok : prog.

  Definition begin T xp (cs : cachestate) rx : prog T :=
    cs <- BUFCACHE.write (LogCache xp) (LogHeader xp) (header_to_valu (mk_header 0)) cs;
    rx (ms_empty, cs).

  Theorem begin_ok: forall xp cs,
    {< m,
    PRE    rep xp (NoTransaction m) (ms_empty, cs)
    POST:r rep xp (ActiveTxn m m) r
    CRASH  exists mscs', rep xp (NoTransaction m) mscs' \/ rep xp (ActiveTxn m m) mscs'
    >} begin xp cs.
  Proof.
    unfold begin; log_unfold.
    hoare.
    unfold valid_entries; intuition; inversion H.
  Qed.

  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.

  Definition abort T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    cs <- BUFCACHE.write (LogCache xp) (LogHeader xp) (header_to_valu (mk_header 0)) cs;
    rx (ms_empty, cs).

  Theorem abort_ok : forall xp mscs,
    {< m1 m2,
    PRE    rep xp (ActiveTxn m1 m2) mscs
    POST:r rep xp (NoTransaction m1) r
    CRASH  exists mscs', rep xp (ActiveTxn m1 m2) mscs' \/ rep xp (NoTransaction m1) mscs'
    >} abort xp mscs.
  Proof.
    unfold abort; log_unfold.
    destruct mscs as [ms cs].
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.

  Ltac word2nat_clear := try clear_norm_goal; repeat match goal with
    | [ H : forall _, {{ _ }} _ |- _ ] => clear H
    | [ H : _ =p=> _ |- _ ] => clear H
    end.

  Lemma skipn_1_length': forall T (l: list T),
    length (match l with [] => [] | _ :: l' => l' end) = length l - 1.
  Proof.
    destruct l; simpl; omega.
  Qed.

  Hint Rewrite app_length firstn_length skipn_length combine_length map_length repeat_length length_upd
    skipn_1_length' : lengths.

  Ltac solve_lengths' :=
    repeat (progress (autorewrite with lengths; repeat rewrite Nat.min_l by solve_lengths'; repeat rewrite Nat.min_r by solve_lengths'));
    simpl; try word2nat_solve.

  Ltac solve_lengths_prepare :=
    intros; word2nat_clear; simpl;
    (* Stupidly, this is like 5x faster than [rewrite Map.cardinal_1 in *] ... *)
    repeat match goal with
    | [ H : context[Map.cardinal] |- _ ] => rewrite Map.cardinal_1 in H
    | [ |- context[Map.cardinal] ] => rewrite Map.cardinal_1
    end.

  Ltac solve_lengths_prepped :=
    try (match goal with
      | [ |- context[{{ _ }} _] ] => fail 1
      | [ |- _ =p=> _ ] => fail 1
      | _ => idtac
      end;
      word2nat_clear; word2nat_simpl; word2nat_rewrites; solve_lengths').

  Ltac solve_lengths := solve_lengths_prepare; solve_lengths_prepped.


  Definition KIn V := InA (@Map.eq_key V).
  Definition KNoDup V := NoDupA (@Map.eq_key V).

  Lemma replay_sel_other : forall a ms m def,
    ~ Map.In a ms -> selN (replay ms m) (wordToNat a) def = selN m (wordToNat a) def.
  Proof.
    (* intros; rename a into a'; remember (wordToNat a') as a. *)
    intros a ms m def HnotIn.
    destruct (MapFacts.elements_in_iff ms a) as [_ Hr].
    assert (not (exists e : valu, InA (Map.eq_key_elt (elt:=valu))
      (a, e) (Map.elements ms))) as HnotElem by auto; clear Hr HnotIn.
    remember (Map.eq_key_elt (elt:=valu)) as eq in *.
    unfold replay, replay'.
    remember (Map.elements ms) as elems in *.
    assert (forall x y, InA eq (x,y) elems -> x <> a) as Hneq. {
      intros x y Hin.
      destruct (Addr_as_OT.eq_dec a x); [|intuition].
      destruct HnotElem; exists y; subst; auto.
    }
    clear Heqelems HnotElem.
    induction elems as [|p]; [reflexivity|].
    rewrite <- IHelems; clear IHelems; [|intros; eapply Hneq; right; eauto].
    destruct p as [x y]; simpl.
    assert (x <> a) as Hsep. {
      apply (Hneq x y); left; subst eq. 
      apply Equivalence.equiv_reflexive_obligation_1.
      apply MapProperties.eqke_equiv.
    }
    eapply (selN_updN_ne _ y);
      unfold not; intros; destruct Hsep; apply wordToNat_inj; trivial.
  Qed.

  Lemma replay'_length : forall V (l:list (addr * V)) (m:list V),
      length m = length (replay' l m).
    induction l; [trivial|]; intro.
    unfold replay'; simpl.
    rewrite length_upd.
    eapply IHl.
  Qed.
  Hint Rewrite replay'_length : lengths.

  Lemma InA_NotInA_neq : forall T eq, Equivalence eq -> forall l (x y:T),
      InA eq x l -> ~ (InA eq y l) -> ~ eq x y.
    intros until 0; intros Eqeq; intros until 0; intros HIn HnotIn.
    rewrite InA_altdef, Exists_exists in *.
    intro Hcontra; apply HnotIn; clear HnotIn.
    elim HIn; clear HIn; intros until 0; intros HIn.
    destruct HIn as [HIn Heq_x_x0].
    exists x0. split; [apply HIn|].
    etransitivity; eauto; symmetry; auto.
  Qed.

  Lemma replay'_sel : forall V a (v: V) l m def,
    KNoDup l -> In (a, v) l -> wordToNat a < length m -> sel (replay' l m) a def = v.
  Proof.
    intros until 0; intros HNoDup HIn Hbounds.

    induction l as [|p]; [inversion HIn|]; destruct p as [x y]; simpl.
    destruct HIn. {
      clear IHl.
      injection H; clear H;
        intro H; rewrite H in *; clear H;
        intro H; rewrite H in *; clear H.
      apply selN_updN_eq. rewrite <- replay'_length; assumption.
    } {
      assert (x <> a) as Hneq. {
        inversion HNoDup. 
        assert (InA eq (a,v) l). {
          apply In_InA; subst; eauto using MapProperties.eqk_equiv.
        }
      remember (Map.eq_key (elt:=V)) as eq_key in *.
      assert (forall a b, eq a b -> eq_key a b) as Heq_eqk by (
        intros; subst; apply MapProperties.eqk_equiv).
      assert (forall a l, InA eq a l -> InA eq_key a l) as HIn_eq_eqk by (
        intros until 0; intro HInAeq; induction HInAeq; [subst|right]; auto).
      assert (@Equivalence (Map.key*V) eq_key) as Eqeq by (
        subst eq_key; apply MapProperties.eqk_equiv).
      intro Hcontra; destruct
        (@InA_NotInA_neq (Map.key*V) eq_key Eqeq l (a,v) (x,y) (HIn_eq_eqk _ _ H4) H2).
      subst; unfold Map.eq_key; reflexivity.
      }
      unfold sel, upd in *.
      rewrite selN_updN_ne, IHl;
        try trivial;
        match goal with
          | [ H: KNoDup (?a::?l) |- KNoDup ?l ] => inversion H; assumption
          | [ Hneq: ?a<>?b |- wordToNat ?a <> wordToNat ?b] =>
            unfold not; intro Hcontra; destruct (Hneq (wordToNat_inj _  _ Hcontra))
        end.
    }
  Qed.

  Lemma InA_eqke_In : forall V a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
  Proof.
    intros.
    induction l.
    inversion H.
    inversion H.
    inversion H1.
    destruct a0; simpl in *; subst.
    left; trivial.
    simpl.
    right.
    apply IHl; auto.
  Qed.

  Lemma mapsto_In : forall V a (v: V) ms,
    Map.MapsTo a v ms -> In (a, v) (Map.elements ms).
  Proof.
    intros.
    apply Map.elements_1 in H.
    apply InA_eqke_In; auto.
  Qed.

  Lemma replay_sel_in : forall a v ms m def,
    # a < length m -> Map.MapsTo a v ms -> selN (replay ms m) (wordToNat a) def = v.
  Proof.
    intros.
    apply mapsto_In in H0.
    unfold replay.
    apply replay'_sel.
    apply Map.elements_3w.
    auto.
    auto.
  Qed.

  Lemma replay_sel_invalid : forall a ms m def,
    ~ goodSize addrlen a -> selN (replay ms m) a def = selN m a def.
  Proof.
    intros; unfold goodSize in *.
    destruct (lt_dec a (length m)); [|
      repeat (rewrite selN_oob); unfold replay;
        try match goal with [H: _ |- length (replay' _ _) <= a]
            => rewrite <- replay'_length end;
        auto; omega].
    unfold replay, replay'.
    induction (Map.elements ms); [reflexivity|].
    rewrite <- IHl0; clear IHl0; simpl.
    unfold upd.
    rewrite selN_updN_ne.
    trivial.
    destruct a0.
    unfold Map.key in k.
    intro Hf.
    word2nat_auto.
  Qed.

  Lemma replay_length : forall ms m,
    length (replay ms m) = length m.
  Proof.
    intros.
    unfold replay.
    rewrite <- replay'_length.
    trivial.
  Qed.
  Hint Rewrite replay_length : lengths.

  Lemma replay_add : forall a v ms m,
    replay (Map.add a v ms) m = upd (replay ms m) a v.
  Proof.
    intros.
    (* Let's show that the lists are equal because [sel] at any index [pos] gives the same valu *)
    eapply list_selN_ext.
    rewrite length_upd.
    repeat rewrite replay_len.
    trivial.
    solve_lengths.
    intros.
    destruct (lt_dec pos (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace pos with (wordToNat (natToWord addrlen (pos))) by word2nat_auto.
      destruct (weq ($ pos) a).
      + (* [pos] is [a], the address we're updating *)
        erewrite replay_sel_in.
        reflexivity.
        autorewrite with lengths in *.
        solve_lengths.
        instantiate (default := $0).
        subst.
        unfold upd.
        rewrite selN_updN_eq.
        apply Map.add_1.
        trivial.
        rewrite replay_length in *.
        word2nat_auto.

      + (* [pos] is another address *)
        unfold upd.
        rewrite selN_updN_ne by word2nat_auto.

        case_eq (Map.find $ pos ms).

        (* [pos] is in the transaction *)
        intros w Hf.
        autorewrite with lengths in *.
        erewrite replay_sel_in.
        reflexivity.
        solve_lengths.
        apply Map.find_2 in Hf.
        erewrite replay_sel_in.
        apply Map.add_2.
        unfold not in *; intros; solve [auto].
        eauto.
        solve_lengths.
        eauto.

        (* [pos] is not in the transaction *)
        Ltac wneq H := intro HeqContra; symmetry in HeqContra; apply H; auto.
        intro Hf; 
          repeat (erewrite replay_sel_other);
          try trivial;
          intro HIn; destruct HIn as [x HIn];
          try apply Map.add_3 in HIn;
          try apply Map.find_1 in HIn;
          try wneq n;
          replace (Map.find $ (pos) ms) with (Some x) in Hf; inversion Hf.
    - (* [pos] is an invalid address *)
      rewrite replay_sel_invalid by auto.
      unfold upd.
      rewrite selN_updN_ne by (
        generalize (wordToNat_bound a); intro Hb;
        omega).
      rewrite replay_sel_invalid by auto; trivial.
  Qed.

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


  Lemma upd_prepend_length: forall l a v, length (upd_prepend l a v) = length l.
  Proof.
    intros; unfold upd_prepend.
    solve_lengths.
  Qed.
  Hint Rewrite upd_prepend_length : lengths.

  Definition write T (xp : xparams) a v (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    rx (Map.add a v ms, cs).

  Theorem write_ok : forall xp mscs a v,
    {< m1 m2 F' v0,
    PRE        rep xp (ActiveTxn m1 m2) mscs * [[ (F' * a |-> v0)%pred (list2mem m2) ]]
    POST:mscs' exists m', rep xp (ActiveTxn m1 m') mscs' *
               [[(F' * a |-> v)%pred (list2mem m') ]]
    CRASH      exists m' mscs', rep xp (ActiveTxn m1 m') mscs'
    >} write xp a v mscs.
  Proof.
    unfold write; log_unfold.
    destruct mscs as [ms cs].
    hoare.

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

  Definition read T (xp: xparams) a (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    match Map.find a ms with
    | Some v =>
      rx ((ms, cs), v)
    | None =>
      let2 (cs, v) <- BUFCACHE.read_array (LogCache xp) (DataStart xp) a cs;
      rx ((ms, cs), v)
    end.


  Theorem read_ok: forall xp mscs a,
    {< m1 m2 v,
    PRE            rep xp (ActiveTxn m1 m2) mscs *
                   [[ exists F, (F * a |-> v) (list2mem m2) ]]
    POST:(mscs',r) rep xp (ActiveTxn m1 m2) mscs' *
                   [[ r = v ]]
    CRASH          exists mscs', rep xp (ActiveTxn m1 m2) mscs'
    >} read xp a mscs.
  Proof.
    unfold read; log_unfold.
    destruct mscs as [ms cs]; simpl; intros.

    case_eq (Map.find a ms); hoare.

    eapply list2mem_sel with (def := $0) in H1.
    apply Map.find_2 in H.
    eapply replay_sel_in in H.
    rewrite <- H.
    rewrite H1.
    reflexivity.
    unfold valid_entries in *.
    eauto.

    solve_lengths.
    unfold indomain' in *.
    eauto.

    unfold sel. rewrite selN_combine.
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

  Definition flush_unsync T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    cs <- BUFCACHE.write (LogCache xp) (LogHeader xp)
      (header_to_valu (mk_header (Map.cardinal ms))) cs;
    cs <- BUFCACHE.write (LogCache xp) (LogDescriptor xp)
      (descriptor_to_valu (map fst (Map.elements ms))) cs;
    cs <- For i < $ (Map.cardinal ms)
    Ghost old crash
    Loopvar cs <- cs
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ ((LogCommit xp) |=> $0
          * data_rep xp (synced_list old)
          * (LogHeader xp) |~> header_to_valu (mk_header (Map.cardinal ms))
          * (LogDescriptor xp) |~> descriptor_to_valu (map fst (Map.elements ms))
          * exists l', [[ length l' = # i ]]
          * array (LogData xp) (firstn (# i) (List.combine (map snd (Map.elements ms)) l')) $1
          * avail_region (LogData xp ^+ i) (# (LogLen xp) - # i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.write_array (LogCache xp) (LogData xp ^+ i) $0
        (sel (map snd (Map.elements ms)) i $0) cs;
      lrx cs
    Rof;
    rx (ms, cs).

  Definition flush_sync T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    cs <- BUFCACHE.sync (LogCache xp) (LogHeader xp) cs;
    cs <- BUFCACHE.sync (LogCache xp) (LogDescriptor xp) cs;
    cs <- For i < $ (Map.cardinal ms)
    Ghost old crash
    Loopvar cs <- cs
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ ((LogCommit xp) |=> $0
          * data_rep xp (synced_list old)
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal ms))
          * exists rest, (LogDescriptor xp) |=> descriptor_to_valu (map fst (Map.elements ms) ++ rest)
          * [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]]
          * array (LogData xp) (firstn (# i) (synced_list (map snd (Map.elements ms)))) $1
          * exists l', [[ length l' = Map.cardinal ms - # i ]]
          * array (LogData xp ^+ i) (List.combine (skipn (# i) (map snd (Map.elements ms))) l') $1
          * avail_region (LogData xp ^+ $ (Map.cardinal ms)) (# (LogLen xp) - Map.cardinal ms))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.sync_array (LogCache xp) (LogData xp ^+ i) $0 cs;
      lrx cs
    Rof;
    rx (ms, cs).

  Definition flush T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    If (lt_dec (wordToNat (LogLen xp)) (Map.cardinal ms)) {
      rx ((ms, cs), false)
    } else {
      (* Write... *)
      let2 (ms, cs) <- flush_unsync xp (ms, cs);
      (* ... and sync *)
      let2 (ms, cs) <- flush_sync xp (ms, cs);
      rx ((ms, cs), true)
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

  Ltac assert_lte a b := let H := fresh in assert (a <= b)%word as H by
      (word2nat_simpl; repeat rewrite wordToNat_natToWord_idempotent'; word2nat_solve); clear H.

  Ltac array_sort' :=
    eapply pimpl_trans; rewrite emp_star; [ apply pimpl_refl |];
    repeat rewrite <- sep_star_assoc;
    match goal with
    | [ |- ?p =p=> ?p ] => fail 1
    | _ => idtac
    end;
    repeat match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      assert_lte a2 a1;
      try (assert_lte a1 a2; fail 1); (* don't swap forever if two terms are equal *)
      rewrite (sep_star_assoc p (array a1 l1 s));
      rewrite (sep_star_comm (array a1 l1 s)); rewrite <- (sep_star_assoc p (array a2 l2 s))
    end;
    (* make sure we can prove it's sorted *)
    match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      (assert_lte a1 a2; fail 1) || fail 2
    | _ => idtac
    end;
    eapply pimpl_trans; rewrite <- emp_star; [ apply pimpl_refl |].

  Ltac array_sort :=
    word2nat_clear; word2nat_auto; [ array_sort' | .. ].

  Lemma singular_array: forall T a (v: T),
    a |-> v <=p=> array a [v] $1.
  Proof.
    intros. split; cancel.
  Qed.

  Lemma equal_arrays: forall T (l1 l2: list T) a1 a2,
    a1 = a2 -> l1 = l2 -> array a1 l1 $1 =p=> array a2 l2 $1.
  Proof.
    cancel.
  Qed.

  Lemma array_app: forall T (l1 l2: list T) a1 a2,
    a2 = a1 ^+ $ (length l1) ->
    array a1 l1 $1 * array a2 l2 $1 <=p=> array a1 (l1 ++ l2) $1.
  Proof.
    induction l1.
    intros; word2nat_auto; split; cancel; apply equal_arrays; word2nat_auto.
    intros; simpl; rewrite sep_star_assoc. rewrite IHl1. auto.
    simpl in *.
    word2nat_simpl. rewrite <- plus_assoc. auto.
  Qed.

  Ltac rewrite_singular_array :=
    repeat match goal with
    | [ |- context[@ptsto addr (@weq addrlen) ?V ?a ?v] ] =>
      setoid_replace (@ptsto addr (@weq addrlen) V a v)%pred
      with (array a [v] $1) by (apply singular_array)
    end.

  Lemma make_unifiable: forall a l s,
    array a l s <=p=> unifiable_array a l s.
  Proof.
    split; cancel.
  Qed.

  Ltac array_cancel_trivial :=
    fold unifiable_array;
    match goal with
    | [ |- _ =p=> ?x * unifiable_array ?a ?l ?s ] => first [ is_evar x | is_var x ]; unfold unifiable_array; rewrite (make_unifiable a l s)
    | [ |- _ =p=> unifiable_array ?a ?l ?s * ?x ] => first [ is_evar x | is_var x ]; unfold unifiable_array; rewrite (make_unifiable a l s)
    end;
    solve [ cancel ].

  Ltac array_match :=
    unfold unifiable_array in *;
    match goal with (* early out *)
    | [ |- _ =p=> _ * array _ _ _ ] => idtac
    | [ |- _ =p=> _ * _ |-> _ ] => idtac
    | [ |- _ =p=> array _ _ _ ] => idtac
    end;
    solve_lengths_prepare;
    rewrite_singular_array;
    array_sort;
    repeat (rewrite array_app; [ | solve_lengths_prepped ]); [ repeat rewrite <- app_assoc | .. ];
    try apply pimpl_refl;
    try (apply equal_arrays; [ solve_lengths_prepped | try reflexivity ]).

  Ltac try_arrays_lengths := try (array_cancel_trivial || array_match); solve_lengths_prepped.

  (* Slightly different from CPDT [equate] *)
  Ltac equate x y :=
    let tx := type of x in
    let ty := type of y in
    let H := fresh in
    assert (x = y) as H by reflexivity; clear H.

  Ltac split_pair_list_evar :=
    match goal with
    | [ |- context [ ?l ] ] =>
      is_evar l;
      match type of l with
      | list (?A * ?B) =>
        let l0 := fresh in
        let l1 := fresh in
        evar (l0 : list A); evar (l1 : list B);
        let l0' := eval unfold l0 in l0 in
        let l1' := eval unfold l1 in l1 in
        equate l (@List.combine A B l0' l1');
        clear l0; clear l1
      end
    end.

  Theorem combine_upd: forall A B i a b (va: A) (vb: B),
    List.combine (upd a i va) (upd b i vb) = upd (List.combine a b) i (va, vb).
  Proof.
    unfold upd; intros.
    apply combine_updN.
  Qed.

  Lemma updN_0_skip_1: forall A l (a: A),
    length l > 0 -> updN l 0 a = a :: skipn 1 l .
  Proof.
    intros; destruct l.
    simpl in H. omega.
    reflexivity.
  Qed.

  Lemma cons_app: forall A l (a: A),
    a :: l = [a] ++ l.
  Proof.
    auto.
  Qed.

  Lemma firstn_app_l: forall A (al ar: list A) n,
    n <= length al ->
    firstn n (al ++ ar) = firstn n al.
  Proof.
    induction al.
    intros; simpl in *. inversion H. auto.
    intros; destruct n; simpl in *; auto.
    rewrite IHal by omega; auto.
  Qed.

  Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
    List.combine (map fst l) (map snd l) = l.
  Proof.
    induction l.
    auto.
    simpl; rewrite IHl; rewrite <- surjective_pairing; auto.
  Qed.

  Lemma skipn_skipn: forall A n m (l: list A),
    skipn n (skipn m l) = skipn (n + m) l.
  Proof.
    admit.
  Qed.

  Hint Rewrite firstn_combine_comm skipn_combine_comm selN_combine
    removeN_combine List.combine_split combine_nth combine_one updN_0_skip_1 skipn_selN : lists.
  Hint Rewrite <- combine_updN combine_upd combine_app : lists.

  Ltac split_pair_list_vars :=
    set_evars;
    repeat match goal with
    | [ H : list (?A * ?B) |- _ ] =>
      match goal with
      | |- context[ List.combine (map fst H) (map snd H) ] => fail 1
      | _ => idtac
      end;
      rewrite <- combine_map_fst_snd with (l := H)
    end;
    subst_evars.

  Ltac split_lists :=
    unfold upd_prepend, upd_sync;
    unfold sel, upd;
    repeat split_pair_list_evar;
    split_pair_list_vars;
    autorewrite with lists; [ f_equal | .. ].

  Theorem flush_unsync_ok : forall xp mscs,
    {< m1 m2,
    PRE        rep xp (ActiveTxn m1 m2) mscs *
               [[ Map.cardinal (fst mscs) <= wordToNat (LogLen xp) ]]
    POST:mscs' rep xp (FlushedUnsyncTxn m1 m2) mscs'
    CRASH      exists mscs', rep xp (ActiveTxn m1 m2) mscs'
    >} flush_unsync xp mscs.
  Proof.
    unfold flush_unsync; log_unfold; unfold avail_region.
    destruct mscs as [ms cs].
    intros.
    solve_lengths_prepare.
    hoare_with idtac try_arrays_lengths.
    instantiate (a3 := nil); auto.
    split_lists.
    rewrite cons_app.
    rewrite app_assoc.
    erewrite firstn_plusone_selN.
    reflexivity.
    solve_lengths.
    simpl.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    instantiate (a4 := l2 ++ [valuset_list (selN l3 0 ($0, nil))]).
    simpl.
    rewrite firstn_app_l by solve_lengths.
    repeat erewrite selN_map by solve_lengths.
    rewrite <- surjective_pairing.
    rewrite selN_app2.
    rewrite H18.
    rewrite Nat.sub_diag.
    reflexivity.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract (case_eq l3; intros; subst; word2nat_clear; simpl in *; solve_lengths).

    solve_lengths_prepare.
    instantiate (a2 := repeat $0 (addr_per_block - length (Map.elements ms))).
    rewrite descriptor_to_valu_zeroes.
    rewrite firstn_oob by solve_lengths.
    fold unifiable_array.
    cancel.
    solve_lengths.
    solve_lengths.
    rewrite Forall_forall; intuition.
    abstract solve_lengths.
    abstract solve_lengths.
    instantiate (a0 := m); pred_apply; cancel.
    Unshelve.
    auto.
    constructor.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush_unsync _ _) _) => apply flush_unsync_ok : prog.

  Theorem flush_sync_ok : forall xp mscs,
    {< m1 m2,
    PRE        rep xp (FlushedUnsyncTxn m1 m2) mscs *
               [[ Map.cardinal (fst mscs) <= wordToNat (LogLen xp) ]]
    POST:mscs' rep xp (FlushedTxn m1 m2) mscs'
    CRASH      exists mscs', rep xp (ActiveTxn m1 m2) mscs'
    >} flush_sync xp mscs.
  Proof.
    unfold flush_sync; log_unfold; unfold avail_region.
    destruct mscs as [ms cs].
    intros.
    solve_lengths_prepare.
    hoare_with ltac:(unfold upd_sync) try_arrays_lengths.
    split_lists.
    rewrite skipn_skipn.
    rewrite (plus_comm 1).
    rewrite Nat.add_0_r.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    reflexivity.
    solve_lengths.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    rewrite repeat_selN.
    reflexivity.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    solve_lengths_prepare.
    rewrite skipn_oob by solve_lengths.
    rewrite firstn_oob by solve_lengths.
    cancel.
    solve_lengths.
    solve_lengths.
    instantiate (a0 := m); pred_apply; cancel.
    array_match.
    abstract solve_lengths.
    Unshelve.
    auto.
    constructor.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush_sync _ _) _) => apply flush_sync_ok : prog.

  Theorem flush_ok : forall xp mscs,
    {< m1 m2,
    PRE            rep xp (ActiveTxn m1 m2) mscs
    POST:(mscs',r) ([[ r = true ]] * rep xp (FlushedTxn m1 m2) mscs') \/
                   ([[ r = false ]] * rep xp (ActiveTxn m1 m2) mscs')
    CRASH          exists mscs', rep xp (ActiveTxn m1 m2) mscs'
    >} flush xp mscs.
  Proof.
    unfold flush; log_unfold.
    destruct mscs as [ms cs].
    intros.
    abstract hoare_unfold log_unfold.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush _ _) _) => apply flush_ok : prog.

  Lemma equal_unless_in_trans: forall T m a b c (def: T),
    equal_unless_in m a b def -> equal_unless_in m b c def -> equal_unless_in m a c def.
  Proof.
    unfold equal_unless_in; intuition.
    rewrite H2 by auto. apply H3; auto.
    rewrite H2 by auto. apply H3; auto.
  Qed.

  Lemma equal_unless_in_comm: forall T m a b (def: T),
    equal_unless_in m a b def -> equal_unless_in m b a def.
  Proof.
    unfold equal_unless_in; intuition. rewrite H1 by auto; reflexivity.
    rewrite H1 by auto; reflexivity.
  Qed.

  Lemma In_MapIn: forall V a (ms: Map.t V), In a (map fst (Map.elements ms)) <-> Map.In a ms.
    intuition.
    apply MapFacts.elements_in_iff.
    apply in_map_iff in H.
    destruct H.
    intuition; subst.
    eexists.
    apply InA_alt.
    eexists.
    intuition; eauto.
    constructor; simpl; auto.

    apply MapFacts.elements_in_iff in H.
    apply in_map_iff.
    destruct H.
    apply InA_alt in H.
    destruct H.
    intuition.
    eexists.
    intuition; eauto.
    destruct x0; inversion H0; auto.
  Qed.

  Lemma equal_unless_in_replay_eq: forall ms a b def,
    replay ms a = replay ms b <-> equal_unless_in (map fst (Map.elements ms)) a b def.
  Proof.
    unfold equal_unless_in, sel.
    intuition.
    {
    erewrite <- replay_length with (m := a).
    erewrite <- replay_length with (m := b).
    f_equal; eauto.
    }
    {
      erewrite <- replay_sel_invalid with (m := a).
      erewrite <- replay_sel_invalid with (m := b).
      f_equal; eauto.
      word2nat_auto.
      word2nat_auto.
    }
    {
    destruct (lt_dec n (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace n with (wordToNat (natToWord addrlen (n))) by word2nat_auto.
      erewrite <- replay_sel_other.
      erewrite <- replay_sel_other with (m := b).
      f_equal; eauto.
      intro Hi; apply In_MapIn in Hi; tauto.
      intro Hi; apply In_MapIn in Hi; tauto.
    - erewrite <- replay_sel_invalid with (m := a).
      erewrite <- replay_sel_invalid with (m := b).
      f_equal; eauto.
      word2nat_auto.
      word2nat_auto.
    }
    {
    eapply list_selN_ext.
    repeat rewrite replay_length; auto.
    intros.
    destruct (lt_dec pos (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace pos with (wordToNat (natToWord addrlen (pos))) by word2nat_auto.
      case_eq (Map.find $ pos ms).
      + intros w Hf. apply Map.find_2 in Hf. apply replay_sel_in.
        autorewrite with lengths in *.
        solve_lengths.
        erewrite replay_sel_in; eauto.
        autorewrite with lengths in *.
        solve_lengths.
      + intros Hf. repeat erewrite replay_sel_other.
        apply H1.
        right.
        word2nat_rewrites; try word2nat_solve.
        intro HIn.
        apply MapFacts.not_find_in_iff in Hf.
        apply In_MapIn in HIn. tauto.
        apply MapFacts.not_find_in_iff; auto.
        apply MapFacts.not_find_in_iff; auto.
    - repeat rewrite replay_sel_invalid by auto.
      apply H1.
      left.
      word2nat_auto.
    }
  Qed.

  Lemma f_equal_unless_in: forall A B (f: A -> B) l a b def def',
    equal_unless_in l a b def -> equal_unless_in l (map f a) (map f b) def'.
  Proof.
    unfold equal_unless_in; split.
    repeat rewrite map_length; intuition.
    intros.
    destruct H.
    destruct (lt_dec n (length b)).
    repeat rewrite selN_map with (default' := def) by congruence.
    f_equal. intuition.
    repeat rewrite selN_oob by (rewrite map_length; omega); trivial.
  Qed.

  Lemma equal_unless_in_replay_eq': forall ms (a b: list valuset) def,
    equal_unless_in (map fst (Map.elements ms)) a b def -> replay ms (map fst a) = replay ms (map fst b).
  Proof.
    intros.
    apply equal_unless_in_replay_eq with (def := fst def).
    eapply f_equal_unless_in; eauto.
  Qed.

  Lemma combine_repeat_map: forall A B (v: B) (l: list A),
    List.combine l (repeat v (length l)) = map (fun x => (x, v)) l.
  Proof.
    induction l; simpl; auto.
    fold repeat; rewrite IHl; auto.
  Qed.

  Lemma equal_unless_in_replay_eq'': forall ms (a b: list valu) def,
    replay ms a = replay ms b -> equal_unless_in (map fst (Map.elements ms)) (List.combine a (repeat (@nil valu) (length a))) (List.combine b (repeat (@nil valu) (length b))) def.
  Proof.
    intros.
    repeat rewrite combine_repeat_map.
    eapply f_equal_unless_in.
    apply equal_unless_in_replay_eq with (def := fst def); auto.
  Qed.


  Lemma map_fst_combine: forall A B (a: list A) (b: list B),
    length a = length b -> map fst (List.combine a b) = a.
  Proof.
    unfold map, List.combine; induction a; intros; auto.
    destruct b; try discriminate; simpl in *.
    rewrite IHa; [ auto | congruence ].
  Qed.
  Hint Resolve equal_unless_in_trans equal_unless_in_comm equal_unless_in_replay_eq equal_unless_in_replay_eq'' : replay.

  Definition apply_unsync T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    cs <- For i < $ (Map.cardinal ms)
    Ghost cur
    Loopvar cs <- cs
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ ((LogCommit xp) |=> $1
          * log_rep xp cur ms
          * exists d, data_rep xp d
          * [[ replay' (skipn (wordToNat i) (Map.elements ms)) (map fst d) = cur ]]
          * [[ equal_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur (map fst d) $0 ]]
          * [[ nil_unless_in (map fst (Map.elements ms)) (map snd d) ]])%pred d' ]]
    OnCrash
      exists mscs', rep xp (CommittedTxn cur) mscs'
    Begin
      cs <- BUFCACHE.write_array (LogCache xp) (DataStart xp)
        (sel (map fst (Map.elements ms)) i $0) (sel (map snd (Map.elements ms)) i $0) cs;
      lrx cs
    Rof;
    rx (ms, cs).

  Theorem apply_unsync_ok: forall xp mscs,
    {< m,
    PRE        rep xp (CommittedTxn m) mscs
    POST:mscs' rep xp (AppliedUnsyncTxn m) mscs'
    CRASH      exists mscs', rep xp (CommittedTxn m) mscs'
    >} apply_unsync xp mscs.
  Proof.
    unfold apply_unsync; log_unfold.
    destruct mscs as [ms cs]; simpl.
    hoare_with log_unfold ltac:(eauto with replay).
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply_unsync _ _) _) => apply apply_unsync_ok : prog.

  Definition apply_sync T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    cs <- For i < $ (Map.cardinal ms)
    Ghost cur
    Loopvar cs <- cs
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ ((LogCommit xp) |=> $1
          * log_rep xp cur ms
          * exists cur_unflushed, data_rep xp (List.combine cur cur_unflushed)
          * [[ nil_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur_unflushed ]])%pred d' ]]
    OnCrash
      exists mscs', rep xp (AppliedUnsyncTxn cur) mscs'
    Begin
      cs <- BUFCACHE.sync_array (LogCache xp) (DataStart xp) (sel (map fst (Map.elements ms)) i $0) cs;
      lrx cs
    Rof;
    cs <- BUFCACHE.write (LogCache xp) (LogCommit xp) $0 cs;
    rx (ms, cs).

  Theorem apply_sync_ok: forall xp mscs,
    {< m,
    PRE        rep xp (AppliedUnsyncTxn m) mscs
    POST:mscs' rep xp (AppliedTxn m) mscs'
    CRASH      exists mscs', rep xp (AppliedUnsyncTxn m) mscs' \/ rep xp (AppliedTxn m) mscs'
    >} apply_sync xp mscs.
  Proof.
    unfold apply_sync; log_unfold.
    destruct mscs as [ms cs]; simpl.
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

  Definition apply T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    let2 (ms, cs) <- apply_unsync xp (ms, cs);
    let2 (ms, cs) <- apply_sync xp (ms, cs);
    cs <- BUFCACHE.sync (LogCache xp) (LogCommit xp) cs;
    rx (ms, cs).

  Theorem apply_ok: forall xp mscs,
    {< m,
    PRE        rep xp (CommittedTxn m) mscs
    POST:mscs' rep xp (NoTransaction m) mscs'
    CRASH      exists mscs', rep xp (CommittedTxn m) mscs' \/
                             rep xp (AppliedTxn m) mscs' \/
                             rep xp (NoTransaction m) mscs'
    >} apply xp mscs.
  Proof.
    unfold apply; log_unfold.
    destruct mscs as [ms cs].
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

  Definition commit T xp (mscs : memstate * cachestate) rx : prog T :=
    let (ms, cs) := mscs in
    let3 (ms, cs, ok) <- flush xp (ms, cs);
    If (bool_dec ok true) {
      cs <- BUFCACHE.write (LogCache xp) (LogCommit xp) $1 cs;
      cs <- BUFCACHE.sync (LogCache xp) (LogCommit xp) cs;
      let2 (ms, cs) <- apply xp (ms, cs);
      rx (ms, cs, true)
    } else {
      let2 (ms, cs) <- abort xp (ms, cs);
      rx (ms, cs, false)
    }.


  Definition would_recover_old xp old :=
    (exists mscs, (rep xp (NoTransaction old) mscs) \/
     (exists cur, rep xp (ActiveTxn old cur) mscs))%pred.

  Definition might_recover_cur xp old cur :=
    (exists mscs, rep xp (CommittedUnsyncTxn old cur) mscs \/
      rep xp (CommittedTxn cur) mscs \/
      rep xp (AppliedTxn cur) mscs \/
      rep xp (NoTransaction cur) mscs)%pred.

  (** The log is in a valid state with (after recovery) represents either disk state [old] or [cur] *)
  Definition would_recover_either xp old cur :=
    (would_recover_old xp old \/ might_recover_cur xp old cur)%pred.

  Ltac or_r := apply pimpl_or_r; right.
  Ltac or_l := apply pimpl_or_r; left.

  Theorem commit_ok: forall xp mscs,
    {< m1 m2,
     PRE            rep xp (ActiveTxn m1 m2) mscs
     POST:(mscs',r) ([[ r = true ]] * rep xp (NoTransaction m2) mscs') \/
                    ([[ r = false ]] * rep xp (NoTransaction m1) mscs')
     CRASH          would_recover_either xp m1 m2
    >} commit xp mscs.
  Proof.
    unfold commit, would_recover_either, would_recover_old, might_recover_cur.
    hoare_with log_unfold ltac:(info_eauto with replay).
    cancel_with ltac:(info_eauto with replay).
    or_r; cancel.
    or_r; or_r; or_l; cancel_with auto.
    or_l; cancel.
    or_l; cancel.
    unfold avail_region.
    norm.
    unfold stars; simpl.
    rewrite sep_star_comm.
    eapply pimpl_trans. rewrite <- emp_star. apply pimpl_refl.
    array_match.
    intuition.
    solve_lengths.
  Qed.

  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.

  Module MapProperties := WProperties Map.

  Definition read_log T (xp : xparams) cs rx : prog T :=
    let2 (cs, d) <- BUFCACHE.read (LogCache xp) (LogDescriptor xp) cs;
    let desc := valu_to_descriptor d in
    let2 (cs, h) <- BUFCACHE.read (LogCache xp) (LogHeader xp) cs;
    let len := (valu_to_header h) :-> "length" in
    let2 (cs, log) <- For i < len
    Ghost cur log_on_disk
    Loopvar cs_log_prefix <- (cs, [])
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep (fst cs_log_prefix) d' *
      [[ ((LogCommit xp) |=> $1
          * exists old d, data_rep xp d
          * cur_rep old log_on_disk cur
          * log_rep xp old log_on_disk
            (* If something's in the transaction, it doesn't matter what state it's in on disk *)
          * [[ equal_unless_in (map fst (Map.elements log_on_disk)) (synced_list old) d ($0, nil) ]]
          * [[ snd cs_log_prefix = firstn (wordToNat i) (Map.elements log_on_disk) ]])%pred d' ]]
    OnCrash
      exists mscs, rep xp (CommittedTxn cur) mscs
    Begin
      let (cs, log_prefix) := (cs_log_prefix : cachestate * list (addr * valu)) in
      let2 (cs, v) <- BUFCACHE.read_array (LogCache xp) (LogData xp) i cs;
      lrx (cs, log_prefix ++ [(sel desc i $0, v)])
    Rof;
    rx (MapProperties.of_list log, cs).

  Theorem read_log_ok: forall xp cs,
    {< m ms,
    PRE          rep xp (CommittedTxn m) (ms, cs)
    POST:(r,cs') [[ r = ms ]] * rep xp (CommittedTxn m) (ms, cs)
    CRASH        exists mscs', rep xp (CommittedTxn m) mscs'
    >} read_log xp cs.
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

  Hint Extern 1 ({{_}} progseq (read_log _ _) _) => apply read_log_ok : prog.

  Definition recover T xp rx : prog T :=
    cs <- BUFCACHE.init (LogCache xp);
    let2 (cs, v) <- BUFCACHE.read (LogCache xp) (LogCommit xp) cs;
    If (weq v $1) {
      let2 (ms, cs) <- read_log xp cs;
      let2 (ms, cs) <- apply xp (ms, cs);
      rx (ms, cs)
    } else {
      rx (ms_empty, cs)
    }.

  Hint Rewrite crash_xform_sep_star_dist crash_xform_or_dist crash_xform_exists_comm crash_xform_lift_empty
    crash_invariant_ptsto : crash_xform.

  Hint Resolve crash_invariant_emp.

  Lemma crash_invariant_synced_array: forall l start stride,
    crash_xform (array start (List.combine l (repeat nil (length l))) stride) =p=>
    array start (List.combine l (repeat nil (length l))) stride.
  Proof.
    unfold array.
    induction l; intros; simpl; auto.
    autorewrite with crash_xform.
    cancel.
    auto.
  Qed.
  Hint Rewrite crash_invariant_synced_array : crash_xform.

  Lemma crash_xform_ptsto: forall AT AEQ (a: AT) v,
    crash_xform (a |-> v) =p=> exists v', [[ In v' (valuset_list v) ]] * (@ptsto AT AEQ valuset a (v', nil)).
  Proof.
    unfold crash_xform, possible_crash, ptsto, pimpl; intros.
    repeat deex; destruct (H1 a).
    intuition; congruence.
    repeat deex; rewrite H in H3; inversion H3; subst.
    repeat eexists.
    apply lift_impl.
    intros; eauto.
    split; auto.
    intros.
    destruct (H1 a').
    intuition.
    repeat deex.
    specialize (H2 a' H4).
    congruence.
  Qed.
  Hint Rewrite crash_xform_ptsto : crash_xform.

  Definition possible_crash_list (l: list valuset) (l': list valu) :=
    length l = length l' /\ forall i, i < length l -> In (selN l' i $0) (valuset_list (selN l i ($0, nil))).

  Lemma crash_xform_array: forall l start stride,
    crash_xform (array start l stride) =p=>
      exists l', [[ possible_crash_list l l' ]] * array start (List.combine l' (repeat nil (length l'))) stride.
  Proof.
    unfold array, possible_crash_list.
    induction l; intros.
    cancel.
    instantiate (a := nil).
    simpl; auto.
    auto.
    autorewrite with crash_xform.
    rewrite IHl.
    cancel; [ instantiate (a := w :: l0) | .. ]; simpl; auto; fold repeat; try cancel;
      destruct i; simpl; auto;
      destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_invariant_avail_region: forall start len,
    crash_xform (avail_region start len) =p=> avail_region start len.
  Proof.
    unfold avail_region.
    intros.
    autorewrite with crash_xform.
    norm'l.
    unfold stars; simpl.
    autorewrite with crash_xform.
    rewrite crash_xform_array.
    unfold possible_crash_list.
    cancel.
    solve_lengths.
  Qed.
  Hint Rewrite crash_invariant_avail_region : crash_xform.

  Ltac log_intact_unfold := unfold MEMLOG.would_recover_either, MEMLOG.would_recover_old, MEMLOG.might_recover_cur.

  Ltac word_discriminate :=
    match goal with [ H: $ _ = $ _ |- _ ] => solve [
      apply natToWord_discriminate in H; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial]
    ] end.

  Lemma pred_apply_crash_xform: forall AT AEQ (P Q: @pred AT AEQ valuset) m m',
    possible_crash m m' -> P m -> (crash_xform P) m'.
  Proof.
    unfold pimpl, crash_xform; eauto.
  Qed.

  Theorem recover_ok: forall xp,
    {< m1 m2,
    PRE       crash_xform (would_recover_either xp m1 m2)
    POST:mscs rep xp (NoTransaction m1) mscs \/ rep xp (NoTransaction m2) mscs
    CRASH     would_recover_either xp m1 m2
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
    rewrite sep_star_comm. rewrite <- emp_star.
    repeat rewrite sep_star_or_distr; repeat apply pimpl_or_l; norm'l; try word_discriminate;
      unfold stars; simpl; autorewrite with crash_xform.

    cancel.
    rewrite BUFCACHE.crash_xform_rep.
    instantiate (a0 := p).
    rewrite sep_star_comm.
    apply pimpl_refl.
    Ltac cancel_pred_crash :=
      eapply pred_apply_crash_xform; eauto;
      autorewrite with crash_xform;
      cancel; subst; cancel.

    eapply pimpl_ok2; [ eauto with prog | ].
    intros; simpl.
    norm'l.
    unfold BUFCACHE.rep, diskIs in H7.
    destruct_lift H7; subst.
    (* XXX have to destruct exis in crash_transform'd H4 before evars get made *)
    norm'r.
    cancel'.
    intuition.
    eapply pred_apply_crash_xform; eauto.
    autorewrite with crash_xform.

    pimpl_crash.
    cancel.

    or_l; cancel.
    or_l.
    norm. cancel'.
    intuition.
    cancel_pred_crash.

      - step; step; try word_discriminate.
        rewrite crash_invariant_avail_region.
        or_l; cancel.
        autorewrite with crash_xform.
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

    (* Switched from Admitted to Qed to make CoqIDE's async proofs happy *)
  Qed.

  Hint Extern 1 ({{_}} progseq (recover _) _) => apply recover_ok : prog.

  Definition read_array T xp a i stride mscs rx : prog T :=
    let2 (mscs, r) <- read xp (a ^+ i ^* stride) mscs;
    rx (mscs, r).

  Definition write_array T xp a i stride v mscs rx : prog T :=
    mscs <- write xp (a ^+ i ^* stride) v mscs;
    rx mscs.

  Theorem read_array_ok : forall xp mscs a i stride,
    {< mbase m vs,
    PRE            rep xp (ActiveTxn mbase m) mscs *
                   [[ exists F', (array a vs stride * F')%pred (list2mem m) ]] *
                   [[ wordToNat i < length vs ]]
    POST:(mscs',r) [[ r = sel vs i $0 ]] * rep xp (ActiveTxn mbase m) mscs'
    CRASH          exists mscs', rep xp (ActiveTxn mbase m) mscs'
    >} read_array xp a i stride mscs.
  Proof.
    unfold read_array.
    hoare.

    pred_apply.
    rewrite isolate_fwd with (i:=i) by auto.
    cancel.
  Qed.

  Theorem write_array_ok : forall xp a i stride v mscs,
    {< mbase m vs F',
    PRE        rep xp (ActiveTxn mbase m) mscs
                * [[ (array a vs stride * F')%pred (list2mem m) ]]
                * [[ wordToNat i < length vs ]]
    POST:mscs' exists m', rep xp (ActiveTxn mbase m') mscs'
                * [[ (array a (Array.upd vs i v) stride * F')%pred (list2mem m') ]]
    CRASH      exists m' mscs', rep xp (ActiveTxn mbase m') mscs'
    >} write_array xp a i stride v mscs.
  Proof.
    unfold write_array.
    hoare.

    pred_apply.
    rewrite isolate_fwd with (i:=i) by auto.
    cancel.

    rewrite <- isolate_bwd_upd by auto.
    cancel.

    Grab Existential Variables.
    exact $0.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _ _) _) => apply write_array_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ ?a) (rep _ _ ?a)) => constructor : okToUnify.

End MEMLOG.



Global Opaque MEMLOG.write.

