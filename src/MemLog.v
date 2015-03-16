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
Require Import SepAuto2.
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
Require Import Idempotent.
Require Import FSLayout.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Import ListNotations.
Set Implicit Arguments.

Definition memstate := Map.t valu.
Definition ms_empty := Map.empty valu.
Definition memstate_cachestate := (memstate * (cachestate * unit))%type.

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

  Theorem valid_entries_empty : forall m, valid_entries m ms_empty.
  Proof.
    unfold valid_entries; intros.
    apply MapFacts.empty_mapsto_iff in H. intuition.
  Qed.

  Theorem valid_size_empty : forall xp, valid_size xp ms_empty.
  Proof.
    unfold valid_size; intros.
    rewrite MapProperties.cardinal_1 by apply Map.empty_1. omega.
  Qed.

  Hint Resolve valid_entries_empty.
  Hint Resolve valid_size_empty.

  (* Replay the state in memory *)
  Definition replay' V (l : list (addr * V)) (m : list V) : list V :=
    fold_right (fun p m' => upd m' (fst p) (snd p)) m l.

  Definition replay (ms : memstate) (m : diskstate) : diskstate :=
    replay' (Map.elements ms) m.

  Theorem replay_empty : forall d, replay ms_empty d = d.
  Proof.
    unfold replay.
    rewrite MapProperties.elements_empty.
    reflexivity.
  Qed.

  Hint Rewrite replay_empty.

  Lemma replay'_upd : forall l d a (v : valu),
    upd (replay' l (upd d a v)) a v = upd (replay' l d) a v.
  Proof.
    induction l; simpl; intros.
    autorewrite with core; auto.
    destruct (weq a0 (fst a)); subst.
    - repeat rewrite upd_twice. rewrite IHl. auto.
    - rewrite upd_comm by auto. rewrite IHl. rewrite upd_comm by auto. auto.
  Qed.

  Theorem replay_twice : forall m d, replay m (replay m d) = replay m d.
  Proof.
    unfold replay.
    intro m; generalize (Map.elements m); clear m.
    induction l; simpl; auto; intros.
    rewrite replay'_upd.
    rewrite IHl. auto.
  Qed.

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

  Lemma avail_region_grow_all : forall fsxp m,
    valid_size fsxp m ->
    array (LogData fsxp)
      (List.combine (map snd (Map.elements (elt:=valu) m))
         (repeat [] (length (map snd (Map.elements (elt:=valu) m))))) $ (1) *
    avail_region (LogData fsxp ^+ $ (Map.cardinal (elt:=valu) m))
      (# (LogLen fsxp) - Map.cardinal (elt:=valu) m) =p=>
    avail_region (LogData fsxp) # (LogLen fsxp).
  Proof.
    admit.
  Qed.

  Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).

  Definition data_rep (xp: memlog_xparams) (m: list valuset) : @pred addr (@weq addrlen) valuset :=
    array (DataStart xp) m $1.

  (** On-disk representation of the log *)
  Definition log_rep xp m (ms : memstate) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest,
      (LogDescriptor xp) |=> (descriptor_to_valu (map fst (Map.elements ms) ++ rest)) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      array (LogData xp) (synced_list (map snd (Map.elements ms))) $1 *
      avail_region (LogData xp ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms))%pred.

  (* XXX DRY? *)
  Definition log_rep_unsynced xp m (ms : memstate) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest others,
      (LogDescriptor xp) |-> (descriptor_to_valu (map fst (Map.elements ms) ++ rest),
                              map descriptor_to_valu others) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      exists unsynced,
      array (LogData xp) (List.combine (map snd (Map.elements ms)) unsynced) $1 *
      [[ length unsynced = Map.cardinal ms ]] *
      avail_region (LogData xp ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms) *
      [[ Forall (@Rec.well_formed descriptor_type) others ]])%pred.

  Definition log_rep_empty xp : @pred addr (@weq addrlen) valuset :=
     (exists rest,
      (LogDescriptor xp) |=> (descriptor_to_valu rest) *
      [[ @Rec.well_formed descriptor_type (rest) ]] *
      avail_region (LogData xp) (wordToNat (LogLen xp)))%pred.

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
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * [[ ms = ms_empty ]]
    * data_rep xp (synced_list m)
    * log_rep_empty xp

    | ActiveTxn old cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * data_rep xp (synced_list old) (* Transactions are always completely buffered in memory. *)
    * log_rep_empty xp
    * cur_rep old ms cur
    * [[ valid_entries old ms ]]

    | FlushedUnsyncTxn old cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * data_rep xp (synced_list old)
    * log_rep_unsynced xp old ms
    * cur_rep old ms cur

    | FlushedTxn old cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur

    | CommittedUnsyncTxn old cur =>
      (LogHeader xp) |-> (header_to_valu (mk_header (Map.cardinal ms)), header_to_valu (mk_header 0) :: nil)
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur

    | CommittedTxn cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header (Map.cardinal ms)))
    * exists old d, data_rep xp d
      (* If something's in the transaction, it doesn't matter what state it's in on disk *)
    * [[ equal_unless_in (map fst (Map.elements ms)) (synced_list old) d ($0, nil) ]]
    * log_rep xp old ms
    * cur_rep old ms cur

    | AppliedUnsyncTxn cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header (Map.cardinal ms)))
    * exists old old_unflushed, data_rep xp (List.combine cur old_unflushed)
    * [[ nil_unless_in (map fst (Map.elements ms)) old_unflushed ]]
    * log_rep xp old ms
    * cur_rep old ms cur

    | AppliedTxn cur =>
      (LogHeader xp) |-> (header_to_valu (mk_header 0), header_to_valu (mk_header (Map.cardinal ms)) :: nil)
    * data_rep xp (synced_list cur)
    * exists old, log_rep xp old ms
    * cur_rep old ms cur

    end)%pred.

  Definition rep xp F st mscs := let '^(ms, cs) := mscs in (exists d,
    BUFCACHE.rep cs d * [[ (F * rep_inner xp st ms)%pred d ]])%pred.

  Definition init T xp cs rx : prog T :=
    cs <- BUFCACHE.write (LogHeader xp) (header_to_valu (mk_header 0)) cs;
    cs <- BUFCACHE.sync (LogHeader xp) cs;
    rx ^(ms_empty, cs).

  Ltac log_unfold := unfold rep, rep_inner, data_rep, cur_rep, log_rep, log_rep_unsynced, valid_size, synced_list.

  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _ _) (data_rep _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (rep_inner _ _ _) (rep_inner _ _ _)) => constructor : okToUnify.

  (* XXX actually okay? *)
  Local Hint Extern 0 (okToUnify (array (DataStart _) _ _) (array (DataStart _) _ _)) => constructor : okToUnify.

  Definition log_uninitialized xp old :=
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
     [[ goodSize addrlen (# (LogData xp) + # (LogLen xp)) ]] *
     data_rep xp (synced_list old) *
     avail_region (LogData xp) (wordToNat (LogLen xp)) *
     (LogDescriptor xp) |->? *
     (LogHeader xp) |->?)%pred.

  (* XXX remove once SepAuto and SepAuto2 are unified *)
  Hint Extern 0 (okToUnify (BUFCACHE.rep _ _) (BUFCACHE.rep _ _)) => constructor : okToUnify.

  Definition unifiable_array := @array valuset.

  Hint Extern 0 (okToUnify (unifiable_array _ _ _) (unifiable_array _ _ _)) => constructor : okToUnify.

  Theorem init_ok : forall xp cs,
    {< old d F,
    PRE
      BUFCACHE.rep cs d * [[ (F * log_uninitialized xp old)%pred d ]]
    POST RET:mscs
      rep xp F (NoTransaction old) mscs
    CRASH
      exists cs' d', BUFCACHE.rep cs' d' * [[ (F * log_uninitialized xp old)%pred d' ]]
    >} init xp cs.
  Proof.
    unfold init, log_uninitialized; log_unfold.
    hoare.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _ _) _) => apply init_ok : prog.

  Definition begin T (xp : memlog_xparams) (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    rx ^(ms_empty, cs).

  Theorem begin_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (NoTransaction m) mscs
    POST RET:r
      rep xp F (ActiveTxn m m) r
    CRASH
      exists mscs', rep xp F (NoTransaction m) mscs' \/ rep xp F (ActiveTxn m m) mscs'
    >} begin xp mscs.
  Proof.
    unfold begin; log_unfold.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.

  Definition abort T (xp : memlog_xparams) (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    rx ^(ms_empty, cs).

  Theorem abort_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs
    POST RET:r
      rep xp F (NoTransaction m1) r
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs' \/ rep xp F (NoTransaction m1) mscs'
    >} abort xp mscs.
  Proof.
    unfold abort; log_unfold.
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

  Lemma valid_entries_replay : forall m d,
    valid_entries d m ->
    valid_entries (replay m d) m.
  Proof.
    unfold valid_entries, indomain', replay. intros.
    apply H in H0.
    rewrite <- replay'_length.
    auto.
  Qed.
  Hint Resolve valid_entries_replay.

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

  Definition write T (xp : memlog_xparams) a v (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    rx ^(Map.add a v ms, cs).

  Theorem write_ok : forall xp mscs a v,
    {< m1 m2 F F' v0,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs * [[ (F' * a |-> v0)%pred (list2mem m2) ]]
    POST RET:mscs
      exists m', rep xp F (ActiveTxn m1 m') mscs *
      [[ (F' * a |-> v)%pred (list2mem m') ]]
    CRASH
      exists m' mscs', rep xp F (ActiveTxn m1 m') mscs'
    >} write xp a v mscs.
  Proof.
    unfold write; log_unfold.
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

  Definition read T (xp: memlog_xparams) a (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    match Map.find a ms with
    | Some v =>
      rx ^(^(ms, cs), v)
    | None =>
      let^ (cs, v) <- BUFCACHE.read_array (DataStart xp) a cs;
      rx ^(^(ms, cs), v)
    end.


  Theorem read_ok: forall xp mscs a,
    {< m1 m2 v F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs *
      [[ exists F, (F * a |-> v) (list2mem m2) ]]
    POST RET:^(mscs,r)
      rep xp F (ActiveTxn m1 m2) mscs *
      [[ r = v ]]
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs'
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

    unfold sel.
    rewrite combine_length_eq.
    apply list2mem_ptsto_bounds in H1.
    rewrite replay_length in *.
    eauto.
    rewrite repeat_length.
    eauto.
    
    simpl.
    eapply list2mem_sel with (def := $0) in H1.
    rewrite H1.
    unfold sel.
    rewrite replay_sel_other. trivial.
    intuition.
    subst.
    rewrite selN_combine.
    simpl.
    eauto.

    rewrite repeat_length.
    eauto.

    intro.
    hnf in H4.
    destruct H4.
    apply Map.find_1 in H4.
    congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.

  Definition flush_unsync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    cs <- BUFCACHE.write (LogDescriptor xp)
      (descriptor_to_valu (map fst (Map.elements ms))) cs;
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ old crash F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header 0)
          * data_rep xp (synced_list old)
          * (LogDescriptor xp) |~> descriptor_to_valu (map fst (Map.elements ms))
          * exists l', [[ length l' = # i ]]
          * array (LogData xp) (firstn (# i) (List.combine (map snd (Map.elements ms)) l')) $1
          * avail_region (LogData xp ^+ i) (# (LogLen xp) - # i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.write_array (LogData xp ^+ i) $0
        (sel (map snd (Map.elements ms)) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx ^(ms, cs).

  Definition flush_sync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    cs <- BUFCACHE.sync (LogDescriptor xp) cs;
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ old crash F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header 0)
          * data_rep xp (synced_list old)
          * exists rest, (LogDescriptor xp) |=> descriptor_to_valu (map fst (Map.elements ms) ++ rest)
          * [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]]
          * array (LogData xp) (firstn (# i) (synced_list (map snd (Map.elements ms)))) $1
          * exists l', [[ length l' = Map.cardinal ms - # i ]]
          * array (LogData xp ^+ i) (List.combine (skipn (# i) (map snd (Map.elements ms))) l') $1
          * avail_region (LogData xp ^+ $ (Map.cardinal ms)) (# (LogLen xp) - Map.cardinal ms))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.sync_array (LogData xp ^+ i) $0 cs;
      lrx ^(cs)
    Rof ^(cs);
    rx ^(ms, cs).

  Definition flush T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    If (lt_dec (wordToNat (LogLen xp)) (Map.cardinal ms)) {
      rx ^(^(ms, cs), false)
    } else {
      (* Write... *)
      let^ (ms, cs) <- flush_unsync xp ^(ms, cs);
      (* ... and sync *)
      let^ (ms, cs) <- flush_sync xp ^(ms, cs);
      rx ^(^(ms, cs), true)
    }.

  Theorem firstn_map : forall A B n l (f: A -> B),
    firstn n (map f l) = map f (firstn n l).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    destruct l; simpl.
    reflexivity.
    f_equal.
    eauto.
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

  Definition emp_star_r' : forall V AT AEQ P, P * (emp (V:=V) (AT:=AT) (AEQ:=AEQ)) =p=> P.
  Proof.
    cancel.
  Qed.

  Ltac word_assert P := let H := fresh in assert P as H by
      (word2nat_simpl; repeat rewrite wordToNat_natToWord_idempotent'; word2nat_solve); clear H.

  Ltac array_sort' :=
    eapply pimpl_trans; rewrite emp_star; [ apply pimpl_refl |];
    set_evars;
    repeat rewrite <- sep_star_assoc;
    subst_evars;
    match goal with
    | [ |- ?p =p=> ?p ] => fail 1
    | _ => idtac
    end;
    repeat match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      word_assert (a2 <= a1)%word;
      first [
        (* if two arrays start in the same place, try to prove one of them is empty and eliminate it *)
        word_assert (a1 = a2)%word;
        first [
          let H := fresh in assert (length l1 = 0) by solve_lengths;
          apply length_nil in H; try rewrite H; clear H; simpl; rewrite emp_star_r'
        | let H := fresh in assert (length l2 = 0) by solve_lengths;
          apply length_nil in H; try rewrite H; clear H; simpl; rewrite emp_star_r'
        | fail 2
        ]
      | (* otherwise, just swap *)
        rewrite (sep_star_assoc p (array a1 l1 s));
        rewrite (sep_star_comm (array a1 l1 s)); rewrite <- (sep_star_assoc p (array a2 l2 s))
      ]
    end;
    (* make sure we can prove it's sorted *)
    match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      (word_assert (a1 <= a2)%word; fail 1) || fail 2
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
    set_evars;
    repeat (rewrite array_app; [ | solve_lengths_prepped ]); [ repeat rewrite <- app_assoc | .. ];
    try apply pimpl_refl;
    try (apply equal_arrays; [ solve_lengths_prepped | try reflexivity ]);
    subst_evars.

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

(*
  Theorem flush_unsync_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs *
      [[ let '^(ms, cs) := mscs in Map.cardinal ms <= wordToNat (LogLen xp) ]]
    POST RET:mscs
      rep xp F (FlushedUnsyncTxn m1 m2) mscs
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs'
    >} flush_unsync xp mscs.
  Proof.
    unfold flush_unsync; log_unfold; unfold avail_region.
    destruct mscs as [ms cs].
    intros.
    solve_lengths_prepare.
    hoare_with idtac try_arrays_lengths.
    instantiate (a2 := nil); auto.
    split_lists.
    rewrite cons_app.
    rewrite app_assoc.
    erewrite firstn_plusone_selN.
    reflexivity.
    solve_lengths.
    simpl.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    instantiate (a3 := l1 ++ [valuset_list (selN l2 0 ($0, nil))]).
    simpl.
    rewrite firstn_app_l by solve_lengths.
    repeat erewrite selN_map by solve_lengths.
    rewrite <- surjective_pairing.
    rewrite selN_app2.
    rewrite H17.
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
    abstract (case_eq l2; intros; subst; word2nat_clear; simpl in *; solve_lengths).

    solve_lengths_prepare.
    instantiate (a1 := repeat $0 (addr_per_block - length (Map.elements ms))).
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
    {< m1 m2 F,
    PRE
      rep xp F (FlushedUnsyncTxn m1 m2) mscs *
      [[ let '^(ms, cs) := mscs in Map.cardinal ms <= wordToNat (LogLen xp) ]]
    POST RET:mscs
      rep xp F (FlushedTxn m1 m2) mscs
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs'
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
    rewrite firstn_oob by solve_lengths; auto.
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
*)

  Theorem flush_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs
    POST RET:^(mscs,r)
      ([[ r = true ]] * rep xp F (FlushedTxn m1 m2) mscs) \/
      ([[ r = false ]] * rep xp F (ActiveTxn m1 m2) mscs)
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs'
    >} flush xp mscs.
  Proof.
    unfold flush; log_unfold.
    destruct mscs as [ms cs].
    intros.
    admit. (* abstract hoare_unfold log_unfold. *)
    
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

  Definition apply_unsync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ cur F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal ms))
          * log_rep xp cur ms
          * exists d, data_rep xp d
          * [[ replay' (skipn (wordToNat i) (Map.elements ms)) (map fst d) = cur ]]
          * [[ equal_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur (map fst d) $0 ]]
          * [[ nil_unless_in (map fst (Map.elements ms)) (map snd d) ]])%pred d' ]]
    OnCrash
      exists mscs', rep xp F (CommittedTxn cur) mscs'
    Begin
      cs <- BUFCACHE.write_array (DataStart xp)
        (sel (map fst (Map.elements ms)) i $0) (sel (map snd (Map.elements ms)) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx ^(ms, cs).

  Theorem apply_unsync_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (CommittedTxn m) mscs
    POST RET:mscs
      rep xp F (AppliedUnsyncTxn m) mscs
    CRASH
      exists mscs', rep xp F (CommittedTxn m) mscs'
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

  Definition apply_sync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ cur F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal ms))
          * log_rep xp cur ms
          * exists cur_unflushed, data_rep xp (List.combine cur cur_unflushed)
          * [[ nil_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur_unflushed ]])%pred d' ]]
    OnCrash
      exists mscs', rep xp F (AppliedUnsyncTxn cur) mscs'
    Begin
      cs <- BUFCACHE.sync_array (DataStart xp) (sel (map fst (Map.elements ms)) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    cs <- BUFCACHE.write (LogHeader xp) (header_to_valu (mk_header 0)) cs;
    rx ^(ms, cs).

  Theorem apply_sync_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (AppliedUnsyncTxn m) mscs
    POST RET:mscs
      rep xp F (AppliedTxn m) mscs
    CRASH
      exists mscs', rep xp F (AppliedUnsyncTxn m) mscs' \/ rep xp F (AppliedTxn m) mscs'
    >} apply_sync xp mscs.
  Proof.
    unfold apply_sync; log_unfold.
    step.
    step.
    (* address passed to [sync_array] is in-bounds *)
    admit.
    step.
    instantiate (1 := upd l1 (map fst (Map.elements m) $[ m1 ]) nil).
    (* updating the (List.combine cur cur_unflushed) *)
    admit.
    (* nil_unless_in for one less item *)
    admit.

    (* crash condition *)
    apply pimpl_or_r; left. cancel; auto.

    (* nil_unless_in *)
    admit.

    (* crash condition *)
    apply pimpl_or_r; left. cancel; auto.
    cancel.
    instantiate (1 := upd l1 (map fst (Map.elements m) $[ m1 ]) nil).
    admit.
    admit.

    step.
    step.

    admit.

    admit.
    admit.

    apply pimpl_or_r; left. cancel; eauto.
(*
    rewrite skipn_oob in H22 by solve_lengths.
*)

    Grab Existential Variables.
    all: eauto.
 Qed.

  Hint Extern 1 ({{_}} progseq (apply_sync _ _) _) => apply apply_sync_ok : prog.

  Definition apply T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (ms, cs) <- apply_unsync xp ^(ms, cs);
    let^ (ms, cs) <- apply_sync xp ^(ms, cs);
    cs <- BUFCACHE.sync (LogHeader xp) cs;
    rx ^(ms, cs).

  Theorem apply_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (CommittedTxn m) mscs
    POST RET:mscs
      rep xp F (NoTransaction m) mscs
    CRASH
      exists mscs', rep xp F (CommittedTxn m) mscs' \/
                    rep xp F (AppliedTxn m) mscs' \/
                    rep xp F (NoTransaction m) mscs'
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

  Definition commit T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    If (bool_dec (Map.is_empty ms) true) {
      rx ^(^(ms, cs), true)
    } else {
      let^ (mscs, ok) <- flush xp ^(ms, cs);
      let '^(ms, cs) := mscs in
      If (bool_dec ok true) {
        cs <- BUFCACHE.write (LogHeader xp) (header_to_valu (mk_header (Map.cardinal ms))) cs;
        cs <- BUFCACHE.sync (LogHeader xp) cs;
        let^ (ms, cs) <- apply xp ^(ms, cs);
        rx ^(^(ms, cs), true)
      } else {
        let^ (ms, cs) <- abort xp ^(ms, cs);
        rx ^(^(ms, cs), false)
      }
    }.

  Definition would_recover_old' xp old :=
    (exists ms, rep_inner xp (NoTransaction old) ms \/
     (exists cur, rep_inner xp (ActiveTxn old cur) ms))%pred.

  Definition would_recover_old xp F old :=
    (exists cs d, BUFCACHE.rep cs d * [[ (F * would_recover_old' xp old)%pred d ]])%pred.

  Definition would_recover_either' xp old cur :=
    (exists ms,
      rep_inner xp (NoTransaction old) ms \/
      (exists x, rep_inner xp (ActiveTxn old x) ms) \/
      rep_inner xp (CommittedTxn old) ms \/
      rep_inner xp (AppliedTxn old) ms \/
      rep_inner xp (CommittedUnsyncTxn old cur) ms \/
      rep_inner xp (CommittedTxn cur) ms \/
      rep_inner xp (AppliedTxn cur) ms \/
      rep_inner xp (NoTransaction cur) ms)%pred.

  Definition would_recover_either_pred' xp old curpred :=
    (exists ms,
      rep_inner xp (NoTransaction old) ms \/
      (exists x, rep_inner xp (ActiveTxn old x) ms) \/
      rep_inner xp (CommittedTxn old) ms \/
      rep_inner xp (AppliedTxn old) ms \/
      (exists cur, rep_inner xp (CommittedUnsyncTxn old cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (CommittedTxn cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (AppliedTxn cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (NoTransaction cur) ms * [[ curpred (list2mem cur) ]]))%pred.

  Definition would_recover_either xp F old cur :=
    (exists cs d, BUFCACHE.rep cs d * [[ (F * would_recover_either' xp old cur)%pred d ]])%pred.

  Definition would_recover_either_pred xp F old curpred :=
    (exists cs d, BUFCACHE.rep cs d * [[ (F * would_recover_either_pred' xp old curpred)%pred d ]])%pred.

  Hint Extern 0 (okToUnify (would_recover_old _ _ _) (would_recover_old _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (SepAuto.okToUnify (would_recover_old _ _ _) (would_recover_old _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (would_recover_either _ _ _ _) (would_recover_either _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (SepAuto.okToUnify (would_recover_either _ _ _ _) (would_recover_either _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (would_recover_either_pred _ _ _ _) (would_recover_either_pred _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (SepAuto.okToUnify (would_recover_either_pred _ _ _ _) (would_recover_either_pred _ _ _ _)) => constructor : okToUnify.

  Ltac or_r := apply pimpl_or_r; right.
  Ltac or_l := apply pimpl_or_r; left.

  Theorem commit_ok: forall xp mscs,
    {< m1 m2 F,
     PRE            rep xp F (ActiveTxn m1 m2) mscs
     POST RET:^(mscs,r)
                    ([[ r = true ]] * rep xp F (NoTransaction m2) mscs) \/
                    ([[ r = false ]] * rep xp F (NoTransaction m1) mscs)
     CRASH          would_recover_either xp F m1 m2
    >} commit xp mscs.
  Proof.
    unfold commit, would_recover_either.
    hoare_with log_unfold ltac:(info_eauto with replay).
    cancel_with ltac:(info_eauto with replay).
    admit.
    or_r; cancel.
    or_r; or_l; cancel_with auto.
    eauto.
    eauto.
    admit.
    admit.
    admit.
(*
    or_l; cancel.
    or_l; cancel.
    unfold avail_region.
    norm.
    unfold stars; simpl.
    rewrite sep_star_comm.
    eapply pimpl_trans. rewrite <- emp_star. apply pimpl_refl.
    array_match.
    intuition.
    solve_lengths.*)
  Qed.

  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.

  Module MapProperties := WProperties Map.

  Definition read_log T (xp : memlog_xparams) cs rx : prog T :=
    let^ (cs, d) <- BUFCACHE.read (LogDescriptor xp) cs;
    let desc := valu_to_descriptor d in
    let^ (cs, h) <- BUFCACHE.read (LogHeader xp) cs;
    let len := (valu_to_header h) :-> "length" in
    let^ (cs, log) <- For i < len
    Ghost [ cur log_on_disk F ]
    Loopvar [ cs log_prefix ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal log_on_disk))
          * exists old d, data_rep xp d
          * cur_rep old log_on_disk cur
          * log_rep xp old log_on_disk
            (* If something's in the transaction, it doesn't matter what state it's in on disk *)
          * [[ equal_unless_in (map fst (Map.elements log_on_disk)) (synced_list old) d ($0, nil) ]]
          * [[ log_prefix = firstn (wordToNat i) (Map.elements log_on_disk) ]])%pred d' ]]
    OnCrash
      exists mscs, rep xp F (CommittedTxn cur) mscs
    Begin
      let^ (cs, v) <- BUFCACHE.read_array (LogData xp) i cs;
      lrx ^(cs, log_prefix ++ [(sel desc i $0, v)])
    Rof ^(cs, []);
    rx ^(MapProperties.of_list log, cs).

  Theorem read_log_ok: forall xp cs,
    {< m ms F,
    PRE
      rep xp F (CommittedTxn m) ^(ms, cs)
    POST RET:^(r,cs)
      [[ r = ms ]] * rep xp F (CommittedTxn m) ^(ms, cs)
    CRASH
      exists mscs', rep xp F (CommittedTxn m) mscs'
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

  Definition recover T (xp: memlog_xparams) cs rx : prog T :=
    let^ (ms, cs) <- read_log xp cs;
    let^ (ms, cs) <- apply xp ^(ms, cs);
    rx ^(ms, cs).

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

  Lemma valid_entries_lengths_eq : forall l1 l2 m,
    length l1 = length l2 -> valid_entries l1 m -> valid_entries l2 m.
  Proof.
    unfold valid_entries, indomain'.
    intuition.
    rewrite <- H; eauto.
  Qed.

  Ltac word_discriminate :=
    match goal with [ H: $ _ = $ _ |- _ ] => solve [
      apply natToWord_discriminate in H; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial]
    ] end.

  Ltac cancel_pred_crash :=
    eapply pred_apply_crash_xform; eauto;
    autorewrite with crash_xform;
    cancel; subst; cancel.

  Lemma equal_unless_in_refl : forall A ms l d,
    @equal_unless_in A ms l l d.
  Proof.
    unfold equal_unless_in; intuition.
  Qed.
  Hint Resolve equal_unless_in_refl : replay.

  Lemma would_recover_old'_either' : forall xp old,
    would_recover_old' xp old =p=> would_recover_either' xp old old.
  Proof.
    unfold would_recover_old', would_recover_either'.
    cancel.
  Qed.

  Lemma would_recover_old_either : forall xp F old,
    would_recover_old xp F old =p=> would_recover_either xp F old old.
  Proof.
    unfold would_recover_old, would_recover_either.
    cancel.
    apply would_recover_old'_either'.
  Qed.

  Lemma would_recover_old'_either_pred' : forall xp old p,
    would_recover_old' xp old =p=> would_recover_either_pred' xp old p.
  Proof.
    unfold would_recover_old', would_recover_either_pred'.
    cancel.
  Qed.

  Lemma would_recover_old_either_pred : forall xp F old p,
    would_recover_old xp F old =p=> would_recover_either_pred xp F old p.
  Proof.
    unfold would_recover_old, would_recover_either_pred.
    cancel.
    apply would_recover_old'_either_pred'.
  Qed.

  Lemma would_recover_either'_pred'_pimpl : forall xp old new p,
    would_recover_either' xp old new * [[ p (list2mem new) ]] =p=> would_recover_either_pred' xp old p.
  Proof.
    unfold would_recover_either', would_recover_either_pred'.
    (* split up manually because the automated search takes too long to find the 8th OR *)
    intros; norm; intuition; unfold stars; simpl.
    cancel.
    cancel.
    cancel.
    cancel.
    do 4 or_r. or_l. cancel.
    do 5 or_r. or_l. cancel.
    do 6 or_r. or_l. cancel.
    repeat or_r. cancel.
  Qed.

  Lemma would_recover_either_pred_pimpl : forall xp F old new p,
    would_recover_either xp F old new * [[ p (list2mem new) ]] =p=> would_recover_either_pred xp F old p.
  Proof.
    unfold would_recover_either, would_recover_either_pred.
    cancel.
    rewrite <- would_recover_either'_pred'_pimpl.
    cancel.
  Qed.

  Lemma notxn_would_recover_old : forall xp F old mscs,
    rep xp F (NoTransaction old) mscs =p=> would_recover_old xp F old.
  Proof.
    unfold would_recover_old, would_recover_old'.
    cancel. cancel.
  Qed.

  Lemma activetxn_would_recover_old : forall xp F old new mscs,
    rep xp F (ActiveTxn old new) mscs =p=> would_recover_old xp F old.
  Proof.
    unfold would_recover_old, would_recover_old'.
    cancel. cancel.
  Qed.

  (**
   * [after_crash_pred'] is similar to [would_recover_either_pred'] but describes
   * states after a crash (i.e., after [crash_xform]).  This is a smaller set of
   * different states that we have to consider.
   *)
  Definition after_crash_pred' xp old curpred :=
    (exists ms,
      rep_inner xp (NoTransaction old) ms \/
      rep_inner xp (CommittedTxn old) ms \/
      (exists cur, rep_inner xp (CommittedTxn cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (NoTransaction cur) ms * [[ curpred (list2mem cur) ]]))%pred.

  Lemma crash_xform_would_recover_either_pred' : forall fsxp old curpred,
    crash_xform (would_recover_either_pred' fsxp old curpred) =p=>
    after_crash_pred' fsxp old curpred.
  Proof.
    intros.
    unfold would_recover_either_pred', after_crash_pred'.
    autorewrite with crash_xform.
    repeat setoid_rewrite crash_xform_or_dist.
    setoid_rewrite crash_xform_exists_comm.
    norm'l; unfold stars; simpl.
    rewrite sep_star_comm. rewrite star_emp_pimpl.
    repeat apply pimpl_or_l; unfold rep_inner at 1;
      unfold data_rep, log_rep, log_rep_empty, synced_list, cur_rep.

    - (* NoTransaction old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. cancel.

      or_l.
      unfold rep_inner, data_rep, log_rep_empty. cancel.

    - (* ActiveTxn old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. cancel.

      or_l.
      unfold rep_inner, data_rep, log_rep_empty. cancel.

    - (* CommittedTxn old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. rewrite crash_xform_array. cancel.

      or_r. or_l.
      unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
      cancel; auto.
      unfold possible_crash_list in *.
      unfold equal_unless_in in H7.
      intuition.
      autorewrite with lengths in H1.
      rewrite Nat.min_l in H1 by auto.
      eapply valid_entries_lengths_eq; [ | eauto ]. congruence.
      admit.

    - (* AppliedTxn old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. intuition.

      + (* Header change applied too *)
        cancel.
        or_l.
        unfold rep_inner, data_rep, log_rep_empty. cancel.
        apply avail_region_grow_all; auto.

      + (* Header change was lost *)
        cancel.
        or_r. or_l.
        unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
        cancel. cancel.
        rewrite replay_twice; auto.

    - (* CommittedUnsyncTxn old new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. intuition.

      + (* Commit bit applied *)
        cancel.
        or_r. or_r. or_l.
        unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
        cancel. cancel.

      + (* Commit bit lost *)
        cancel.
        or_l.
        unfold rep_inner, data_rep, log_rep_empty. cancel.
        apply avail_region_grow_all; auto.

    - (* CommittedTxn new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. rewrite crash_xform_array. cancel.

      or_r. or_r. or_l.
      unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
      cancel.
      cancel.
      unfold possible_crash_list in *.
      unfold equal_unless_in in H8.
      intuition.
      autorewrite with lengths in H1.
      rewrite Nat.min_l in H1 by auto.
      eapply valid_entries_lengths_eq; [ | eauto ]. congruence.
      admit.

    - (* AppliedTxn new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. intuition.

      + (* Header change applied too *)
        autorewrite with crash_xform. norm'l; unfold stars; simpl.
        autorewrite with crash_xform. cancel.

        or_r. or_r. or_r.
        unfold rep_inner, data_rep, log_rep_empty. cancel.
        apply avail_region_grow_all; auto.

      + (* Header change was lost *)
        autorewrite with crash_xform. norm'l; unfold stars; simpl.
        autorewrite with crash_xform. cancel.

        or_r. or_r. or_l.
        unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
        cancel. cancel.
        rewrite replay_twice; eauto.

    - (* NoTransaction new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. cancel.

      or_r. or_r. or_r.
      unfold rep_inner, data_rep, log_rep_empty. cancel.

    Grab Existential Variables.
    all: eauto.
  Qed.

  Hint Rewrite crash_xform_would_recover_either_pred' : crash_xform.

  Lemma after_crash_pred'_would_recover_either_pred' : forall fsxp old curpred,
    after_crash_pred' fsxp old curpred =p=>
    would_recover_either_pred' fsxp old curpred.
  Proof.
    unfold after_crash_pred', would_recover_either_pred'.
    intros; norm'l; unfold stars; simpl.
    rewrite sep_star_comm. rewrite star_emp_pimpl.
    repeat apply pimpl_or_l.
    cancel.
    cancel.
    cancel.
    (* the automated search takes too long to get to the 8th OR branch.. *)
    norm; unfold stars; simpl; auto.
    repeat or_r. cancel.
  Qed.

  Theorem recover_ok: forall xp cs,
    {< m1 m2pred F,
    PRE
      exists d, BUFCACHE.rep cs d *
      [[ crash_xform (F * would_recover_either_pred' xp m1 m2pred)%pred d ]]
    POST RET:mscs
      rep xp (crash_xform F) (NoTransaction m1) mscs \/
      exists m2,
      rep xp (crash_xform F) (NoTransaction m2) mscs * [[ m2pred (list2mem m2) ]]
    CRASH
      would_recover_either_pred xp (crash_xform F) m1 m2pred
    >} recover xp cs.
  Proof.
    unfold recover, would_recover_either_pred.
    intros.
    eapply pimpl_ok2; eauto with prog.
    intros. norm'l. unfold stars; simpl.

    (* We need to split up all of the possible [rep] preconditions, because
     * this will decide what disk image to use for instantiating our evars.
     * We convert [crash_xform would_recover_either_pred'] into [after_crash_pred'],
     * which has fewer distinct states.
     *)

    (* XXX an odd setoid_rewrite issue: can't rewrite the top-level term? *)
    apply crash_xform_sep_star_dist in H4.
    autorewrite with crash_xform in H4.
    unfold after_crash_pred' in H4.
    destruct_lift H4.
    repeat ( apply sep_star_or_distr in H; apply pimpl_or_apply in H; destruct H;
      destruct_lift H ).

    - (* NoTransaction old *)
      cancel. instantiate (1:=ms_empty).
      unfold rep_inner, data_rep, synced_list.
      cancel.
      unfold log_rep_empty, log_rep, cur_rep.
      rewrite MapProperties.cardinal_1 by apply Map.empty_1.
      rewrite Nat.sub_0_r. ring_simplify (LogData xp ^+ $0).
      cancel.

      autorewrite with core.
      step.
      step.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'; cancel.
      autorewrite with core; cancel.
      unfold would_recover_either_pred'; cancel.

    - (* CommittedTxn old *)
      cancel.
      step.
      step.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'; cancel.
      cancel.
      unfold would_recover_either_pred'; cancel.

    - (* CommittedTxn new *)
      cancel.
      step.
      step.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'. norm; unfold stars; simpl; auto. repeat or_r. cancel.
      cancel.
      unfold would_recover_either_pred'; cancel.

    - (* NoTransaction new *)
      cancel. instantiate (1:=ms_empty).
      unfold rep_inner, data_rep, synced_list.
      cancel.
      unfold log_rep_empty, log_rep, cur_rep.
      rewrite MapProperties.cardinal_1 by apply Map.empty_1.
      rewrite Nat.sub_0_r. ring_simplify (LogData xp ^+ $0).
      cancel.

      autorewrite with core.
      step.
      step.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'; cancel.
      unfold would_recover_either_pred'. norm; unfold stars; simpl; auto. repeat or_r. cancel.
      autorewrite with core; cancel.
      unfold would_recover_either_pred'; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.

  Definition read_array T xp a i stride mscs rx : prog T :=
    let^ (mscs, r) <- read xp (a ^+ i ^* stride) mscs;
    rx ^(mscs, r).

  Definition write_array T xp a i stride v mscs rx : prog T :=
    mscs <- write xp (a ^+ i ^* stride) v mscs;
    rx mscs.

  Theorem read_array_ok : forall xp mscs a i stride,
    {< mbase m vs F,
    PRE
      rep xp F (ActiveTxn mbase m) mscs *
      [[ exists F', (array a vs stride * F')%pred (list2mem m) ]] *
      [[ wordToNat i < length vs ]]
    POST RET:^(mscs,r)
      [[ r = sel vs i $0 ]] * rep xp F (ActiveTxn mbase m) mscs
    CRASH
      exists mscs', rep xp F (ActiveTxn mbase m) mscs'
    >} read_array xp a i stride mscs.
  Proof.
    unfold read_array.
    hoare.

    pred_apply.
    rewrite isolate_fwd with (i:=i) by auto.
    cancel.
  Qed.

  Theorem write_array_ok : forall xp a i stride v mscs,
    {< mbase m vs F F',
    PRE
      rep xp F (ActiveTxn mbase m) mscs *
      [[ (array a vs stride * F')%pred (list2mem m) ]] *
      [[ wordToNat i < length vs ]]
    POST RET:mscs
      exists m', rep xp F (ActiveTxn mbase m') mscs *
      [[ (array a (Array.upd vs i v) stride * F')%pred (list2mem m') ]]
    CRASH
      exists m' mscs', rep xp F (ActiveTxn mbase m') mscs'
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

(*
  Section RECOVER_CORR3.

  Variable main_prog : forall T, memstate_cachestate ->
                                 ((memstate_cachestate * (bool * unit)) -> prog T) -> prog T.

  Theorem recover_corr2_to_corr3: forall mscs (pre post: pred) xp cachesize,
    {< mbase F,
    PRE             rep xp F (NoTransaction mbase) mscs * 
                    [[ pre (list2mem mbase)]]
    POST RET:^(mscs, r)
                    [[ r = false ]] * rep xp F (NoTransaction mbase) mscs \/
                    [[ r = true ]] * exists m', rep xp F (NoTransaction m') mscs *
                    [[ post (list2mem m') ]]
    CRASH           would_recover_old xp F mbase \/
                    exists m', would_recover_either xp F mbase m' *
                    [[ post (list2mem m') ]]
    >} main_prog mscs ->
    {<< mbase F,
    PRE             [[ cachesize <> 0 ]] *
                    rep xp F (NoTransaction mbase) mscs * 
                    [[ pre (list2mem mbase)]]
    POST RET:^(mscs, r)
                    [[ r = false ]] * rep xp F (NoTransaction mbase) mscs \/
                    [[ r = true ]] * exists m', rep xp F (NoTransaction m') mscs *
                    [[ post (list2mem m') ]]
    REC RET:^(mscs, fsxp)
                    (rep fsxp.(FSXPMemLog) F (NoTransaction mbase) mscs \/
                    exists m', rep fsxp.(FSXPMemLog) F (NoTransaction m') mscs *
                    [[ post (list2mem m') ]])
    >>} main_prog mscs >> recover cachesize.
  Proof.
    intros.
    unfold forall_helper; intros mbase F.
    exists (would_recover_old xp F mbase \/
            exists m', (would_recover_either xp F mbase m') *
            [[ post (list2mem m') ]])%pred; intros.

    eapply pimpl_ok3.
    eapply corr3_from_corr2.
    eauto.
    eapply recover_ok.
    simpl.
    cancel.
    step.
    auto.
    cancel.
    cancel.
    autorewrite with crash_xform.
    rewrite sep_star_or_distr.
    apply pimpl_or_l.
    cancel.
    autorewrite with crash_xform.
    apply pimpl_or_r; left; cancel.
    instantiate (p := crash_xform p); cancel.
    repeat destruct_type unit.

    step.
    rewrite sep_star_or_distr.
    apply pimpl_or_r; left; cancel.
    rewrite H4; auto.
    rewrite H4; cancel.
    apply pimpl_or_r; left; cancel.

    cancel.
    autorewrite with crash_xform.
    apply pimpl_or_r; right; cancel.
    repeat destruct_type unit.
    step.
    rewrite H4; cancel.
    cancel.
    rewrite H4; cancel.
    cancel.
    rewrite H4; cancel.
    cancel.
  Qed.

  End RECOVER_CORR3.
*)

  Hint Extern 0 (okToUnify (rep _ _ _ ?a) (rep _ _ _ ?a)) => constructor : okToUnify.

  (* XXX remove once SepAuto and SepAuto2 are unified *)
  Hint Extern 0 (SepAuto.okToUnify (rep _ _ _ ?a) (rep _ _ _ ?a)) => constructor : okToUnify.

End MEMLOG.



Global Opaque MEMLOG.write.
Arguments MEMLOG.rep : simpl never.
