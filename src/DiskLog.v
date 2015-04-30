Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Eqdep_dec.
Require Import Pred.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import GenSep.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Import ListNotations.

Set Implicit Arguments.

Definition log_contents := list (addr * valu).

Inductive state :=
| Synced (l: log_contents)
(* The log is synced on disk *)

| Shortened (old: log_contents) (new_length: nat)
(* The log has been shortened; the contents are still synced but the length is potentially unsynced *)

| Extended (old: log_contents) (appended: log_contents).
(* The log has been extended; the new contents are synced but the length is potentially unsynced *)

Module DISKLOG.

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
    unfold zext.
    autorewrite with core.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.

  Definition addr_per_block := valulen / addrlen.
  Definition descriptor_type := Rec.ArrayF (Rec.WordF addrlen) addr_per_block.
  Definition descriptor := Rec.data descriptor_type.
  Theorem descriptor_sz_ok : valulen = Rec.len descriptor_type.
  Proof.
    simpl. unfold addr_per_block. rewrite valulen_is. vm_compute. reflexivity.
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
    autorewrite with core.
    trivial.
  Qed.

  Theorem descriptor_valu_id : forall d,
    Rec.well_formed d -> valu_to_descriptor (descriptor_to_valu d) = d.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite descriptor_sz_ok.
    autorewrite with core.
    apply Rec.of_to_id; auto.
  Qed.

  Theorem valu_to_descriptor_length : forall v,
    length (valu_to_descriptor v) = addr_per_block.
  Proof.
    unfold valu_to_descriptor.
    intros.
    pose proof (@Rec.of_word_length descriptor_type).
    unfold Rec.well_formed in H.
    simpl in H.
    apply H.
  Qed.
  Hint Resolve valu_to_descriptor_length.

  Lemma descriptor_to_valu_zeroes: forall l n,
    descriptor_to_valu (l ++ repeat $0 n) = descriptor_to_valu l.
  Proof.
    unfold descriptor_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite descriptor_sz_ok.
    autorewrite with core.
    apply Rec.to_word_append_zeroes.
  Qed.

  Definition valid_xp xp :=
    wordToNat (LogLen xp) <= addr_per_block /\
    (* The log shouldn't overflow past the end of disk *)
    goodSize addrlen (# (LogData xp) + # (LogLen xp)).

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

  Lemma length_synced_list : forall l,
    length (synced_list l) = length l.
  Proof.
    unfold synced_list; intros.
    rewrite combine_length. autorewrite with core. auto.
  Qed.

  Definition valid_size xp (l: log_contents) :=
    length l <= wordToNat (LogLen xp).

  (** On-disk representation of the log *)
  Definition log_rep_synced xp (l: log_contents) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_size xp l ]] *
      exists rest,
      (LogDescriptor xp) |=> (descriptor_to_valu (map fst l ++ rest)) *
      [[ @Rec.well_formed descriptor_type (map fst l ++ rest) ]] *
      array (LogData xp) (synced_list (map snd l)) $1 *
      avail_region (LogData xp ^+ $ (length l))
                         (wordToNat (LogLen xp) - length l))%pred.


  Definition rep_inner xp (st: state) :=
    (* For now, support just one descriptor block, at the start of the log. *)
    ([[ valid_xp xp ]] *
    match st with
    | Synced l =>
      (LogHeader xp) |=> (header_to_valu (mk_header (length l)))
    * log_rep_synced xp l

    | Shortened old len =>
      [[ len <= length old ]]
    * (LogHeader xp) |-> ($ len, $ (length old) :: [])
    * log_rep_synced xp old

    | Extended old appended =>
      (LogHeader xp) |-> ($ (length old + length appended), $ (length old) :: [])
    * log_rep_synced xp (old ++ appended)

    end)%pred.

  Definition rep xp F st cs := (exists d,
    BUFCACHE.rep cs d * [[ (F * rep_inner xp st)%pred d ]])%pred.

  Ltac disklog_unfold := unfold rep, rep_inner, valid_xp, log_rep_synced, synced_list.

  Definition read_log T (xp : log_xparams) cs rx : prog T :=
    let^ (cs, d) <- BUFCACHE.read (LogDescriptor xp) cs;
    let desc := valu_to_descriptor d in
    let^ (cs, h) <- BUFCACHE.read (LogHeader xp) cs;
    let len := (valu_to_header h) :-> "length" in
    let^ (cs, log) <- For i < len
    Ghost [ cur log_on_disk F ]
    Loopvar [ cs log_prefix ]
    Continuation lrx
    Invariant
      rep xp F (Synced log_on_disk) cs
    * [[ log_prefix = firstn (# i) log_on_disk ]]
    OnCrash
      exists cs, rep xp F (Synced cur) cs
    Begin
      let^ (cs, v) <- BUFCACHE.read_array (LogData xp) i cs;
      lrx ^(cs, log_prefix ++ [(sel desc i $0, v)])
    Rof ^(cs, []);
    rx ^(log, cs).

  Theorem read_log_ok: forall xp cs,
    {< l F,
    PRE
      rep xp F (Synced l) cs
    POST RET:^(r,cs)
      [[ r = l ]] * rep xp F (Synced l) cs
    CRASH
      exists cs', rep xp F (Synced l) cs'
    >} read_log xp cs.
  Proof.
    unfold read_log; disklog_unfold.
    intros.
    eapply pimpl_ok2; [ solve [ eauto with prog ] | ].
    intros. (* XXX this hangs: autorewrite_fast_goal. *)
    cancel.
    eapply pimpl_ok2; [ solve [ eauto with prog ] | ].
    cancel.
    eapply pimpl_ok2; [ solve [ eauto with prog ] | ].
    intros. norm. (* XXX the VARNAME system makes everything a mess here *)


    (* eapply pimpl_ok2; [ eauto with prog |]
    instantiate (1 := (List.combine (map snd (Map.elements (elt:=valu) m))
     (repeat [] (length (map snd (Map.elements (elt:=valu) m)))))).
    autorewrite_fast. cancel.
    rewrite header_valu_id in *.
    rec_simpl.
    simpl in H.
    solve_lengths.
    eauto with replay.
    rewrite header_valu_id in *.
    rec_simpl.
    assert (# m1 < length (Map.elements m)).
    solve_lengths.
    replace (# (m1 ^+ $ 1)) with (# m1 + 1).
    erewrite firstn_plusone_selN'.
    eauto.
    rewrite descriptor_valu_id.
    unfold sel.
    rewrite selN_app1 by solve_lengths.
    autorewrite with lists.
    repeat erewrite selN_map by auto.
    simpl.
    rewrite <- surjective_pairing.
    auto.
    solve_lengths.
    unfold Rec.well_formed; simpl.
    intuition.
    auto.
    word2nat_clear.
    word2nat_auto.
    cancel.
    eauto with replay.
    eauto.
    rewrite header_valu_id.
    rewrite firstn_oob.
    apply MapProperties.of_list_3.
    rec_simpl.
    simpl.
    solve_lengths.
    eauto with replay.
    cancel.
    auto.
    Unshelve.
    repeat constructor. exact $0. *)
  Qed.

  Hint Extern 1 ({{_}} progseq (read_log _ _) _) => apply read_log_ok : prog.

End DISKLOG.