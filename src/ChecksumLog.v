Require Import Hashmap.
Require Import Word.
Require Import Prog.
Require Import BasicProg.
Require Import Hoare.
Require Import Pred.
Require Import Array.
Require Import List.
Require Import SepAuto2.
Require Import Cache.
Require Import Omega.
Require Import GenSep.
Require Import PredCrash.
Require Import Rec.
Require Import Eqdep_dec.

Import ListNotations.
Set Implicit Arguments.

Definition header_type : Rec.type := Rec.RecF ([
    ("previous_length",  Rec.WordF addrlen);
    ("current_length",  Rec.WordF addrlen);
    ("checksum",   Rec.WordF hashlen);
    ("padding", Rec.WordF (valulen - hashlen - addrlen - addrlen))
  ]).
Definition header := Rec.data header_type.
Definition make_header : header := (@Rec.of_word header_type $0)
                                :=> "checksum" := default_hash.

Theorem header_len :
  valulen = Rec.len header_type.
Proof.
  simpl. rewrite valulen_is. compute. auto.
Qed.

Definition header_to_valu (h : header) : valu.
  rewrite header_len.
  exact (Rec.to_word h).
Defined.

Definition valu_to_header (v : valu) : header.
  rewrite header_len in *.
  exact (Rec.of_word v).
Defined.

Lemma of_to_header : forall h,
  valu_to_header (header_to_valu h) = h.
Proof.
  intros.
  destruct h.
  unfold valu_to_header, header_to_valu.
  unfold eq_rec_r, eq_rec.
  rewrite eq_rect_nat_double.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  repeat rewrite Rec.of_to_id.
  reflexivity.

  unfold Rec.well_formed.
  simpl.
  intuition.
Qed.


Parameter maxlen : addr.
Definition Header : addr := $0.
Definition DataStart : addr := $1.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

Check header_to_valu.

Definition hide_rec p : Prop := p.
Opaque hide_rec.


Definition log_rep_inner previous_length header vl hm :=
  (exists h current_length,
    let header' := make_header
      :=> "previous_length" := ($ previous_length)
      :=> "current_length"  := ($ current_length)
      :=> "checksum"        := h
    in
    hash_list_rep (rev vl) h hm /\
      length vl = current_length /\
      current_length <= # (maxlen) /\
      previous_length <= # (maxlen) /\
      hide_rec (header = header')).

(** Log_rep:
  - The current list of values in the log is a prefix of the disk.
  - The checksum and current_length in the header matches the current
    list of values (previous_length can be anything)
  Eventually current_length can live in memory **)
Definition log_rep previous_length vl hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header,
    [[ log_rep_inner previous_length header vl hm ]] *
    Header |-> (header_to_valu header, nil) *
    array DataStart (combine vl (repeat nil (length vl))) $1)%pred.

(*Definition log_rep' vl hm cs d F : pred :=
  BUFCACHE.rep cs d *
  [[ (log_rep vl hm * F)%pred d ]].*)

Definition log_rep_crash_xform (vl : list valu) hm :
  @pred addr (@weq addrlen) valuset :=
  (exists previous_length header vl vl',
    [[ log_rep_inner previous_length header vl' hm ]] *
    Header |-> (header_to_valu header, nil) *
    array DataStart (combine vl (repeat nil (length vl))) $1)%pred.

Definition crep (vl : list valu) hm :
  @pred addr (@weq addrlen) valuset :=
  (exists previous_length header header' vl vl' vl'',
    [[ log_rep_inner (length vl') header' vl'' hm ]] *
    [[ log_rep_inner previous_length header vl' hm ]] *
    Header |-> (header_to_valu header', header_to_valu header :: nil) *
    array DataStart (combine vl (repeat nil (length vl))) $1)%pred.

(*Definition crep vdisk hm :
  @pred addr (@weq addrlen) valuset :=
  (exists previous_length vl next_vl h next_h current_length next_length header next_header unsynced_data,
    [[ log_rep_recovered_inner vl previous_length current_length h header hm ]] *
    [[ log_rep_recovered_inner next_vl current_length next_length next_h next_header hm ]] *
    [[ length vdisk = # (maxlen) ]] *
    (Header |-> (header_to_valu header, nil) \/
      Header |-> (header_to_valu next_header, header_to_valu header :: nil)) *
    array DataStart (combine vdisk (updN (repeat nil # (maxlen)) current_length unsynced_data)) $1
  )%pred.*)

Definition append T v cs rx : prog T :=
  let^ (cs, header_valu) <- BUFCACHE.read Header cs;
  let header := valu_to_header header_valu in
  let log_pointer := header :-> "current_length" in
  checksum <- Hash (Word.combine v (header :-> "checksum"));
  cs <- BUFCACHE.write (DataStart ^+ log_pointer) v cs;
  cs <- BUFCACHE.write Header (header_to_valu (
          make_header
            :=> "previous_length" := log_pointer
            :=> "current_length" := log_pointer ^+ $1
            :=> "checksum" := checksum
          )) cs;
  cs <- BUFCACHE.sync (DataStart ^+ log_pointer) cs;
  cs <- BUFCACHE.sync Header cs;
  rx cs.

Definition truncate T cs rx : prog T :=
  hash0 <- Hash default_valu;
  cs <- BUFCACHE.write Header (header_to_valu (
          make_header
            :=> "previous_length" := $0 (* Could keep the previous length, but not much point... *)
            :=> "current_length"  := $0
            :=> "checksum"        := hash0
          )) cs;
  cs <- BUFCACHE.sync Header cs;
  rx cs.

Ltac unhide_rec :=
  match goal with
  | [H: hide_rec _ |- _ ] => inversion H
  end;
  subst.

Theorem append_ok : forall v cs,
  {< d previous_length vl F v_old,
  PRE:hm
    [[ length vl < # (maxlen) ]] *
    BUFCACHE.rep cs d *
    [[ (log_rep previous_length vl hm *
        (DataStart ^+ $ (length vl)) |-> (v_old, nil) * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      [[ (log_rep (length vl) (vl ++ v :: nil) hm' * F)%pred d' ]]
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' *
      [[ ((log_rep_crash_xform vl hm' * (DataStart ^+ $ (length vl)) |->?
          \/ log_rep_crash_xform (vl ++ v :: nil) hm'
          \/ crep vl hm' * (DataStart ^+ $ (length vl)) |->?) * F)%pred d' ]]
  >} append v cs.
Proof.
  unfold append, log_rep, log_rep_inner.
  step.
  pred_apply; cancel.

  step.
  rewrite of_to_header.
  simpl.
  step.
  Transparent hide_rec.
  unhide_rec.
  cancel.

  step.
  pred_apply; cancel.
  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.
  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.

  step_idtac.
  unhide_rec.
  rewrite array_isolate with (vs:=(combine (l ++ [v]) (repeat [] (length l + 1))))
    (i:=$ (length l)).
  rewrite wmult_comm, wmult_unit.
  unfold sel.
  rewrite wordToNat_natToWord_bound with (bound:=maxlen); try omega.
  rewrite skipn_oob.
  rewrite firstn_combine_comm, firstn_app, firstn_repeat, selN_combine,
      selN_last, repeat_selN; try omega.
  cancel.
  rewrite app_length, repeat_length; auto.
  rewrite combine_length. rewrite app_length, repeat_length.
  rewrite min_r; simpl; try omega.
  rewrite combine_length. rewrite app_length, repeat_length.
  rewrite wordToNat_natToWord_bound with (bound:=maxlen); try omega.
  rewrite min_r; simpl; try omega.

  unhide_rec.
  repeat eexists.

  rewrite rev_unit.
  solve_hash_list_rep.
  solve_hash_list_rep.
  eauto.

  intuition.
  eapply hashmap_get_subset.
  rewrite upd_hashmap'_eq. eauto.
  intuition.
  unfold hash2, hash_safe in *.
  rewrite H13 in H17.
  intuition.
  contradict_hashmap_get_default H15 hm0.
  contradict_hashmap_get_default H15 hm0.
  instantiate (Goal13:=hm0).
  solve_hashmap_subset.

  omega.
  omega.

  unfold hide_rec.
  unhide_rec.
  rewrite natToWord_plus.
  unfold hash2.
  auto.

  cancel_with eauto.
  pred_apply; cancel.
  apply pimpl_or_r. right.
  apply pimpl_or_r. right.
  unfold crep.
  unhide_rec.
  cancel.
  unfold log_rep_inner.
  eexists.
  exists (length l + 1).
  intuition.
  instantiate (a16:=l ++ [v]).
  rewrite rev_unit.
  solve_hash_list_rep.
  solve_hash_list_rep.
  eauto.

  eapply hashmap_get_subset.
  rewrite upd_hashmap'_eq. eauto.
  intuition.
  unfold hash2, hash_safe in *.
  rewrite H13 in H17.
  intuition.
  contradict_hashmap_get_default H15 hm0.
  contradict_hashmap_get_default H15 hm0.
  instantiate (Goal11:=hm0).
  solve_hashmap_subset.

  rewrite app_length; simpl.
  omega.
  eauto.

  unfold hide_rec.
  unhide_rec.
  unfold make_header.
  cbn.
  rewrite natToWord_plus.
  unfold hash2.
  reflexivity.

  unfold log_rep_inner.
  eexists.
  exists (length l).
  intuition.
  solve_hash_list_rep.

  unfold hide_rec.
  unhide_rec.
  cbn.
  rewrite Nat.min_l.
  eauto.
  omega.

  cancel_with eauto.
  pred_apply; cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  unfold log_rep_crash_xform.
  repeat (apply pimpl_exists_r; eexists).
  instantiate (x1:=l ++ [v]).
  rewrite array_isolate with (vs:=(combine (l ++ [v]) (repeat [] (length (l ++ [v]))))).
  instantiate (w0:=$ (length l)).
  rewrite wmult_comm, wmult_unit.
  unfold sel.
  rewrite wordToNat_natToWord_bound with (bound:=maxlen); try omega.
  rewrite skipn_oob.
  rewrite firstn_combine_comm, firstn_app, firstn_repeat, selN_combine,
      selN_last, repeat_selN; try omega.
  unhide_rec.
  cancel.

  unfold log_rep_inner.
  eexists.
  exists (length l + 1).
  intuition.
  instantiate (x2:=l ++ [v]).
  rewrite rev_unit.
  solve_hash_list_rep.
  solve_hash_list_rep.
  eauto.

  eapply hashmap_get_subset.
  rewrite upd_hashmap'_eq. eauto.
  intuition.
  unfold hash2, hash_safe in *.
  rewrite H13 in H17.
  intuition.
  contradict_hashmap_get_default H15 hm0.
  contradict_hashmap_get_default H15 hm0.
  instantiate (Goal20:=hm0).
  solve_hashmap_subset.

  rewrite app_length; simpl.
  omega.

  unfold hide_rec.
  unhide_rec.
  cbn.
  rewrite Nat.min_l; eauto.
  rewrite natToWord_plus.
  unfold hash2.
  reflexivity.

  rewrite app_length; simpl.
  omega.
  rewrite app_length, repeat_length; simpl.
  omega.
  rewrite app_length; simpl.
  omega.
  rewrite combine_length, repeat_length, app_length; simpl.
  rewrite min_r; omega.


  erewrite wordToNat_natToWord_bound with (bound:=maxlen);
    try rewrite combine_length, repeat_length, app_length, min_r; simpl; omega.

  cancel_with eauto.
  pred_apply; cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  unfold crep.
  unhide_rec.
  cancel.
  unfold log_rep_inner.
  eexists.
  exists (length l + 1).
  intuition.
  instantiate (a12:=l ++ [v]).
  rewrite rev_unit.
  solve_hash_list_rep.
  solve_hash_list_rep.
  eauto.

  eapply hashmap_get_subset.
  rewrite upd_hashmap'_eq. eauto.
  intuition.
  unfold hash2, hash_safe in *.
  rewrite H12 in H17.
  intuition.
  contradict_hashmap_get_default H13 hm0.
  contradict_hashmap_get_default H13 hm0.
  instantiate (Goal10:=hm0).
  solve_hashmap_subset.

  rewrite app_length; simpl.
  omega.
  eauto.

  unfold hide_rec.
  unhide_rec.
  unfold make_header.
  cbn.
  rewrite natToWord_plus.
  unfold hash2.
  reflexivity.

  unfold log_rep_inner.
  eexists.
  exists (length l).
  intuition.
  solve_hash_list_rep.

  unfold hide_rec.
  unhide_rec.
  cbn.
  rewrite Nat.min_l.
  eauto.
  omega.

  all: cancel_with eauto.
  Grab Existential Variables.
  auto.
Qed.

Theorem truncate_ok : forall cs,
  {< d previous_length vl F,
  PRE:hm
    BUFCACHE.rep cs d *
    [[ (log_rep previous_length vl hm * F)%pred d ]]
  POST:hm' RET:cs'
    exists d' vl,
    BUFCACHE.rep cs' d' *
    [[ (log_rep 0 nil hm' * array DataStart vl $1 * F)%pred d' ]]
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' (** TODO **)
  >} truncate cs.
Proof.
  unfold truncate, log_rep, log_rep_inner.
  step.
  step.
  step.
  step.
  solve_hash_list_rep; eauto.
  unfold hide_rec.
  auto.
Qed.