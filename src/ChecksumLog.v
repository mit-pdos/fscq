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
Require Import HashmapProg.

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

Definition synced l : list valuset :=
  List.combine l (repeat nil (length l)).

Check header_to_valu.

Definition hide_rec p : Prop := p.
Opaque hide_rec.

(** Previous length doesn't need to be less than current_length,
    but if we can guarantee that after a crash, it will be much
    easier to prove that it's okay to roll back to the previous
    length. *)
Definition log_rep_inner header previous_length vl hm :=
  (exists h current_length,
    let header' := make_header
      :=> "previous_length" := ($ previous_length)
      :=> "current_length"  := ($ current_length)
      :=> "checksum"        := h
    in
    hash_list_rep (rev vl) h hm /\
      length vl = current_length /\
      current_length <= # (maxlen) /\
      previous_length <= current_length /\
      hide_rec (header = header')).

(** THE invariant? Whatever is in the header, out of the values
  that we hope are on disk, the first previous_length of them are
  definitely synced.*)
Definition log_rep_unmatched previous_length vl hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header,
    [[ log_rep_inner header previous_length vl hm ]]
    * array DataStart (synced (firstn previous_length vl)) $1)%pred.

(** There is a synced header on disk and an array of synced
  values that matches it.
**)
Definition log_rep previous_length vl hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header,
    [[ log_rep_inner header previous_length vl hm ]]
    * Header |-> (header_to_valu header, nil)
    * array DataStart (synced vl) $1)%pred.

Definition log_rep_crash_xform previous_length vl vl' hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header,
    [[ log_rep_inner header previous_length vl hm ]]
    * Header |-> (header_to_valu header, nil)
    * [[ length vl = length vl' ]]
    * [[ firstn previous_length vl' = firstn previous_length vl ]]
    * array DataStart (synced vl') $1)%pred.

(** If the append crashes in the middle, there may be an
  unsynced header at the Header block. The original array
  at DataStart will remain synced (captured by the first
  log_rep_invariant).
**)
Definition crep previous_length vl vl' hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header header',
    [[ log_rep_inner header' (length vl) vl' hm ]] *
    [[ log_rep_inner header previous_length vl hm ]] *
    Header |-> (header_to_valu header', header_to_valu header :: nil) *
    array DataStart (synced vl) $1)%pred.

(** crep can sync to the old or new header
  - old header: vl has remained synced on disk, so we're back
    in log_rep for the previous_length
  - new header: vl has remained synced on disk, but the rest
    of vl' may not match
  TODO: generalize vl ++ [v] to any vl'
**)
Lemma crep_crash_xform : forall previous_length vl v hm,
  crash_xform (crep previous_length vl (vl ++ [v]) hm
    * (DataStart ^+ $(length vl)) |->?)
    =p=> (exists v, log_rep previous_length vl hm * (DataStart ^+ $(length vl)) |-> (v, nil)) \/
        (exists vl', log_rep_crash_xform previous_length vl vl' hm).

(** log_rep after a crash: Same as normal log_rep, except we don't
    know if the list that matches the hash we have matches the list
    that's on disk.
Definition log_rep_crash_xform previous_length (vl : list valu) hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header vl',
    [[ log_rep_inner previous_length header vl hm ]] *
    Header |-> (header_to_valu header, nil) *
    [[ length vl <= length vl' ]] *
    [[ length vl' <= # (maxlen) ]] *
    array DataStart (combine vl' (repeat nil (length vl'))) $1)%pred.

(** The one in-between case right before a crash:
  - Two possible headers could be synced to disk
  - The older one matches the list on disk,
    the other matches a longer list. **)
Definition crep previous_length (vl vl' : list valu) hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header header' vl'',
    [[ log_rep_inner (length vl) header' vl' hm ]] *
    [[ log_rep_inner previous_length header vl hm ]] *
    [[ length vl' <= length vl'' ]] *
    [[ length vl'' <= # (maxlen) ]] *
    Header |-> (header_to_valu header', header_to_valu header :: nil) *
    array DataStart (combine vl'' (repeat nil (length vl''))) $1)%pred.*)


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

Definition read_log T pointer cs rx : prog T :=
  let^ (cs, values) <- For i < pointer
  Hashmap hm'
  Ghost [ crash F l ]
  Loopvar [ cs values ]
  Continuation lrx
  Invariant
    exists d', BUFCACHE.rep cs d'
    * [[ (F * array DataStart (synced l) $1
        * [[ # (pointer) <= length l ]]
        * [[ values = firstn # (i) l ]])%pred d' ]]
  OnCrash crash
  Begin
    let^ (cs, v) <- BUFCACHE.read_array DataStart i cs;
    lrx ^(cs, values ++ [v])
  Rof ^(cs, []);
  rx ^(cs, values).

Theorem read_log_ok : forall pointer cs,
  {< d F values,
  PRE
    BUFCACHE.rep cs d
    * [[ (F * array DataStart (synced values) $1)%pred d ]]
    * [[ # (pointer) <= length values ]]
  POST RET:^(cs', values')
      BUFCACHE.rep cs' d
      * [[ (F * array DataStart (synced values) $1)%pred d ]]
      * [[ values' = firstn # (pointer) values ]]
  CRASH
    exists cs',
      BUFCACHE.rep cs' d
      * [[ (F * array DataStart (synced values) $1)%pred d ]]
  >} read_log pointer cs.
Proof.
  Admitted. (*
  unfold read_log.
  hoare.
  pred_apply; cancel_with eauto.

  rewrite combine_length, repeat_length.
  rewrite min_l; try omega. Search lt wlt.
  apply wlt_lt in H0.
  omega.

  erewrite <- natplus1_wordplus1_eq; eauto.
  erewrite firstn_plusone_selN'; eauto.
  rewrite selN_combine; simpl; auto.
  rewrite repeat_length; auto.
  apply wlt_lt in H0.
  omega.
  unfold addrlen; omega.

  cancel.
Qed.*)

Hint Extern 1 ({{_}} progseq (read_log _ _) _) => apply read_log_ok : prog.

Definition recover T cs rx : prog T :=
  let^ (cs, header_valu) <- BUFCACHE.read Header cs;
  let header := valu_to_header header_valu in
  let rollback_pointer := header :-> "previous_length" in
  let log_pointer := header :-> "current_length" in
  let checksum := header :-> "checksum" in
  let^ (cs, values) <- read_log log_pointer cs;
  h <- hash_list values;
  If (weq checksum h) {
    rx ^(cs, true)
  } else {
    h <- hash_list (firstn # (rollback_pointer) values);
    cs <- BUFCACHE.write Header (header_to_valu (
            make_header
              :=> "previous_length" := rollback_pointer
              :=> "current_length" := rollback_pointer
              :=> "checksum" := h
            )) cs;
    cs <- BUFCACHE.sync Header cs;
    rx ^(cs, false)
  }.

Ltac unhide_rec :=
  match goal with
  | [H: hide_rec _ |- _ ] => inversion H
  end;
  subst.

Ltac solve_bound :=
  erewrite wordToNat_natToWord_bound with (bound:=maxlen); try omega.

Ltac solve_bound' H :=
  erewrite wordToNat_natToWord_bound with (bound:=maxlen) in H; try omega.

Theorem recover_ok :  forall cs,
  {< d F prev_len values dvalues,
  PRE:hm
    BUFCACHE.rep cs d
    * [[ (log_rep_crash_xform prev_len values dvalues hm
        * F)%pred d ]]
  POST:hm' RET:^(cs', ok)
    exists d',
      BUFCACHE.rep cs' d'
      * [[ (exists n,
          log_rep prev_len (firstn n values) hm'
          * array (DataStart ^+ $ (n)) (skipn n (synced dvalues)) $1
          * F)%pred d' ]]
  CRASH:hm'
    exists cs' d',
      BUFCACHE.rep cs' d'
  >} recover cs.
Proof.
  unfold recover, log_rep_crash_xform, log_rep_inner.
  step.
  pred_apply; cancel.
  step.
  pred_apply. instantiate (2:=l0). cancel.
  unhide_rec.
  rewrite of_to_header.
  cbn.
  solve_bound.

  step.
  unhide_rec.
  rewrite of_to_header.
  cbn.
  rewrite firstn_length.
  rewrite min_l.
  eapply goodSize_bound.
  repeat solve_bound; eauto.
  solve_bound.

  step.
  step.
  unfold log_rep, log_rep_inner.
  rewrite of_to_header in *.
  unhide_rec. cbn in *.
  instantiate (1:=length l).

  assert (l = l0).
    apply rev_injective.
    eapply hash_list_injective; solve_hash_list_rep.
    solve_hash_list_rep.
    match goal with
    | [ H: context[firstn _ _] |- _ ]
        => try solve_bound' H; rewrite firstn_oob in H; try omega
    end.
    solve_hash_list_rep.

  subst.
  cancel.
  erewrite <- firstn_skipn with (l:=(combine l0 (repeat [] (length l0)))) at 1.
  rewrite <- array_app.
  unfold synced; rewrite firstn_combine_comm.
  rewrite firstn_length, min_l; try omega.
  rewrite firstn_repeat; auto.
  cancel.
  rewrite firstn_length, combine_length, min_l; try omega; auto.
  rewrite repeat_length, min_l; try omega.

  repeat eexists.
  erewrite wordToNat_natToWord_bound with (bound:=maxlen) in H18; try omega.
  solve_hash_list_rep.
  rewrite firstn_length, min_l; omega.
  rewrite firstn_length, min_l; omega.

  Transparent hide_rec.
  unfold hide_rec.
  rewrite firstn_length, min_l; try omega.
  reflexivity.

  Opaque hide_rec.
  step.
  rewrite of_to_header.
  unhide_rec.
  cbn in *.
  repeat rewrite firstn_length;
  repeat rewrite min_l; repeat solve_bound.
  eapply goodSize_bound.
  solve_bound; eauto.

  rewrite of_to_header in *.
  cbn in *.
  step_idtac.
  cancel_with eauto.
  pred_apply; cancel.

  step_idtac.
  eauto.
  pred_apply; cancel.
  step.
  unfold log_rep, log_rep_inner.
  unhide_rec. cbn in *.
  instantiate (1:=n).
  cancel.
  match goal with
  | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite <- H
  end.

  erewrite <- firstn_skipn with (l:=(combine l0 (repeat [] (length l0)))) at 1.
  rewrite <- array_app.
  unfold synced; rewrite firstn_combine_comm.
  rewrite firstn_length, min_l; try omega.
  instantiate (1:=n).
  rewrite firstn_repeat; auto.
  cancel.
  omega.
  rewrite firstn_length, combine_length, min_l; try omega; auto.
  rewrite repeat_length, min_l; try omega.

  repeat eexists.
  Search hash_list_rep.
  Search firstn.
  rewrite firstn_firstn in H21.
  Search (# ($ (_))).
  repeat solve_bound' H21.
  rewrite min_l in H21; try omega.
  Search hash_list_rep.
  match goal with
  | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite <- H
  end.
  solve_hash_list_rep.
  rewrite firstn_length, min_l; try omega.
  rewrite firstn_length, min_l; try omega.

  Transparent hide_rec.
  unfold hide_rec.
  rewrite firstn_length, min_l; try omega.
  reflexivity.

  all: cancel_with eauto.
Qed.

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
      [[ ((log_rep_crash_xform previous_length vl hm' * (DataStart ^+ $ (length vl)) |->?
          \/ log_rep_crash_xform (length vl) (vl ++ v :: nil) hm'
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