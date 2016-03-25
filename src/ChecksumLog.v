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
(* TODO: Remove previous_length from args *)
Definition log_rep_inner header prev_len vl hm :=
  (exists h current_length,
    let header' := make_header
      :=> "previous_length" := ($ prev_len)
      :=> "current_length"  := ($ current_length)
      :=> "checksum"        := h
    in
    hash_list_rep (rev vl) h hm /\
      length vl = current_length /\
      current_length <= # (maxlen) /\
      hide_rec (header = header')).

(** There is a synced header on disk and an array of synced
  values that matches it.
**)
Definition log_rep vl hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header prev_len,
    [[ log_rep_inner header prev_len vl hm ]]
    * Header |-> (header_to_valu header, nil)
    * array DataStart (synced vl) $1)%pred.

Definition log_rep_crash_xform prev_vl vl vl_disk hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header,
    [[ log_rep_inner header (length prev_vl) vl hm ]]
    * Header |-> (header_to_valu header, nil)
    * [[ list_prefix prev_vl vl ]]
    * [[ list_prefix prev_vl vl_disk ]]
    * [[ length vl = length vl_disk ]]
    * array DataStart (synced vl_disk) $1)%pred.

(** If the append crashes in the middle, there may be an
  unsynced header at the Header block. The original array
  at DataStart will remain synced (captured by the first
  log_rep_invariant).
**)
Definition crep vl vl' hm :
  @pred addr (@weq addrlen) valuset :=
  (exists header header' prev_len,
    [[ log_rep_inner header' (length vl) vl' hm ]] *
    [[ log_rep_inner header prev_len vl hm ]] *
    (Header |-> (header_to_valu header', header_to_valu header :: nil) \/
      Header |-> (header_to_valu header, header_to_valu header' :: nil))*
    array DataStart (synced vl) $1)%pred.

(** crep can sync to the old or new header
  - old header: vl has remained synced on disk, so we're back
    in log_rep for the previous_length
  - new header: vl has remained synced on disk, but the rest
    of vl' may not match
  TODO: generalize vl ++ [v] to any vl'
**)
Lemma crep_crash_xform : forall vl vl' hm F,
  crash_xform (exists unsynced_data,
    crep vl vl' hm
    * [[ list_prefix vl vl' ]]
    * [[ length vl + length unsynced_data = length vl' ]]
    * array (DataStart ^+ $(length vl)) unsynced_data $1
    * F)
    =p=> exists unsynced_data,
          log_rep vl hm
          * [[ length vl + length unsynced_data = length vl' ]]
          * array (DataStart ^+ $(length vl)) (synced unsynced_data) $1
          * crash_xform F \/
          log_rep_crash_xform vl vl' unsynced_data hm
          * crash_xform F.
Proof.
Admitted.

Lemma crep_crash_xform_rollback : forall vl vl' hm F,
  crash_xform (
    crep vl vl' hm
    * [[ list_prefix vl' vl ]]
    * F)
    =p=> exists unsynced_data,
          log_rep vl hm
          * crash_xform F \/
          log_rep vl' hm
          * [[ length vl' + length unsynced_data = length vl ]]
          * array (DataStart ^+ $ (length vl')) (synced unsynced_data) $1
          * crash_xform F.
Proof.
Admitted.

Hint Rewrite crep_crash_xform : crash_xform.

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
  let^ (cs, header_valu) <- BUFCACHE.read Header cs;
  let header := valu_to_header header_valu in
  let log_pointer := header :-> "current_length" in
  hash0 <- Hash default_valu;
  cs <- BUFCACHE.write Header (header_to_valu (
          make_header
            :=> "previous_length" := log_pointer
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
    rx cs
  } else {
    h <- hash_list (firstn # (rollback_pointer) values);
    cs <- BUFCACHE.write Header (header_to_valu (
            make_header
              :=> "previous_length" := rollback_pointer
              :=> "current_length" := rollback_pointer
              :=> "checksum" := h
            )) cs;
    cs <- BUFCACHE.sync Header cs;
    rx cs
  }.

Lemma list_prefix_length : forall A (l1 l2 : list A),
  list_prefix l1 l2 -> length l1 <= length l2.
Proof.
  induction l1; intros; simpl.
  omega.

  unfold list_prefix in H.
  simpl in H.
  destruct l2; inversion H.
  apply IHl1 in H2.
  simpl.
  rewrite firstn_length, min_l; try omega.
Qed.

Ltac unhide_rec :=
  match goal with
  | [H: hide_rec _ |- _ ] => inversion H
  end;
  subst.

Ltac solve_bound :=
  erewrite wordToNat_natToWord_bound with (bound:=maxlen); try omega.

Ltac solve_bound' H :=
  erewrite wordToNat_natToWord_bound with (bound:=maxlen) in H; try omega.

Ltac solve_prefix_bound :=
  try solve_bound;
  repeat match goal with
  | [ H: list_prefix ?l _ |- _ ] => eapply list_prefix_length in H
  end; eauto; try omega.

Lemma skipn_combine_comm' : forall A B n (a : list A) (b : list B),
  skipn n (combine a b) = combine (skipn n a) (skipn n b).
Proof.
  induction n; auto.
  intros.
  apply skipn_combine_comm.
Qed.

Theorem recover_ok_log_rep : forall cs,
  {< F values,
  PRE:hm
    exists d,
    BUFCACHE.rep cs d
    * [[ (log_rep values hm * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d'
      * [[ (log_rep values hm' * F)%pred d' ]]
  CRASH:hm'
    exists cs' d',
      BUFCACHE.rep cs' d'
      * [[ (log_rep values hm' * F)%pred d' ]]
  >} recover cs.
Proof.
  unfold recover, log_rep, log_rep_inner.
  step.
  pred_apply; cancel.
  step.
  pred_apply.
  match goal with
  | [|- context[array DataStart (combine ?l _)] ] => instantiate (1:=l)
  end.
  cancel.
  rewrite of_to_header; cbn.
  unhide_rec.
  solve_bound.

  rewrite of_to_header; cbn.
  step.
  unhide_rec.
  rewrite firstn_length.
  rewrite min_l.
  eapply goodSize_bound.
  repeat solve_bound; eauto.
  solve_bound.

  step.
  {
    (* If hashes match. *)
    step_idtac.
    repeat eexists; eauto.
    solve_hash_list_rep.
  }
  {
    (* Else, data was corrupted (impossible case). *)
    eapply pimpl_ok2; eauto with prog.
    intros.
    unfold pimpl; intros.
    unhide_rec.
    match goal with
    | [ H: context[firstn # ($ _ )] |- _ ]
      => solve_bound' H; rewrite firstn_oob in H; auto
    end.
    match goal with
    | [ H: hash_list_rep _ _ _ |- _ ]
      => eapply hash_list_injective2 in H; try solve_hash_list_rep; rewrite H in *
    end.
    match goal with
    | [ H: context[_ -> False] |- _ ] => destruct_lift H; intuition
    end.
  }

  (* Crash condition. *)
  - repeat eexists; eauto.
    solve_hash_list_rep.
  - cancel.
  - repeat eexists; eauto.
    solve_hash_list_rep.
  - repeat eexists; eauto.
    solve_hash_list_rep.
Qed.

Theorem recover_ok_log_rep_crash_xform : forall cs,
  {< F values values',
  PRE:hm
    exists d,
    BUFCACHE.rep cs d
    * [[ (exists unsynced_data,
          log_rep_crash_xform values values' unsynced_data hm
          * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d'
      * [[ (exists dvalues,
          log_rep values hm'
          * [[ length values + length dvalues = length values' ]]
          * array (DataStart ^+ $ (length values)) (synced dvalues) $1
          * F \/
          log_rep values' hm'
          * F)%pred d' ]]
  CRASH:hm'
    exists cs' d',
      BUFCACHE.rep cs' d'
      * [[ (exists unsynced_data,
            log_rep values hm'
            * [[ length values + length unsynced_data = length values' ]]
            * array (DataStart ^+ $(length values)) (synced unsynced_data) $1
            * F \/
            log_rep_crash_xform values values' unsynced_data hm'
            * F \/
            crep values values' hm'
            * array (DataStart ^+ $ (length values)) (synced unsynced_data) $1
            * F)%pred d' ]]
>} recover cs.
Proof.
  unfold recover, log_rep_crash_xform, log_rep, log_rep_inner.
  step.
  pred_apply; cancel.
  step.
  pred_apply.
  match goal with
  | [|- context[array DataStart (combine ?l _)] ] => instantiate (1:=l)
  end.
  cancel.
  rewrite of_to_header; cbn.
  unhide_rec.
  solve_bound.

  rewrite of_to_header; cbn.
  step.
  unhide_rec.
  rewrite firstn_length.
  rewrite min_l.
  eapply goodSize_bound.
  repeat solve_bound; eauto.
  solve_bound.

  step.
  {
    (* If hashes match. *)
    step_idtac.
    right.
    pred_apply; cancel.

    unhide_rec.
    assert (Heq: l = l1).
      apply rev_injective.
      eapply hash_list_injective; solve_hash_list_rep.
      match goal with
      | [ H: context[firstn _ _] |- _ ]
          => try solve_bound' H; rewrite firstn_oob in H; try omega
      end.
      solve_hash_list_rep.
    cancel.

    repeat eexists; eauto.
    solve_hash_list_rep.
  }

  {
    (* Else, data was corrupted (rollback case). *)
    step.

    unhide_rec.
    repeat rewrite firstn_length;
    repeat rewrite min_l; repeat solve_bound.
    eapply goodSize_bound.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.

    unhide_rec.
    step_idtac.
    cancel_with eauto.
    pred_apply; cancel.

    step_idtac.
    eauto.
    pred_apply; cancel.
    step_idtac.
    left.
    unfold log_rep, log_rep_inner.
    unhide_rec. cbn in *.
    pred_apply; cancel.

    erewrite <- firstn_skipn at 1.
    rewrite <- array_app.
    unfold synced; rewrite firstn_combine_comm, skipn_combine_comm'.
    rewrite skipn_length, skipn_repeat; try omega.
    rewrite firstn_repeat; try omega.
    instantiate (2:=l).
    instantiate (1:=length l0).
    instantiate (1:=length l0).
    instantiate (1:=DataStart ^+ $(length l0)).
    cancel.

    replace (firstn (length l0) l) with l0;
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    auto.

    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.
    rewrite firstn_length, combine_length, min_l; try omega; auto.
    rewrite repeat_length, min_l; solve_prefix_bound.

    replace l0 with (firstn (length l0) l);
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    repeat eexists.
    match goal with
    | [ H: context[firstn _ (firstn _ _)] |- _ ]
      => rewrite firstn_firstn in H;
          solve_bound' H;
          solve_bound' H;
          rewrite min_l in H;
          solve_prefix_bound; try omega
    end.
    solve_hash_list_rep.
    solve_prefix_bound.
    rewrite firstn_length, min_l; solve_prefix_bound.
    instantiate (1:=length l0).
    rewrite firstn_length, min_l; solve_prefix_bound.
    reflexivity.
    rewrite skipn_length; solve_prefix_bound.

    cancel.
    repeat eexists.
    right; right.
    unfold crep, log_rep_inner.
    pred_apply; cancel.
    match goal with
    | [ |- context[array DataStart ?a $1] ]
      => erewrite <- firstn_skipn with (l:=a)
    end.
    match goal with
    | [ |- context[array (DataStart ^+ ?a)] ]
      => rewrite <- array_app with (a2:=DataStart ^+ a)
    end.
    unfold synced; rewrite firstn_combine_comm, skipn_combine_comm'.
    rewrite skipn_length, skipn_repeat; try solve [ solve_prefix_bound ].
    rewrite firstn_repeat; try solve [ solve_prefix_bound ].
    replace (firstn (length l0) l) with l0;
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      repeat match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
      cancel_with eauto.
      apply pimpl_or_r; right.
      cancel_with eauto.
      rewrite firstn_length, combine_length, min_l; solve_prefix_bound.
      rewrite repeat_length, min_l; try omega.

    repeat eexists.
    solve_hash_list_rep.
    omega.
    repeat eexists.
    match goal with
    | [ H: context[firstn _ (firstn _ _)] |- _ ]
      => rewrite firstn_firstn in H;
          solve_bound' H;
          solve_bound' H;
          rewrite min_l in H;
          try solve [ solve_prefix_bound ]
    end.
    replace l0 with (firstn (length l0) l);
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    solve_hash_list_rep.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.

    cancel_with eauto.
    repeat eexists.
    left.
    pred_apply; cancel.
    erewrite <- firstn_skipn at 1.
    rewrite <- array_app.
    unfold synced; rewrite firstn_combine_comm, skipn_combine_comm'.
    rewrite skipn_length, skipn_repeat; try omega.
    rewrite firstn_repeat; try omega.
    replace (firstn (length l0) l) with l0;
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    cancel.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.
    rewrite firstn_length, combine_length, min_l; solve_prefix_bound.
    rewrite repeat_length, min_l; solve_prefix_bound.

    repeat eexists; eauto.
    match goal with
    | [ H: context[firstn _ (firstn _ _)] |- _ ]
      => rewrite firstn_firstn in H;
          solve_bound' H;
          solve_bound' H;
          rewrite min_l in H;
          try solve [ solve_prefix_bound ]
    end.
    replace l0 with (firstn (length l0) l);
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    solve_hash_list_rep.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.
    rewrite skipn_length; solve_prefix_bound.

    cancel.
    repeat eexists.
    right; left.
    pred_apply; cancel.
    repeat eexists.
    solve_hash_list_rep.
    omega.

    cancel.
    repeat eexists.
    right; right.
    unfold crep, log_rep_inner.
    pred_apply; cancel.
    match goal with
    | [ |- context[array DataStart ?a $1] ]
      => erewrite <- firstn_skipn with (l:=a)
    end.
    match goal with
    | [ |- context[array (DataStart ^+ ?a)] ]
      => rewrite <- array_app with (a2:=DataStart ^+ a)
    end.
    unfold synced; rewrite firstn_combine_comm, skipn_combine_comm'.
    rewrite skipn_length, skipn_repeat; try omega.
    rewrite firstn_repeat; try omega.
    replace (firstn (length l0) l) with l0;
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    instantiate (1:=length l0).
    instantiate (1:=l).
    cancel_with eauto.
    apply pimpl_or_r; right.
    cancel_with eauto.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.
    rewrite firstn_length, combine_length, min_l; solve_prefix_bound.
    rewrite repeat_length, min_l; solve_prefix_bound.

    repeat eexists.
    solve_hash_list_rep.
    omega.
    repeat eexists.
      match goal with
      | [ H: context[firstn _ (firstn _ _)] |- _ ]
        => rewrite firstn_firstn in H;
            solve_bound' H;
            solve_bound' H;
            rewrite min_l in H;
            try solve [ solve_prefix_bound ]
      end.
    replace l0 with (firstn (length l0) l);
      try solve [ match goal with
      | [ H: firstn _ _ = firstn _ _ |- _ ] => rewrite H
      end;
      match goal with
      | [ H: list_prefix _ _ |- _ ] => unfold list_prefix in H; rewrite H
      end;
      auto ].
    solve_hash_list_rep.
    solve_prefix_bound.
    solve_prefix_bound.
    solve_prefix_bound.

    apply pimpl_or_r; right.
    apply pimpl_or_r; left.
    cancel.
    repeat eexists.
    solve_hash_list_rep.
    omega.
    unhide_rec.
    reflexivity.
  }

  (* Crash conditions common to both cases. *)
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  cancel.
  repeat eexists.
  solve_hash_list_rep.
  omega.
  unhide_rec.
  reflexivity.

  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  cancel.
  repeat eexists.
  solve_hash_list_rep.
  omega.
  unhide_rec.
  reflexivity.

  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  cancel.
  repeat eexists.
  solve_hash_list_rep.
  omega.
  unhide_rec.
  reflexivity.

  Grab Existential Variables.
  all: eauto; econstructor.
Qed.

Theorem recover_ok :  forall cs,
  {< F values values',
  PRE:hm
    exists d,
    BUFCACHE.rep cs d
    * [[ crash_xform (exists dvalues,
          crep values values' hm
          * [[ list_prefix values values' ]]
          * [[ length values + length dvalues = length values' ]]
          * array (DataStart ^+ $ (length values)) dvalues $1
          * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d'
      * [[ (exists dvalues,
          log_rep values hm'
          * [[ length values + length dvalues = length values' ]]
          * array (DataStart ^+ $ (length values)) (synced dvalues) $1
          * crash_xform F \/
          log_rep values' hm'
          * crash_xform F)%pred d' ]]
  CRASH:hm'
    exists cs' d',
      BUFCACHE.rep cs' d'
      * [[ (exists unsynced_data,
            log_rep values hm'
            * [[ length values + length unsynced_data = length values' ]]
            * array (DataStart ^+ $(length values)) (synced unsynced_data) $1
            * crash_xform F \/
            log_rep_crash_xform values values' unsynced_data hm'
            * crash_xform F \/
            crep values values' hm'
            * array (DataStart ^+ $ (length values)) (synced unsynced_data) $1
            * crash_xform F)%pred d' ]]
  >} recover cs.
Proof.
  intros.
  eapply pimpl_ok2; try eapply nop_ok.
  intros. norm'l. unfold stars; cbn.

  eapply crep_crash_xform in H4.
  deex.
  inversion H as [ H' | H' ]; destruct_lift H'.
  cancel.
  eapply pimpl_ok2; try eapply recover_ok_log_rep.
  cancel.
  eauto.
  match goal with
  | [ H: context[log_rep ?l hm0] |- _ ]
    => instantiate (2:=l)
  end.
  pred_apply; cancel.
  step_idtac.
  cancel.
  cancel.
  cancel.
  cancel.

  cancel.
  eapply pimpl_ok2; try eapply recover_ok_log_rep_crash_xform.
  cancel.
  eauto.
  eexists; eauto.
  cancel.
Qed.

Theorem recover_ok_rollback :  forall cs,
  {< F values values',
  PRE:hm
    exists d,
    BUFCACHE.rep cs d
    * [[ crash_xform (
          crep values values' hm
          * [[ list_prefix values' values ]]
          * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d'
      * [[ (exists dvalues,
          log_rep values hm'
          * crash_xform F \/
          log_rep values' hm'
          * [[ length values' + length dvalues = length values ]]
          * array (DataStart ^+ $ (length values')) (synced dvalues) $1
          * crash_xform F)%pred d' ]]
  CRASH:hm'
    exists cs' d',
      BUFCACHE.rep cs' d'
      * [[ (exists dvalues,
          log_rep values hm'
          * crash_xform F \/
          log_rep values' hm'
          * [[ length values' + length dvalues = length values ]]
          * array (DataStart ^+ $ (length values')) (synced dvalues) $1
          * crash_xform F)%pred d' ]]
  >} recover cs.
Proof.
  intros.
  eapply pimpl_ok2; try eapply nop_ok.
  intros. norm'l. unfold stars; cbn.

  eapply crep_crash_xform_rollback in H4.
  deex.
  inversion H as [ H' | H' ]; destruct_lift H';
  cancel;
  try eapply pimpl_ok2; try eapply recover_ok_log_rep; cancel.

  eauto.
  eauto.
  step.
  cancel.
  eauto.
  eauto.
  pred_apply.
  match goal with
  | [ H: context[log_rep ?l hm0] |- _ ]
    => instantiate (2:=l)
  end.
  cancel.
  step_idtac.
  all: cancel.
  cancel.

  Grab Existential Variables.
  all: eauto.
Qed.


Theorem append_ok : forall v cs,
  {< d vl F v_old,
  PRE:hm
    [[ length vl < # (maxlen) ]] *
    BUFCACHE.rep cs d *
    [[ (log_rep vl hm *
        (DataStart ^+ $ (length vl)) |-> (v_old, nil) * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      [[ (log_rep (vl ++ v :: nil) hm' * F)%pred d' ]]
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' *
      [[ ((log_rep vl hm' * (DataStart ^+ $ (length vl)) |->?
          \/ log_rep (vl ++ v :: nil) hm'
          \/ crep vl (vl ++ v :: nil) hm' * (DataStart ^+ $ (length vl)) |->?) * F)%pred d' ]]
  >} append v cs.
Proof.
  unfold append, log_rep, log_rep_inner.
  step_idtac.
  cancel_with eauto.
  pred_apply; cancel.

  step.
  rewrite of_to_header.
  cbn.
  step.
  unhide_rec.
  cancel.

  step.
  pred_apply; cancel.
  unhide_rec.
  cbn in *.
  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.
  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.

  step_idtac.
  {
    (* POST proof for disk contents. *)
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
  }

  {
    (* POST proof for log_rep_inner. *)
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
    match goal with
    | [ H: context[hashmap_get ?hm], H': hash_fwd _ = _ |- _]
      => rewrite H' in H; inversion H;
        match goal with
        | [ H: context[hashmap_get] |- _ ]
          => contradict_hashmap_get_default H hm
        end
    end.
    instantiate (1:=hm0).
    solve_hashmap_subset.

    omega.
    rewrite <- natToWord_plus.
    reflexivity.
  }

  cancel_with eauto.

  {
    pred_apply; cancel.
    apply pimpl_or_r; right.
    apply pimpl_or_r; right.
    unfold crep, log_rep_inner.
    unhide_rec.
    cancel.
    unfold synced; cancel.
    apply pimpl_or_r; left.
    cancel_with eauto.

    repeat eexists.
    rewrite rev_unit.
    solve_hash_list_rep.
    solve_hash_list_rep.
    eauto.

    eapply hashmap_get_subset.
    rewrite upd_hashmap'_eq. eauto.
    intuition.
    unfold hash2, hash_safe in *.
    match goal with
    | [ H: context[hashmap_get ?hm], H': hash_fwd _ = _ |- _]
      => rewrite H' in H; inversion H;
        match goal with
        | [ H: context[hashmap_get] |- _ ]
          => contradict_hashmap_get_default H hm
        end
    end.
    instantiate (1:=hm0).
    solve_hashmap_subset.

    rewrite app_length; simpl.
    omega.
    rewrite app_length; simpl.
    rewrite natToWord_plus.
    reflexivity.

    repeat eexists; try omega.
    solve_hash_list_rep.
  }

  cancel_with eauto.

  {
    pred_apply; cancel.
    apply pimpl_or_r; right.
    apply pimpl_or_r; left.
    unfold log_rep_crash_xform, log_rep_inner.
    cancel.
    rewrite array_isolate with (vs:=(combine (l ++ [v]) (repeat [] (length l + 1))))
      (i:=$ (length l)).
    rewrite wmult_comm, wmult_unit.
    unfold sel.
    solve_bound.
    rewrite skipn_oob.
    rewrite firstn_combine_comm, firstn_app, firstn_repeat, selN_combine,
        selN_last, repeat_selN; try omega.
    cancel.
    rewrite app_length, repeat_length; auto.
    rewrite combine_length, repeat_length, app_length, min_l; simpl; try omega.
    solve_bound.
    rewrite combine_length, repeat_length, app_length, min_l; simpl; try omega.

    repeat eexists; eauto.
    rewrite rev_unit.
    solve_hash_list_rep.
    solve_hash_list_rep.
    eauto.

    eapply hashmap_get_subset.
    rewrite upd_hashmap'_eq. eauto.
    intuition.
    unfold hash2, hash_safe in *.
    match goal with
    | [ H: context[hashmap_get ?hm], H': hash_fwd _ = _ |- _]
      => rewrite H' in H; inversion H;
        match goal with
        | [ H: context[hashmap_get] |- _ ]
          => contradict_hashmap_get_default H hm
        end
    end.
    instantiate (1:=hm0).
    solve_hashmap_subset.

    omega.
    rewrite <- natToWord_plus.
    reflexivity.
  }

  cancel_with eauto.
  {
    pred_apply; cancel.
    apply pimpl_or_r; right.
    apply pimpl_or_r; right.
    unfold crep, log_rep_inner, synced.
    cancel.
    apply pimpl_or_r; left.
    cancel.

    repeat eexists; eauto.
    rewrite rev_unit.
    solve_hash_list_rep.
    solve_hash_list_rep.
    eauto.

    eapply hashmap_get_subset.
    rewrite upd_hashmap'_eq. eauto.
    intuition.
    unfold hash2, hash_safe in *.
    match goal with
    | [ H: context[hashmap_get ?hm], H': hash_fwd _ = _ |- _]
      => rewrite H' in H; inversion H;
        match goal with
        | [ H: context[hashmap_get] |- _ ]
          => contradict_hashmap_get_default H hm
        end
    end.
    instantiate (1:=hm0).
    solve_hashmap_subset.

    rewrite app_length; simpl; omega.
    rewrite app_length; simpl.
    rewrite natToWord_plus.
    reflexivity.

    repeat eexists; eauto.
    solve_hash_list_rep.
  }

  cancel.

  {
    pred_apply; cancel.
    apply pimpl_or_r; right.
    apply pimpl_or_r; right.
    unfold crep, log_rep_inner, synced.
    cancel.
    apply pimpl_or_r; left.
    cancel.

    repeat eexists; eauto.
    rewrite rev_unit.
    solve_hash_list_rep.
    solve_hash_list_rep.
    eauto.

    eapply hashmap_get_subset.
    rewrite upd_hashmap'_eq. eauto.
    intuition.
    unfold hash2, hash_safe in *.
    match goal with
    | [ H: context[hashmap_get ?hm], H': hash_fwd _ = _ |- _]
      => rewrite H' in H; inversion H;
        match goal with
        | [ H: context[hashmap_get] |- _ ]
          => contradict_hashmap_get_default H hm
        end
    end.
    instantiate (1:=hm0).
    solve_hashmap_subset.

    rewrite app_length; simpl; omega.
    rewrite app_length; simpl.
    rewrite natToWord_plus.
    reflexivity.

    repeat eexists; eauto.
    solve_hash_list_rep.
  }
  apply pimpl_or_r; left.
  unhide_rec.
  cancel.
  repeat eexists; eauto.
  solve_hash_list_rep.

  {
    cancel.
    apply pimpl_or_r; right.
    apply pimpl_or_r; right.
    unfold crep, log_rep_inner, synced.
    unhide_rec.
    cancel.
    apply pimpl_or_r; left.
    cancel.

    repeat eexists; eauto.
    rewrite rev_unit.
    solve_hash_list_rep.
    solve_hash_list_rep.
    eauto.

    eapply hashmap_get_subset.
    rewrite upd_hashmap'_eq. eauto.
    intuition.
    unfold hash2, hash_safe in *.
    match goal with
    | [ H: context[hashmap_get ?hm], H': hash_fwd _ = _ |- _]
      => rewrite H' in H; inversion H;
        match goal with
        | [ H: context[hashmap_get] |- _ ]
          => contradict_hashmap_get_default H hm
        end
    end.
    instantiate (1:=hm0).
    solve_hashmap_subset.

    rewrite app_length; simpl; omega.
    rewrite app_length; simpl.
    rewrite natToWord_plus.
    reflexivity.

    repeat eexists; eauto.
    solve_hash_list_rep.
  }

  apply pimpl_or_r; left.
  cancel.
  repeat eexists; eauto.
  solve_hash_list_rep.

  cancel.
  apply pimpl_or_r; left.
  unhide_rec.
  cancel.
  repeat eexists; eauto.
  solve_hash_list_rep.

  apply pimpl_or_r; left.
  cancel.
  repeat eexists; eauto.
  solve_hash_list_rep.

  cancel.
  pred_apply; cancel.
  apply pimpl_or_r; left.
  cancel.
  repeat eexists; eauto.
  solve_hash_list_rep.

  Grab Existential Variables.
  all: auto.
Qed.

Theorem truncate_ok : forall cs,
  {< d vl F,
  PRE:hm
    BUFCACHE.rep cs d *
    [[ (log_rep vl hm * F)%pred d ]]
  POST:hm' RET:cs'
    exists d',
    BUFCACHE.rep cs' d'
    * [[ (exists vl,
        log_rep nil hm' * array DataStart (synced vl) $1 * F)%pred d' ]]
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d'
    * [[ (exists vl,
        log_rep vl hm' * F \/
        log_rep nil hm' * array DataStart (synced vl) $1 * F \/
        crep vl nil hm' * F)%pred d' ]]
  >} truncate cs.
Proof.
  unfold truncate, log_rep, log_rep_inner.
  cbn.
  step_idtac.
  eauto.
  pred_apply; cancel.
  step.
  rewrite of_to_header.
  cbn.
  step_idtac.
  cancel_with eauto.
  pred_apply; cancel.
  step_idtac.
  eauto.
  pred_apply; cancel.
  step.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.
  cancel_with eauto.

  repeat eexists.
  right; right.
  unfold crep, log_rep_inner.
  pred_apply; cancel_with eauto.
  unfold synced.
  match goal with
  | [|- context[array DataStart (combine ?l _)] ] => instantiate (1:=l)
  end.
  cancel_with eauto.
  apply pimpl_or_r; left.
  cancel.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.

  unhide_rec.
  reflexivity.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.

  cancel_with eauto.
  repeat eexists.
  right; left.
  pred_apply; cancel_with eauto.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.

  cancel_with eauto.
  repeat eexists.
  left.
  pred_apply; cancel.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.

  cancel_with eauto.
  repeat eexists.
  right; right.
  unfold crep, log_rep_inner.
  pred_apply; cancel_with eauto.
  unfold synced.
  match goal with
  | [|- context[array DataStart (combine ?l _)] ] => instantiate (1:=l)
  end.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  cancel_with eauto.
  apply pimpl_or_r; left.
  cancel.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.

  eapply pimpl_or_r; left.
  cancel_with eauto.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.

  cancel.
  repeat eexists.
  left.
  pred_apply; cancel.
  repeat eexists; try omega.
  solve_hash_list_rep; eauto.
  unhide_rec.
  reflexivity.
Qed.