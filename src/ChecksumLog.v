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

Set Implicit Arguments.

Definition PreviousLength : addr := $0.
Definition CurrentLength : addr := $1.
Definition Checksum : addr := $2.
Definition DataStart : addr := $3.
Parameter maxlen : addr.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

Definition log_rep_prefix h len vl vdisk hm :=
  hash_list_rep (rev vl) h hm /\
  list_prefix vl vdisk /\
  length vl = len.

(* EVentually len' can live in memory *)
Definition log_rep vl vl' vdisk hm :
  @pred addr (@weq addrlen) valuset :=
  (exists h h' len len',
    [[ log_rep_prefix h len vl vl' hm ]] *
    [[ log_rep_prefix h' len' vl' vdisk hm ]] *
    [[ length vdisk = # (maxlen) ]] *
    PreviousLength |-> (addr2valu $ (len), nil) *
    CurrentLength |-> (addr2valu $ (len'), nil) *
    Checksum |-> (hash_to_valu h', nil) *
    array DataStart (combine vdisk (repeat nil # (maxlen))) $1)%pred.

Definition crep vl vl' vl'' vdisk hm :
  @pred addr (@weq addrlen) valuset :=
  (exists h h' h'' len len' len'' unsynced_data,
    [[ log_rep_prefix h len vl vl' hm ]] *
    [[ log_rep_prefix h' len' vl' vl'' hm ]] *
    [[ log_rep_prefix h'' len'' vl'' vdisk hm ]] *
    (PreviousLength |-> (addr2valu $ (len), nil) \/
      PreviousLength |-> (addr2valu $ (len'), addr2valu $ (len) :: nil)) *
    (CurrentLength |-> (addr2valu $ (len'), nil) \/
      CurrentLength |-> (addr2valu $ (len''), addr2valu $ (len') :: nil)) *
    (Checksum |-> (hash_to_valu h', nil) \/
      Checksum |-> (hash_to_valu h'', hash_to_valu h' :: nil)) *
    (array DataStart (combine vdisk
        (upd (repeat nil # (maxlen)) $ ( len') (unsynced_data :: nil))) $1)
  )%pred.

(** What the rep *should* be after crash.
- PreviousHash points to a synced hash value that matches a
  prefix of the disk.
- NextHash points to a synced hash value. If this hash matches
  a prefix of the disk, then PreviousHash's matched disk prefix
  is also a prefix of NextHash's disk prefix.
- DataStart points to a synced array.

Definition log_rep_part vl hm vdisk :
  @pred addr (@weq addrlen) valuset :=
  (exists h h',
    [[ log_rep_prefix h vl vdisk # (maxlen) hm ]] *
    [[ (exists vl', log_rep_prefix h' vl' vdisk # (maxlen) hm
        -> list_prefix vl vl') ]] *
    PreviousHash |-> (hash_to_valu h, nil) *
    NextHash |-> (hash_to_valu h', nil) *
    array DataStart (combine vdisk (repeat nil # (maxlen))) $1
  )%pred.**)

Definition log_rep' vl vl' hm cs d : pred :=
  BUFCACHE.rep cs d *
  [[ (exists vdisk, log_rep vl vl' vdisk hm)%pred d ]].

Definition possible_crash_list (l: list valuset) (l': list valu) :=
  length l = length l' /\ forall i, i < length l -> In (selN l' i $0) (valuset_list (selN l i ($0, nil))).

Lemma crash_xform_array: forall l start stride,
  crash_xform (array start l stride) =p=>
    exists l', [[ possible_crash_list l l' ]] * array start (List.combine l' (repeat nil (length l'))) stride.
Proof.
Admitted.

Lemma crash_invariant_synced_array: forall l start stride,
  crash_xform (array start (List.combine l (repeat nil (length l))) stride) =p=>
  array start (List.combine l (repeat nil (length l))) stride.
Proof.
Admitted.

Lemma crash_xform_helper : forall vdisk log_pointer unsynced_data,
  crash_xform (array DataStart (combine vdisk
        (upd (repeat nil (length vdisk)) log_pointer (unsynced_data :: nil))) $1) =p=>
    array DataStart (combine vdisk (repeat nil (length vdisk))) $1 \/
    array DataStart (combine (upd vdisk log_pointer unsynced_data) (repeat nil (length vdisk))) $1.
Proof.
Admitted.

Definition read T i (log_pointer : addr) cs rx : prog T :=
  let^ (cs, v) <- BUFCACHE.read_array DataStart i $1 cs;
  rx ^(cs, log_pointer, v).

Definition append T v cs rx : prog T :=
  let^ (cs, log_pointer) <- BUFCACHE.read CurrentLength cs;
  let^ (cs, h) <- BUFCACHE.read Checksum cs;
  h <- Hash (Word.combine v (valu_to_hash h));
  cs <- BUFCACHE.write_array DataStart (valu2addr log_pointer) $1 v cs;
  cs <- BUFCACHE.write PreviousLength log_pointer cs;
  cs <- BUFCACHE.write CurrentLength (addr2valu (valu2addr log_pointer ^+ $1)) cs;
  cs <- BUFCACHE.write Checksum (hash_to_valu h) cs;
  cs <- BUFCACHE.sync_array DataStart (valu2addr log_pointer) $1 cs;
  cs <- BUFCACHE.sync PreviousLength cs;
  cs <- BUFCACHE.sync CurrentLength cs;
  cs <- BUFCACHE.sync Checksum cs;
  rx cs.

Definition truncate T cs rx : prog T :=
  h <- Hash default_valu;
  cs <- BUFCACHE.write PreviousLength $0 cs;
  cs <- BUFCACHE.write CurrentLength $0 cs;
  cs <- BUFCACHE.write Checksum (hash_to_valu h) cs;
  cs <- BUFCACHE.sync PreviousLength cs;
  cs <- BUFCACHE.sync CurrentLength cs;
  cs <- BUFCACHE.sync Checksum cs;
  rx cs.

Theorem append_ok : forall v cs,
  {< d vl vl',
  PRE:hm
    [[ length vl' < # (maxlen) ]] *
    log_rep' vl vl' hm cs d
  POST:hm' RET:cs'
    exists d',
      log_rep' vl' (vl' ++ v :: nil) hm' cs' d'
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' (** TODO **)
  >} append v cs.
Proof.
  unfold append, log_rep', log_rep, log_rep_prefix.
  step.
  pred_apply; cancel.

  step.
  pred_apply; cancel.
  step.
  step.
  rewrite addr2valu2addr.
  rewrite wordToNat_natToWord_bound with (bound := maxlen);
    try omega.
  rewrite combine_length.
  rewrite repeat_length.
  rewrite min_l; omega.
  step.
  pred_apply; cancel.
  step.
  pred_apply; cancel.
  step.
  pred_apply; cancel.

  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.
  rewrite addr2valu2addr.
  instantiate (a1:=(upd_prepend (combine l (repeat nil # (maxlen))) $ (length l1) v)); cancel.
  rewrite addr2valu2addr.
  rewrite wordToNat_natToWord_bound with (bound := maxlen);
    try omega.
  unfold upd_prepend.
  rewrite length_upd, combine_length, repeat_length.
  rewrite min_l; omega.

  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.
  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.

  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.

  step_idtac.

  Lemma upd_sync_prepend : forall l i v default,
    upd_sync (upd_prepend l i v) i default = upd l i (v, nil).
  Proof.
    unfold upd_sync, upd_prepend.
    induction l; intros; simpl.
    auto.
    unfold upd, sel in *.
    destruct # (i) eqn:Hi; simpl.
    auto.
    replace n with # (@natToWord addrlen n).
    erewrite <- IHl. eauto.
    apply wordToNat_natToWord_bound with (bound:=i).
    omega.
  Qed.

  Lemma repeat_upd : forall T n i (v : T),
    upd (repeat v n) i v = repeat v n.
  Proof.
    induction n; intros; simpl.
    auto.
    unfold upd, sel in *.
    destruct # (i) eqn:Hi; simpl.
    auto.
    replace n0 with # (@natToWord addrlen n0).
    rewrite <- IHn at 2. eauto.
    apply wordToNat_natToWord_bound with (bound:=i).
    omega.
  Qed.

  rewrite addr2valu2addr.
  rewrite upd_sync_prepend.
  rewrite <- combine_upd.
  rewrite repeat_upd.
  eauto.

  solve_hash_list_rep.
  unfold list_prefix.
  apply firstn_app; auto.
  rewrite wordToNat_natToWord_bound with (bound := maxlen);
    try omega.

  rewrite rev_unit.
  econstructor.
  solve_hash_list_rep.
  rewrite hash2valu2hash; auto.
  rewrite hash2valu2hash in *.
  eapply hashmap_get_subset.
  rewrite upd_hashmap'_eq. eauto.
  intuition.
  rewrite H24 in H19.
  unfold hash_safe in H19; intuition.
  contradict_hashmap_get_default H26 hm1.
  contradict_hashmap_get_default H26 hm1.
  instantiate (Goal:=hm1).
  solve_hashmap_subset.

  unfold list_prefix in H12.
  unfold list_prefix.
  unfold upd.
  replace (length (l1 ++ _)) with (length l1 + 1).
  rewrite wordToNat_natToWord_bound with (bound := maxlen);
    try omega.
  rewrite <- firstn_app_updN_eq.
  congruence.
  omega.
  rewrite app_length; auto.
  erewrite wordToNat_plusone.
  rewrite wordToNat_natToWord_bound with (bound := maxlen);
    try omega.
  apply lt_wlt.
  rewrite wordToNat_natToWord_bound with (bound := maxlen);
    try omega.
  eauto.
  rewrite length_upd; auto.

  (* creps... *)
  all: cancel_with eauto.
Qed.

Theorem truncate_ok : forall cs,
  {< d vl vl',
  PRE:hm
    log_rep' vl vl' hm cs d
  POST:hm' RET:cs'
    exists d',
      log_rep' nil nil hm' cs' d'
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' (** TODO **)
  >} truncate cs.
Proof.
  unfold truncate, log_rep', log_rep, log_rep_prefix.
  step.
  step.
  step.
  pred_apply; cancel.
  step.
  pred_apply; cancel.
  step_idtac.
  eauto.
  pred_apply; cancel.
  step_idtac.
  eauto.
  pred_apply; cancel.
  step_idtac.
  eauto.
  pred_apply; cancel.
  step.