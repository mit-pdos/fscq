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

Set Implicit Arguments.

Definition PreviousHash : addr := $0.
Definition NextHash : addr := $1.
Definition DataStart : addr := $2.
Parameter maxlen : addr.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

Definition log_rep_prefix h vl vdisk len hm :=
  list_prefix vl vdisk /\
  hash_list_rep (rev vl) h hm /\
  length vdisk = len.

Definition log_rep vl vl' (log_pointer : addr) hm vdisk :
  @pred addr (@weq addrlen) valuset :=
  (exists h h',
    [[ log_rep_prefix h vl vl' # (log_pointer) hm ]] *
    [[ log_rep_prefix h' vl' vdisk # (maxlen) hm ]] *
    PreviousHash |-> (hash_to_valu h, nil) *
    NextHash |-> (hash_to_valu h', nil) *
    array DataStart (combine vdisk (repeat nil # (maxlen))) $1
  )%pred.

(* What the rep *should* be after crash. *)
Definition log_rep_part vl hm vdisk :
  @pred addr (@weq addrlen) valuset :=
  (exists h h',
    [[ log_rep_prefix h vl vdisk # (maxlen) hm ]] *
    PreviousHash |-> (hash_to_valu h, nil) *
    NextHash |-> (hash_to_valu h', nil) *
    array DataStart (combine vdisk (repeat nil # (maxlen))) $1
  )%pred.

Definition log_rep' vl vl' log_pointer hm cs d : pred :=
  BUFCACHE.rep cs d *
  [[ (exists vdisk, log_rep vl vl' log_pointer hm vdisk)%pred d ]].

(**
* - PreviousHash must be equal to either the previous hash, the next
    hash, or the newest hash (hash of the value appended)
  - PreviousHash must point to a hash that matches some prefix of
    the current disk.
* - NextHash can point to anything, as long as it's a hash value.
* - Disk can have original log data, with possibility of log_pointer
    position unsynced (only happens when when log_pointer hasn't been
    incremented yet)
**)
Definition crep vl vl' (log_pointer : addr) hm vdisk :
  @pred addr (@weq addrlen) valuset :=
  (exists h h' unsynced_data,
    [[ log_rep_prefix h vl vl' # (log_pointer) hm ]] *
    [[ log_rep_prefix h' vl' vdisk # (maxlen) hm ]] *
    (PreviousHash |-> (hash_to_valu h, nil) \/
      PreviousHash |-> (hash_to_valu h', hash_to_valu h :: nil) \/
      PreviousHash |-> (hash_to_valu h', nil)) *
    (exists h' h'', NextHash |-> (hash_to_valu h'', nil) \/
      NextHash |-> (hash_to_valu h'', hash_to_valu h' :: nil)) *
    (array DataStart (combine vdisk
        (upd (repeat nil # (maxlen)) log_pointer unsynced_data)) $1)
  )%pred.

Definition read T i (log_pointer : addr) cs rx : prog T :=
  let^ (cs, v) <- BUFCACHE.read_array DataStart i $1 cs;
  rx ^(cs, log_pointer, v).

Definition append T v log_pointer cs rx : prog T :=
  let^ (cs, h') <- BUFCACHE.read NextHash cs;
  h'' <- Hash (Word.combine v (valu_to_hash h'));
  cs <- BUFCACHE.write_array DataStart log_pointer $1 v cs;
  cs <- BUFCACHE.write PreviousHash h' cs;
  cs <- BUFCACHE.write NextHash (hash_to_valu h'') cs;
  cs <- BUFCACHE.sync_array DataStart log_pointer $1 cs;
  cs <- BUFCACHE.sync PreviousHash cs;
  cs <- BUFCACHE.sync NextHash cs;
  rx ^(cs, log_pointer ^+ $1).

Definition truncate T cs rx : prog T :=
  h <- Hash default_valu;
  cs <- BUFCACHE.write PreviousHash (hash_to_valu h) cs;
  cs <- BUFCACHE.write NextHash (hash_to_valu h) cs;
  cs <- BUFCACHE.sync PreviousHash cs;
  cs <- BUFCACHE.sync NextHash cs;
  rx (cs, natToWord addrlen 0).

Theorem append_ok : forall log_pointer v cs,
  {< d vl vl',
  PRE:hm
    [[ # (log_pointer) < # (maxlen) ]] *
    log_rep' vl vl' log_pointer hm cs d
  POST:hm' RET:^(cs', log_pointer')
    exists d',
      log_rep' vl' (vl' ++ v :: nil) log_pointer' hm' cs' d'
  CRASH:hm'
    exists cs' d' vdisk, BUFCACHE.rep cs' d' *
      (crep vl vl' log_pointer hm' vdisk \/
        crep vl' (vl' ++ v :: nil) (log_pointer ^+ $1) hm' vdisk)
  >} append v log_pointer cs.
Proof.
  unfold append, log_rep', log_rep, log_rep_prefix.
  step.
  pred_apply; cancel.

  step.
  step.
  admit. (* Solvable with list_prefix length lemma *)
  step.
  pred_apply; cancel.
  step.
  pred_apply; cancel.
  step_idtac.
  eauto.
  pred_apply; cancel_with eauto.
  instantiate (a25:=(upd_prepend (combine l (repeat nil # (maxlen))) log_pointer v)); cancel.
  admit.

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

  rewrite upd_sync_prepend.
  rewrite <- combine_upd.
  rewrite repeat_upd.
  eauto.

  unfold list_prefix.
  apply firstn_app; auto.
  solve_hash_list_rep.
  admit.
  admit. (* list_prefix holds for updated disk *)

  rewrite rev_unit.
  econstructor.
  solve_hash_list_rep.
  rewrite hash2valu2hash; auto.
  rewrite hash2valu2hash in *.
  eapply hashmap_get_subset.
  rewrite upd_hashmap'_eq. eauto.
  intuition.
  rewrite H20 in H19.
  unfold hash_safe in H19; intuition.
  contradict_hashmap_get_default H22 hm0.
  contradict_hashmap_get_default H22 hm0.
  instantiate (Goal:=hm0).
  solve_hashmap_subset.

  rewrite length_upd; auto.

  (* creps... *)
Admitted.