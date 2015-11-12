Require Import Prog.
Require Import Word.
Require Import FSLayout.
Require Import Log.
Require Import BasicProg.
Require Import Compare.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import GenSep.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import EqdepFacts.
Require Import Arith.

Set Implicit Arguments.

Definition block1 : addr := $0.
Definition block2 : addr := $1.
Definition default_valu : valu := $0.
Definition hash_block : addr := $2.


Definition hash2 sz1 sz2 (a : word sz1) (b : word sz2) :=
  hash_fwd (Word.combine a b).

Definition hash2_valu (a b : valu) :=
  hash2 a (hash2 b default_valu).

Definition hash2_rep sz1 sz2 (a : word sz1) (b : word sz2) v :=
  v = hash2 a b /\
  hash_inv v = existT _ _ (Word.combine a b).

Inductive hash_list_rep : (list valu) -> word hashlen -> Prop :=
  | HL_nil : forall hl,
      hl = hash_fwd default_valu ->
      hash_inv hl = existT _ _ default_valu ->
        hash_list_rep nil hl
  | HL_cons : forall values hvalues hvalues' x,
      hash_list_rep values hvalues ->
      hash2_rep x hvalues hvalues' ->
      hash_list_rep (x :: values) hvalues'.


(* Program that hashes a list of values into a single hash value. *)
Definition hash_list T values rx : prog T :=
    default_hash <- Hash default_valu;
    let^ (hash) <- For i < $ (length values)
    Ghost [ crash ]
    Loopvar [ hash ]
    Continuation lrx
    Invariant
      [[ hash_list_rep (rev (firstn #i values)) hash ]]
    OnCrash crash
    Begin
      hash <- Hash (Word.combine (sel values i default_valu) hash);
      lrx ^(hash)
    Rof ^(default_hash);
    rx hash.


Theorem hash_list_ok : forall values,
  {< (_ : unit) ,
  PRE
    emp * [[ goodSize addrlen (length values) ]]
  POST RET:hash
    emp * [[ hash_list_rep (rev values) hash ]]
  CRASH
    emp
  >} hash_list values.
Proof.
  unfold hash_list.
  step.
  step.
  constructor; auto.
  step.
  step.

  assert (Hlength: length (rev (firstn # (m ^+ $ (1)) values)) = S (# (m))).
    rewrite rev_length.
    rewrite firstn_length.
    erewrite wordToNat_plusone; eauto.
    destruct (le_dec (S (# m)) (length values)).
      apply Min.min_l. auto.

      apply not_lt in n.
      apply wlt_lt in H.
      rewrite wordToNat_natToWord_idempotent' in H; auto.
      intuition.

  (* Loop invariant. *)
  - destruct (rev (firstn # (m ^+ $ (1)) values)) eqn:Hrev_values.
    + simpl in Hlength. inversion Hlength.
    + eapply HL_cons.
      assert (Hl: rev l = (firstn # (m) values)).
        replace l with (rev (rev l)) in Hrev_values;
          try apply rev_involutive.
        rewrite <- rev_unit in Hrev_values.
        erewrite wordToNat_plusone in Hrev_values; eauto.
        apply rev_injective in Hrev_values.

        rewrite <- removelast_firstn;
          try (apply lt_word_lt_nat; auto).
        replace (rev l) with (rev l ++ removelast (w :: nil)).
        rewrite <- removelast_app.
        rewrite Hrev_values.
        auto.

        intuition. inversion H3.
        simpl. rewrite app_nil_r. auto.

      rewrite <- rev_involutive in Hl.
      apply rev_injective in Hl.
      rewrite Hl. eauto.
      unfold hash2_rep, hash2.
      assert (Hw: selN (firstn # (m ^+ $ (1)) values) (# m) default_valu = w).
        rewrite <- rev_involutive in Hrev_values.
        apply rev_injective in Hrev_values.
        rewrite Hrev_values.
        simpl. apply selN_last. rewrite rev_length.
        simpl in Hlength. apply eq_add_S in Hlength.
        auto.
      rewrite selN_firstn in Hw;
        try (erewrite wordToNat_plusone; eauto).
      subst.
      intuition.

  (* Loop invariant implies post-condition. *)
  - step.
    assert (Hfirstn: firstn # (natToWord addrlen (length values)) values = values).
      rewrite wordToNat_natToWord_idempotent'; auto.
      apply firstn_oob. auto.
    rewrite <- Hfirstn. auto.

  Grab Existential Variables.
  all: eauto.
Qed.

Hint Extern 1 ({{_}} progseq (hash_list _ _ _) _) => apply hash_list_ok : prog.


(* Representations for an example with two log blocks. *)
(* block1 and block2 are synced, hash_block has some valid hash *)
Definition any_hash_rep (a b a' b' : valu) (d : @mem addr (@weq addrlen) valuset) :
    @pred addr (@weq addrlen) valuset :=
  (exists hv,
    [[ (block1 |-> (a, nil) *
     block2 |-> (b, nil) *
     hash_block |-> (hash_to_valu hv, nil))%pred d ]] *
    [[ hash2_rep a' b' hv ]])%pred.

(* hash_block has the valid hash of block1 and block2 values *)
Definition rep a b (d : @mem addr (@weq addrlen) valuset) :
    @pred addr (@weq addrlen) valuset :=
  any_hash_rep a b a b d.

(* After a crash:
  - block1 and block2 can be anything
  - hash_block can be one of:
    - hash of old values
    - hash of new values but unsynced
    - hash of new values and synced *)
Definition crep (a b a' b' : valu) :
    @pred addr (@weq addrlen) valuset :=
  (exists hv hv',
    block1 |->? *
    block2 |->? *
    ( hash_block |-> (hash_to_valu hv, nil) *
        [[ hash2_rep a b hv ]] \/
      hash_block |-> (hash_to_valu hv', hash_to_valu hv :: nil) *
        [[ hash2_rep a b hv /\ hash2_rep a' b' hv' ]] \/
      hash_block |-> (hash_to_valu hv', nil) *
        [[ hash2_rep a' b' hv' ]]))%pred.


(* Example "log" implementation using checksums *)
Definition put T cs d1 d2 rx : prog T :=
  cs <- BUFCACHE.write block1 d1 cs;
  cs <- BUFCACHE.write block2 d2 cs;
  h <- Hash (Word.combine d1 d2);
  cs <- BUFCACHE.write hash_block (hash_to_valu h) cs;
  cs <- BUFCACHE.sync block1 cs;
  cs <- BUFCACHE.sync block2 cs;
  cs <- BUFCACHE.sync hash_block cs;
  rx cs.

Definition get T cs rx : prog T :=
  let^ (cs, d1) <- BUFCACHE.read block1 cs;
  let^ (cs, d2) <- BUFCACHE.read block2 cs;
  rx ^(d1, d2).

Definition recover T cs rx : prog T :=
  let^ (cs, d1) <- BUFCACHE.read block1 cs;
  let^ (cs, d2) <- BUFCACHE.read block2 cs;
  let^ (cs, diskh) <- BUFCACHE.read hash_block cs;
  h <- Hash (Word.combine d1 d2);
  If (weq diskh (hash_to_valu h)) {
    rx cs
  } else {
    cs <- put cs default_valu default_valu;
    rx cs
  }.


Theorem put_ok : forall cs d1 d2,
  {< d d1_old d2_old d1_old' d2_old',
  PRE
    BUFCACHE.rep cs d *
    any_hash_rep d1_old d2_old d1_old' d2_old' d
  POST RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      rep d1 d2 d'
  CRASH
    exists cs' d',
      BUFCACHE.rep cs' d' *
      [[ (crep d1_old' d2_old' d1 d2)%pred d' ]]
  >} put cs d1 d2.
Proof.
  unfold put, rep, any_hash_rep, crep, hash2_rep, hash2.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.

  all: cancel.
  Grab Existential Variables.
  all: eauto.
Qed.

Hint Extern 1 ({{_}} progseq (put _ _ _) _) => apply put_ok : prog.


Theorem get_ok : forall cs,
  {< d d1 d2,
  PRE
    BUFCACHE.rep cs d *
    rep d1 d2 d
  POST RET:^(d1', d2')
    exists cs', BUFCACHE.rep cs' d *
    rep d1 d2 d *
    [[ d1 = d1' /\ d2 = d2' ]]
  CRASH
    exists cs', BUFCACHE.rep cs' d *
    rep d1 d2 d
  >} get cs.
Proof.
  unfold get, rep, any_hash_rep.
  step.
  step.
  step.
Qed.

(* block1 and block2 get some value, and hash_block points to a valid hash of  *)
Definition after_crash_pred (v1 v2 : valu) :
    @pred addr (@weq addrlen) valuset :=
  (exists a b hv,
      block1 |-> (a, nil) *
      block2 |-> (b, nil) *
      hash_block |-> (hash_to_valu hv, nil) *
    [[ hash2_rep v1 v2 hv ]])%pred.

Lemma crash_xform_would_recover_either_pred : forall v1 v2 v1' v2',
  crash_xform (crep v1 v2 v1' v2') =p=>
    after_crash_pred v1 v2 \/
    after_crash_pred v1' v2'.
Proof.
  unfold crep, after_crash_pred.
  intros.
  repeat (autorewrite with crash_xform; cancel).
Qed.

Hint Rewrite crash_xform_would_recover_either_pred : crash_xform.


Theorem recover_ok : forall cs,
  {< d1_old d2_old d1 d2,
  PRE
    exists d,
      BUFCACHE.rep cs d *
      [[ crash_xform (crep d1_old d2_old d1 d2)%pred d ]]
  POST RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      (rep d1_old d2_old d' \/
       rep d1 d2 d' \/
       rep default_valu default_valu d')
  CRASH
    exists cs' d',
      (BUFCACHE.rep cs' d' *
       [[ (crep d1_old d2_old default_valu default_valu)%pred d' ]]) \/
      (BUFCACHE.rep cs' d' *
       [[ (crep d1 d2 default_valu default_valu)%pred d' ]])
  >} recover cs.
Proof.
  unfold recover, rep.
  intros.
  eapply pimpl_ok2; eauto with prog.
  intros. norm'l. unfold stars; simpl.

  (* autorewrite with crash_xform doesn't work? *)
  assert (Hafter_crash: (after_crash_pred d1_old d2_old)%pred d \/
    (after_crash_pred d1 d2)%pred d).
    apply crash_xform_would_recover_either_pred.
    auto.

  unfold after_crash_pred in Hafter_crash.
  destruct Hafter_crash;
  destruct_lift H.

  - cancel.
    step.
    step.
    step.
    step.
    step.
    unfold hash2_rep, hash2 in *.
    destruct H5.

    assert (Hheq: d1_old = a /\ d2_old = b).
      subst.
      apply hash_to_valu_inj in H8.
      rewrite H8 in H3.
      rewrite H11 in H3.
      pose proof (eq_sigT_snd H3).
      autorewrite with core in *.
      apply combine_inj in H0.
      intuition.
    unfold any_hash_rep, hash2_rep.
    cancel.

    step. unfold any_hash_rep, hash2_rep, hash2 in *. cancel.
    step.
    cancel.
    all: cancel; try (
      unfold crep, hash2_rep, hash2 in *;
      instantiate (1:=d);
      apply pimpl_or_r; left;
      repeat cancel).

  - cancel.
    step.
    step.
    step.
    step.
    step.
    unfold hash2_rep, hash2 in *.
    destruct H5.

    assert (Hheq: d1 = a /\ d2 = b).
      subst.
      apply hash_to_valu_inj in H8.
      rewrite H8 in H3.
      rewrite H11 in H3.
      pose proof (eq_sigT_snd H3).
      autorewrite with core in *.
      apply combine_inj in H0.
      intuition.
    unfold any_hash_rep, hash2_rep.
    cancel.

    step. unfold any_hash_rep, hash2_rep, hash2 in *. cancel.
    step.
    cancel.
    all: cancel; try (
      unfold crep, hash2_rep, hash2 in *;
      instantiate (1:=d);
      apply pimpl_or_r; right;
      repeat cancel).

  Grab Existential Variables.
  all: eauto.
Qed.
