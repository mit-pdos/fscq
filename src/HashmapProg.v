Require Import Prog.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import Word.
Require Import FSLayout.
Require Import BasicProg.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import Arith.
Require Import ListUtils.
Require Import Omega.

Set Implicit Arguments.


Definition hash_list T values rx : prog T :=
  hash <- Hash (combine_entry default_entry);
  let^ (hash) <- ForN i < length values
  Hashmap hm'
  Ghost [ crash ]
  Loopvar [ hash ]
  Continuation lrx
  Invariant
    [[ hash_list_rep (rev (firstn i values)) hash hm' ]]
  OnCrash crash
  Begin
    hash <- Hash (Word.combine (combine_entry (selN values i default_entry)) hash);
    lrx ^(hash)
  Rof ^(hash);
  rx hash.


Theorem hash_list_ok : forall values,
  {< (_ : unit) ,
  PRE:hm
    emp * [[ goodSize addrlen (length values) ]]
        * [[ Forall (fun e => goodSize addrlen (fst e)) values ]]
  POST:hm' RET:hash
    emp * [[ hash_list_rep (rev values) hash hm' ]]
  CRASH:hm'
    emp * [[ exists i hash, hash_list_rep (rev (firstn i values)) hash hm' ]]
  >} hash_list values.
Proof.
  unfold hash_list.
  step.
  step; try apply HL_nil; auto.

  assert (Hlength: length (rev (firstn (m + 1) values)) = S m).
    rewrite rev_length.
    rewrite firstn_length.
    rewrite min_l; omega.

  step.
  step.

  (* Loop invariant. *)
  - destruct (rev (firstn (m + 1) values)) eqn:Hrev_values.
    + simpl in Hlength. inversion Hlength.
    + destruct values.
      inversion H0.

      assert (Hvalues: rev (p0 :: firstn m values) = selN (p0 :: values) m default_entry :: rev (firstn m (p0 :: values))).
        rewrite <- rev_unit.
        rewrite <- firstn_plusone_selN; try omega.
        destruct (m + 1) eqn:Hm; try omega.
        simpl.
        replace m with n; try omega.
        auto.

      rewrite Hvalues.
      solve_hash_list_rep.
      solve_hash_list_rep.
      eapply Forall_forall in H4; eauto.
      apply in_selN; auto.
      auto.
      apply upd_hashmap'_eq.
      intuition.
      unfold hash_safe in *.
      rewrite H8 in H17.
      inversion H17 as [ Hdef | Hdef ];
      contradict_hashmap_get_default Hdef hm0.

  (* Loop invariant implies post-condition. *)
  - step.
    rewrite firstn_oob in H9; try omega.
    auto.

  - exists 0; eexists. econstructor. eauto.
  - exists 0; eexists. econstructor. eauto.

  Grab Existential Variables.
  all: econstructor.
Qed.

Hint Extern 1 ({{_}} progseq (hash_list _) _) => apply hash_list_ok : prog.
