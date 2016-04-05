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


Definition hash_list T h values rx : prog T :=
  let^ (hash) <- ForN i < length values
  Hashmap hm'
  Ghost [ l crash ]
  Loopvar [ hash ]
  Continuation lrx
  Invariant
    [[ hash_list_rep (rev (firstn i values) ++ l) hash hm' ]]
  OnCrash crash
  Begin
    hash <- Hash (Word.combine (combine_entry (selN values i default_entry)) hash);
    lrx ^(hash)
  Rof ^(h);
  rx hash.


Theorem hash_list_ok : forall h values,
  {< l,
  PRE:hm
    emp * [[ goodSize addrlen (length values) ]]
        * [[ Forall (fun e => goodSize addrlen (fst e)) values ]]
        * [[ hash_list_rep l h hm ]]
  POST:hm' RET:h'
    emp * [[ hash_list_rep (rev values ++ l) h' hm' ]]
  CRASH:hm'
    emp * [[ exists i hash, hash_list_rep (rev (firstn i values) ++ l) hash hm' ]]
  >} hash_list h values.
Proof.
  unfold hash_list.
  step.
  step; try apply HL_nil; auto.

  assert (Hlength: length (rev (firstn (m + 1) values)) = S m).
    rewrite rev_length.
    rewrite firstn_length.
    rewrite min_l; omega.

  step.

  (* Loop invariant. *)
  - destruct (rev (firstn (m + 1) values)) eqn:Hrev_values.
    + simpl in Hlength. inversion Hlength.
    + destruct values.
      cbn in *. omega.

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
      eapply Forall_forall in H5; eauto.
      apply in_selN; auto.
      auto.
      apply upd_hashmap'_eq.
      intuition.
      unfold hash_safe in *.
      rewrite H8 in H16.
      inversion H16 as [ Hdef | Hdef ];
      contradict_hashmap_get_default Hdef hm0.

  (* Loop invariant implies post-condition. *)
  - step.
    rewrite firstn_oob in H9; try omega.
    auto.

  - exists 0; eexists. simpl. solve_hash_list_rep.

  Grab Existential Variables.
  all: econstructor.
Qed.

Hint Extern 1 ({{_}} progseq (hash_list _) _) => apply hash_list_ok : prog.
