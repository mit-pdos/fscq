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
Require Import EqdepFacts.
Require Import Arith.
Require Import ListUtils.
Require Import Omega.

Set Implicit Arguments.


Definition hash_list h values :=
  let^ (hash) <- ForEach item items_rest values
  Hashmap hm'
  Ghost [ l crash ]
  Loopvar [ hash ]
  Invariant
    exists items_prefix,
    [[ values = items_prefix ++ items_rest ]] *
    [[ hash_list_rep (rev items_prefix ++ l) hash hm' ]]
  OnCrash crash
  Begin
    hash <- Hash2 item hash;
    Ret ^(hash)
  Rof ^(h);
  Ret hash.


Theorem hash_list_ok : forall h values,
  {< l,
  PRE:hm
    emp * [[ hash_list_rep l h hm ]]
  POST:hm' RET:h'
    emp * [[ hash_list_rep (rev values ++ l) h' hm' ]]
  CRASH:hm'
    emp * [[ exists i hash, hash_list_rep (rev (firstn i values) ++ l) hash hm' ]]
  >} hash_list h values.
Proof.
  unfold hash_list.
  step.
  rewrite app_nil_l; reflexivity.
  rewrite app_nil_l; eassumption.
  step; try apply HL_nil; auto.
  step.

  (* Loop invariant. *)
  - rewrite <- cons_nil_app. eauto.
  - rewrite rev_unit. cbn [app].
    econstructor; eauto using hash_list_rep_upd.
    eauto using hashmap_get_fwd_safe_eq.
  - repeat eexists.
    rewrite firstn_app_r, firstn_O.
    rewrite app_nil_r. eauto.
  (* Loop invariant implies post-condition. *)
  - step.
    rewrite app_nil_r. eauto.
  - repeat eexists.
    rewrite firstn_O. cbn. solve_hash_list_rep.
  Grab Existential Variables.
  all: eauto.
  all: try ( exact tt || exact 0 || exact False ).
Qed.

Hint Extern 1 ({{_}} Bind (hash_list _ _) _) => apply hash_list_ok : prog.
