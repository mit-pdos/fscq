Require Import Mem.
Require Import List.
Require Import Prog.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import Cache.
Require Import MemPred.

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.


Record wbcachestate := {
  WbCs : cachestate;
  WbBuf : Map.t valu
}.

Module WBCACHE.

  Definition cachepred (cache : Map.t valu) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    match Map.find a cache with
    | None => a |-> vs
    | Some v => (exists vsdisk, a |-> vsdisk * [[ vs = (v, vsmerge vsdisk) ]])%pred
    end.

  Lemma cachepred_remove_invariant : forall a a' v cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.remove a' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma cachepred_add_invariant : forall a a' v v' cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.add a' v' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.

  Definition rep (wcs : wbcachestate) (m : rawdisk) : rawpred :=
    (exists cm, BUFCACHE.rep (WbCs wcs) cm *
     [[ @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred (WbBuf wcs)) m cm ]])%pred.

  Definition read T a (wcs : wbcachestate) rx : prog T :=
    match Map.find a (WbBuf wcs) with
    | Some v => rx ^(wcs, v)
    | None =>
      let^ (new_cs, v) <- BUFCACHE.read a (WbCs wcs);
      rx ^(Build_wbcachestate new_cs (WbBuf wcs), v)
    end.

  Definition write T a v (wcs : wbcachestate) rx : prog T :=
    rx (Build_wbcachestate (WbCs wcs) (Map.add a v (WbBuf wcs))).

  Definition sync T a (wcs : wbcachestate) rx : prog T :=
    match (Map.find a (WbBuf wcs)) with
    | Some v =>
      new_cs <- BUFCACHE.write a v (WbCs wcs);
      new_cs <- BUFCACHE.sync a new_cs;
      rx (Build_wbcachestate new_cs (Map.remove a (WbBuf wcs)))
    | None =>
      new_cs <- BUFCACHE.sync a (WbCs wcs);
      rx (Build_wbcachestate new_cs (WbBuf wcs))
    end.

  Definition cache0 sz := Build_wbcachestate (BUFCACHE.cache0 sz) (Map.empty _).

  Definition init T (cachesize : nat) (rx : wbcachestate -> prog T) : prog T :=
    rx (cache0 cachesize).

  Theorem read_ok : forall wcs a,
    {< d (F : rawpred) v,
    PRE
      rep wcs d * [[ (F * a |~> v)%pred d ]]
    POST RET:^(wcs, r)
      rep wcs d * [[ r = v ]]
    CRASH
      exists wcs', rep wcs' d
    >} read a wcs.
  Proof.
    unfold read. unfold rep at 1 2.
    (* Don't unfold the [rep] in the crash condition, since that
     * causes incorrect evar instantiation..
     *)
    intros.
    case_eq (Map.find a (WbBuf wcs)); intros.
    - step.
      step.
      subst.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6.
      destruct_lift H6; congruence.
      unfold rep; cancel.
    - step.
      rewrite mem_pred_extract; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2; rewrite H.
      cancel.
      step.
      instantiate (wcs' := Build_wbcachestate cs' (WbBuf wcs)).
      unfold rep; cancel.
  Qed.

  Definition hidden_pred AT AEQ V (p : @pred AT AEQ V) : pred := p.

  Theorem sync_ok : forall wcs a,
    {< d (F : rawpred) v vold,
    PRE
      rep wcs d * [[ (F * a |-> (v, vold))%pred d ]]
    POST RET:wcs
      exists d',
      rep wcs d' * [[ (F * a |=> v)%pred d' ]]
    CRASH
      (* This would be a good place to use XCRASH.. *)
      hidden_pred (exists wcs' d', rep wcs' d' *
      [[ (F * a |=> v)%pred d' \/ (F * a |-> (v, vold))%pred d' ]])%pred
    >} sync a wcs.
  Proof.
    unfold sync, rep.
    intros.
    case_eq (Map.find a (WbBuf wcs)); intros.
    - prestep; norm'l.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6. destruct_lift H6.
      cancel.
      step.
      step.
      rewrite <- mem_pred_absorb with (a := a).
      unfold cachepred at 3.
      rewrite MapFacts.remove_eq_o by auto.
      cancel.
      apply mem_pred_pimpl_except.
      intros; apply cachepred_remove_invariant; auto.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      (* crash conditions *)
      unfold hidden_pred; norm; unfold stars; simpl.
      instantiate (wcs' := Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite MapFacts.remove_eq_o by reflexivity. pred_apply; cancel.
        rewrite mem_pred_pimpl_except; cancel. apply cachepred_remove_invariant; auto.
      right.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      unfold hidden_pred; norm; unfold stars; simpl.
      instantiate (wcs' := Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite MapFacts.remove_eq_o by reflexivity. pred_apply; cancel.
        rewrite mem_pred_pimpl_except; cancel. apply cachepred_remove_invariant; auto.
      left.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      pimpl_crash.
      unfold hidden_pred; norm; unfold stars; simpl.

      instantiate (wcs' := Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite H. pred_apply; cancel.
      right. subst.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      instantiate (wcs'0 := Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite MapFacts.remove_eq_o by reflexivity. pred_apply; cancel.
        rewrite mem_pred_pimpl_except; cancel. apply cachepred_remove_invariant; auto.
      right. subst.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
    - prestep; norm'l.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6. destruct_lift H6.
      cancel.
      step.
      rewrite <- mem_pred_absorb with (a := a).
      unfold cachepred at 3.
      rewrite H.
      cancel.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      pimpl_crash.
      unfold hidden_pred; norm; unfold stars; simpl.

      instantiate (wcs' := Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite H. pred_apply; cancel.
      right. subst.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      instantiate (wcs'0 := Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite H. pred_apply; cancel.
      left. subst.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
  Qed.

End WBCACHE.
