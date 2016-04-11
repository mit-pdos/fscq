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
    | Some v => (exists vsdisk old_cache_writes, a |-> vsdisk * [[ vs = (v, old_cache_writes ++ vsmerge vsdisk) ]])%pred
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
      eassign (Build_wbcachestate cs' (WbBuf wcs)).
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
      [[ (F * a |=> v)%pred d' \/ exists n, (F * a |-> (v, skipn n vold))%pred d' ]])%pred
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
      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite MapFacts.remove_eq_o by reflexivity. pred_apply; cancel.
        rewrite mem_pred_pimpl_except; cancel. apply cachepred_remove_invariant; auto.
      right.
      exists (length dummy). rewrite skipn_app.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      unfold hidden_pred; norm; unfold stars; simpl.
      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite MapFacts.remove_eq_o by reflexivity. pred_apply; cancel.
        rewrite mem_pred_pimpl_except; cancel. apply cachepred_remove_invariant; auto.
      left.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      pimpl_crash.
      unfold hidden_pred; norm; unfold stars; simpl.

      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite H. pred_apply; cancel.
      right. subst.
      exists (length dummy). rewrite skipn_app.
      eassign (@nil valu); simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite MapFacts.remove_eq_o by reflexivity. pred_apply; cancel.
        rewrite mem_pred_pimpl_except; cancel. apply cachepred_remove_invariant; auto.
      right. subst.
      exists (length dummy). rewrite skipn_app.
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

      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite H. pred_apply; cancel.
      right. subst.
      exists 0; simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb. unfold cachepred at 2.
        rewrite H. pred_apply; cancel.
      left. subst.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
  Qed.

  Theorem write_ok : forall wcs a v,
    {< d (F : rawpred) v0,
    PRE
      rep wcs d * [[ (F * a |-> v0)%pred d ]]
    POST RET:wcs
      exists d', rep wcs d' * [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    CRASH
      exists wcs' d', rep wcs' d' *
      [[ (F * a |-> v0)%pred d' \/ (F * a |-> (v, vsmerge v0))%pred d' ]]
    >} write a v wcs.
  Proof.
    unfold write, rep.
    intros.
    case_eq (Map.find a (WbBuf wcs)); intros.
    - step.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6. destruct_lift H6.
      step.
      pred_apply. rewrite <- mem_pred_absorb. subst; simpl.
      unfold cachepred at 3. rewrite MapFacts.add_eq_o by reflexivity. cancel.
      apply mem_pred_pimpl_except. intros; apply cachepred_add_invariant; auto.
      eassign (w :: dummy); unfold vsmerge; simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

    - step.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6.
      step.
      subst; simpl.
      pred_apply.
      rewrite <- mem_pred_absorb with (a:=a). unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by auto. cancel.
      apply mem_pred_pimpl_except. intros; apply cachepred_add_invariant; auto.

      eassign (@nil valu); simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.


  Definition read_array T a i cs rx : prog T :=
    r <- read (a + i) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a + i) v cs;
    rx cs.

  Definition sync_array T a i cs rx : prog T :=
    cs <- sync (a + i) cs;
    rx cs.

  Theorem read_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:^(cs, v)
      rep cs d * [[ v = fst (selN vs i ($0, nil)) ]]
    CRASH
      exists cs', rep cs' d
    >} read_array a i cs.
  Proof.
    unfold read_array.
    hoare.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.
  Qed.


  Theorem write_array_ok : forall a i v cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    >} write_array a i v cs.
  Proof.
    unfold write_array, vsupd.
    hoare.

    pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    cancel.
    or_r; cancel.
    rewrite <- isolateN_bwd_upd by auto. cancel.
    apply pimpl_or_r; right; cancel; eauto.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.




  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _) _) => apply write_array_ok : prog.

  Theorem sync_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync vs i))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * arrayN a (vssync vs i))%pred d' ]]
    >} sync_array a i cs.
  Proof.
    unfold sync_array, vssync.
    hoare.

    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    cancel.
    apply pimpl_or_r; left; cancel; eauto.
    apply pimpl_or_r; right; cancel; eauto.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.



  Definition read_range T A a nr (vfold : A -> valu -> A) a0 cs rx : prog T :=
    let^ (cs, r) <- ForN i < nr
    Ghost [ F crash d vs ]
    Loopvar [ cs pf ]
    Continuation lrx
    Invariant
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) a0 ]]
    OnCrash  crash
    Begin
      let^ (cs, v) <- read_array a i cs;
      lrx ^(cs, vfold pf v)
    Rof ^(cs, a0);
    rx ^(cs, r).


  Definition write_range T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_range vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- write_array a i (selN l i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.

  Definition sync_range T a nr cs rx : prog T :=
    let^ (cs) <- ForN i < nr
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_range vs i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.


  Definition write_vecs T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      let v := selN l i (0, $0) in
      cs <- write_array a (fst v) (snd v) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.


  Definition sync_vecs T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a (selN l i 0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.

End WBCACHE.
