Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import PermArray.
Require Import Pred.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred. 
Require Import FunctionalExtensionality.
Require Import ADestructPair DestructVarname.
Require Export PermCacheSec.


Import AddrMap.
Import Map MapFacts.
Import ListNotations.

Set Implicit Arguments.


  Theorem read_range_ok :
    forall a nr cs pr,
    {< d F vs,
    PERM: pr   
    PRE:bm, hm,
        rep cs d bm *
        [[ (F * arrayS a vs)%pred d ]] *
        [[ nr <= length vs ]]
   POST:bm', hm',
      RET:^(cs, r)
       rep cs d bm' *
      [[ extract_blocks bm' r = firstn nr (List.map fst vs)]] *
      [[ handles_valid bm' r ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm''
    >} read_range a nr cs.
  Proof.
    unfold read_range; intros.
    step.
    unfold handles_valid; auto.
    step.

    step.
    step.
    constructor; unfold handle_valid; eauto.
    eapply handles_valid_subset_trans; eauto.
    erewrite firstn_S_selN_expand.
    erewrite selN_map; auto.
    rewrite extract_blocks_app; simpl.
    rewrite H18.
    clear H17; erewrite <- extract_blocks_subset; eauto.
    rewrite H13; auto.
    apply handles_valid_rev_eq; auto.
    eapply le_trans; [| eauto].
    omega.
    rewrite map_length.
    eapply le_trans; [| eauto].
    omega.
    solve_hashmap_subset.

    rewrite <- H1; cancel; eauto.
    solve_hashmap_subset.

    step.
    step.
    apply handles_valid_rev_eq; auto.
    solve_hashmap_subset.

    rewrite <- H1; cancel; eauto.
    
    Unshelve.
    all: eauto.
    exact tt.
    unfold EqDec; apply handle_eq_dec.
    exact tagged_block0.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem write_range_ok :
    forall a l cs pr,
    {< d F vs vsl,
    PERM: pr   
    PRE:bm, hm,
      rep cs d bm *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ length l <= length vs ]] *
      [[ vsl = extract_blocks bm l ]] *
      [[ handles_valid bm l ]]
    POST:bm', hm', RET:cs
      exists d', rep cs d' bm' *
      [[ (F * arrayS a (vsupd_range vs vsl))%pred d' ]]
    XCRASH:bm'', hm'',
      exists cs' d', rep cs' d' bm''*
      [[ (F * arrayS a (vsupd_range vs vsl))%pred d' ]]
    >} write_range a l cs.
  Proof.
    unfold write_range; intros.
    step.
    prestep; unfold rep; cancel.
    subst.

    erewrite extract_blocks_selN.
    rewrite <- H15; eauto.
    eapply handles_valid_subset_trans; eauto.
    auto.

    rewrite vsupd_range_length; try omega.
    eapply lt_le_trans; eauto.
    rewrite firstn_length_l; try omega.
    eapply le_trans; [|eauto].
    apply Nat.lt_le_incl; auto.
    apply handles_valid_length_eq in H5;
    rewrite <- H5; apply Nat.lt_le_incl; auto.

    step.
    prestep; unfold rep; cancel.
    erewrite firstn_S_selN_expand.
    setoid_rewrite <- vsupd_range_progress; auto.

    
    cancel.
    all: apply handles_valid_length_eq in H5; try rewrite <- H5; auto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    
    rewrite <- H1; cancel; eauto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    repeat xcrash_rewrite.
    setoid_rewrite vsupd_range_progress; auto.
    rewrite <- firstn_plusone_selN.

    apply vsupd_range_xcrash_firstn; auto.
    all: try rewrite <- H5; auto.

    step. step.
    rewrite firstn_oob; auto.
    rewrite <- H5; auto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    eassign (false_pred (AT:= addr)(AEQ:= addr_eq_dec)(V:= valuset))%pred.
    unfold false_pred; cancel.
    Unshelve.
    exact tt.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem sync_range_ok :
    forall a n cs pr,
    {< d d0 F vs,
    PERM: pr   
    PRE:bm, hm,
      synrep cs d0 d bm *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ n <= length vs /\ sync_invariant F ]]
    POST:bm', hm', RET:cs
      exists d', synrep cs d0 d' bm' *
      [[ (F * arrayS a (vssync_range vs n))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} sync_range a n cs.
  Proof.
    unfold sync_range; intros.
    safestep.
    eassign F_; cancel.
    unfold vssync_range; simpl; eauto.
    eauto.
    eauto.
    safestep.
    eassign F_; cancel.
    eauto.
    rewrite vssync_range_length; omega.
    all: auto.

    step. step.
    apply arrayN_unify.
    apply vssync_range_progress; omega.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    rewrite <- H1; cancel; eauto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    
    step. step.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    rewrite <- H1; cancel; eauto.
    
    Unshelve.
    exact tt.
    unfold EqDec; apply handle_eq_dec.
    auto.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (read_range _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write_range _ _ _) _) => apply write_range_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (sync_range _ _ _) _) => apply sync_range_ok : prog.