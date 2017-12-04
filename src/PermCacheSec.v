Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
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
Require Export PermCacheLemmas.


Import AddrMap.
Import Map MapFacts.
Import ListNotations.

Set Implicit Arguments.

  Theorem writeback_ok' :
    forall a cs pr,
    {< vs0,
    PERM: pr                       
    PRE:bm, hm,
        a |+> vs0 * [[ forall hb, Map.find a (CSMap cs) = Some hb -> exists v, bm (fst hb) = Some v ]]
    POST:bm', hm',  RET:cs'
      [[ bm' = bm ]] *
      exists h v,
      ([[ Map.find a (CSMap cs) = Some (h, true) /\ bm' h = Some v /\
          cs' = mk_cs (Map.add a (h, false) (CSMap cs))
                      (CSMaxCount cs) (CSCount cs) (CSEvict cs) ]] *
         a |+> (v, vsmerge vs0)) \/
      ([[ (Map.find a (CSMap cs) = None \/
           Map.find a (CSMap cs) = Some (h, false)) /\ cs' = cs ]] * a |+> vs0) 
    CRASH:bm'', hm'',
       a |+> vs0 \/ (exists v, ([[ forall hb, find a (CSMap cs) = Some hb -> bm (fst hb) = Some v ]] * a |+> (v, vsmerge vs0))%pred)%pred
    >} writeback a cs.
  Proof.
    unfold writeback; intros.
    prestep.
    norml.
    edestruct H5; eauto; cleanup; simpl in *.
    unfold stars; norm.
    unfold stars; cancel.
    eassign F_.
    eassign (t0, l).
    cancel.
    intuition; eauto.
    hoare.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1.
    cancel.
    or_r; cancel.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1.
    cancel; eauto.
    or_l; cancel; eauto.

    norml.
    edestruct H5; eauto; cleanup; simpl in *.
    unfold stars; norm.
    unfold stars; cancel.
    intuition; eauto.
    step.
    rewrite <- H1.
    cancel.
    or_l; cancel.
    eauto.

    norm.
    unfold stars; cancel.
    intuition; eauto.
    hoare.
    rewrite <- H1.
    cancel.
    or_l; cancel.
    eauto.
    Unshelve.
    all:eauto.
  Qed.

Theorem writeback_ok :
  forall a cs pr,
    {< d,
     PERM: pr
     PRE: bm, hm,
       rep cs d bm
     POST: bm', hm',
       RET:cs'
         rep cs' d bm' * [[ bm' = bm ]] *
          [[ addr_clean (CSMap cs') a ]] * 
          [[ In a (CSMap cs) -> In a (CSMap cs')]]
     CRASH:bm'', hm'',
       exists cs', rep cs' d bm''
    >} writeback a cs.
Proof.
  unfold writeback, rep, addr_valid; intros; cleanup.
  destruct (find a (CSMap cs)) eqn:D.
  {
    destruct p.
    destruct b.
    {
      prestep. (* step not smart enough *)
      unfold pimpl; intros m Hp; destruct_lift Hp.
      assert (A: In a (CSMap cs)). {        
        apply MapFacts.in_find_iff.
        intuition; congruence.
      }
      specialize (H7 _ A) as Hx.
      destruct (dummy0 a) eqn: D0; try congruence; clear Hx.
      rewrite mem_pred_extract' in H; eauto.
      unfold mem_pred_one, cachepred at 2 in H; simpl in H.
      rewrite D in H.
      destruct_lift H.

      pred_apply; norm.
      unfold stars; simpl; cancel.
      eassign (dummy1, l).
      cancel.
      intuition; eauto.
      
      step.
      step; eauto.
      erewrite <- mem_pred_absorb_nop with (hm:= dummy0)(a:= a); eauto.
      unfold cachepred; simpl; eauto.
      rewrite MapFacts.add_eq_o; eauto; simpl.
      erewrite ptsto_subset_pimpl.
      eassign l.
      simpl; cancel; eauto.
      apply mem_pred_pimpl_except; intros.
      rewrite MapFacts.add_neq_o; auto.
      unfold vsmerge; simpl.
      eapply incl_cons; eauto.
      apply incl_refl.

      unfold size_valid in *; simpl; auto.
      repeat rewrite map_add_dup_cardinal; auto.      
      destruct (Nat.eq_dec a a0); subst; try congruence.
      apply add_neq_in_iff in H6; eauto.
      unfold addr_clean.
      right; eexists; apply add_eq_o; eauto.
      apply add_in_iff; intuition.
      eexists; eapply hashmap_subset_trans; eauto.

      { (* Crash 1 *)
        unfold pimpl; intros; apply H2;
        pred_apply; cancel.
        eassign {| CSMap := add a (h, false) (CSMap cs);
                   CSMaxCount := CSMaxCount cs;
                   CSCount := CSCount cs;
                   CSEvict := CSEvict cs |}.
        simpl; erewrite <- mem_pred_absorb_nop with (hm:= dummy0)(a:= a); eauto.
        unfold cachepred at 3; simpl; eauto.
        rewrite MapFacts.add_eq_o; eauto; simpl.
        erewrite ptsto_subset_pimpl.
        eassign l.
        simpl; cancel; eauto.
        apply mem_pred_pimpl_except; intros.
        unfold cachepred.
        rewrite MapFacts.add_neq_o; eauto.
        unfold block_mem_subset in *; cleanup.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H8 p_1); cleanup; auto.
        unfold vsmerge; simpl.
        eapply incl_cons; eauto.
        apply incl_refl.

        unfold size_valid in *; simpl; auto.
        repeat rewrite map_add_dup_cardinal; auto.      
        simpl in *; destruct (Nat.eq_dec a a0); subst; try congruence.
        apply add_neq_in_iff in H12; eauto.
        eexists; eapply hashmap_subset_trans; eauto.
      }
      {
        apply H2;
        pred_apply; cancel; eauto.
        erewrite <- mem_pred_absorb_nop with (hm:= dummy0)(a:= a); eauto.
        unfold cachepred at 3; simpl; eauto.
        rewrite D; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        unfold block_mem_subset in *; cleanup.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H8 p_1); cleanup; auto.
      }
    }    
    unfold addr_clean; hoare.
    rewrite <- H1; cancel; eauto.
    erewrite mem_pred_pimpl; cancel.
    unfold cachepred.
    unfold block_mem_subset in *; cleanup.
    destruct (find a0 (CSMap cs)); cancel.
    destruct p_2; cancel;
    specialize (H5 p_1); cleanup; auto.
  }
  unfold addr_clean; hoare.
  rewrite <- H1; cancel; eauto.
  erewrite mem_pred_pimpl; cancel.
  unfold cachepred.
  unfold block_mem_subset in *; cleanup.
  destruct (find a0 (CSMap cs)); cancel.
  destruct p_2; cancel;
  specialize (H5 p_1); cleanup; auto.
Qed.

Hint Extern 1 (corr2 _ _ (Bind (writeback _ _) _)) => apply writeback_ok : prog.

Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (synrep _ _ _ _ _) (synrep _ _ _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (mem_pred ?p _) (mem_pred ?p _)) => constructor : okToUnify.


Theorem evict_ok :
  forall a cs pr,
    {< d ,
     PERM: pr
     PRE: bm, hm,
      rep cs d bm
    POST: bm', hm',
      RET:cs'
        rep cs' d bm' * [[ bm' = bm ]] *
        [[ ~ In a (CSMap cs') ]] *
        [[ In a (CSMap cs) -> cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH: bm'', hm'',
       exists cs', rep cs' d bm''
    >} evict a cs.
  Proof.
    unfold evict; step.
    unfold rep in *; destruct (find a (CSMap r_)) eqn:D.
    {
      hoare.
      eapply addr_valid_ptsto_subset in D as Hx;
      eauto; cleanup.      
      eapply addr_clean_cachepred_remove; eauto.
      
      apply size_valid_remove; auto.
      eapply in_find_iff; intuition; congruence.
      apply addr_valid_remove; auto.
      eapply remove_1; eauto.
      eapply size_valid_remove_cardinal_ok; eauto.
      eexists; eapply hashmap_subset_trans; eauto.
      rewrite <- H1; cancel; eauto.
      erewrite mem_pred_pimpl; cancel.
      unfold cachepred.
      unfold block_mem_subset in *; cleanup.
      destruct (find a0 (CSMap r_)); cancel.
      destruct p_3; cancel;
      specialize (H7 p_0); cleanup; auto.
      eexists; eapply hashmap_subset_trans; eauto.
    }
    
    {
      hoare.    
      eapply addr_clean_cachepred_remove_none; eauto.
      apply size_valid_remove_notin; auto.
      unfold not; intros.
      eapply in_find_iff in D; congruence.
      apply addr_valid_remove; auto.
      eapply remove_1; eauto.
      eapply size_valid_remove_cardinal_ok; eauto.
      eexists; eapply hashmap_subset_trans; eauto.
      rewrite <- H1; cancel; eauto.
      erewrite mem_pred_pimpl; cancel.
      unfold cachepred.
      unfold block_mem_subset in *; cleanup.
      destruct (find a0 (CSMap r_)); cancel.
      destruct p_2; cancel;
      specialize (H7 p_1); cleanup; auto.
      eexists; eapply hashmap_subset_trans; eauto.
    }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (evict _ _) _)) => apply evict_ok : prog.



Theorem maybe_evict_ok :
  forall cs pr,
  {< d,
    PERM: pr                          
    PRE: bm, hm,
      rep cs d bm
    POST: bm', hm', RET:cs'
      rep cs' d bm'* [[ bm' = bm ]] *
      [[ cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH:bm'', hm'',
        exists cs', rep cs' d bm''
    >} maybe_evict cs.
Proof.
  unfold maybe_evict; step. step_r.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  rewrite <- H1; cancel; eauto.
  eassign cs.
  unfold rep; cancel.
  erewrite mem_pred_pimpl; cancel.
  unfold cachepred.
  unfold block_mem_subset in *; cleanup.
  destruct (find a (CSMap cs)); cancel.
  destruct p_2; cancel;
  specialize (H4 p_1); cleanup; auto.
  step.
  apply H9; apply in_find_iff; intuition; congruence.
  step_r.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  rewrite cardinal_1 in *; cleanup; rewrite Heql in *; simpl in *; omega.
  rewrite <- H1; cancel; eauto.
  eassign cs.
  unfold rep; cancel.
  erewrite mem_pred_pimpl; cancel.
  unfold cachepred.
  unfold block_mem_subset in *; cleanup.
  destruct (find a (CSMap cs)); cancel.
  destruct p_2; cancel;
  specialize (H4 p_1); cleanup; auto.
  step.
  apply find_elements_hd in Heql;
  apply H9; apply in_find_iff; intuition; congruence.  
Qed.

Hint Extern 1 (corr2 _ _ (Bind (maybe_evict _) _)) => apply maybe_evict_ok : prog.


Theorem read_ok :
  forall cs a pr,
  {< d F tbs,
    PERM: pr                 
    PRE: bm, hm,
      rep cs d bm *
      [[ (sep_star (AEQ:= addr_eq_dec) F (a |+> tbs))%pred d ]]
    POST: bm', hm', (RET:^(cs', r)
      rep cs' d bm' * [[ bm' = upd bm r (fst tbs) ]])%pred
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm''
  >} read a cs.
Proof.
  unfold read; intros.
  safestep; eauto.
  eapply ptsto_subset_valid' in H4 as Hx; cleanup; simpl in *.
  repeat destruct_branch.
  step. step_r.
  unfold rep in *; erewrite mem_pred_extract with (a := a) in H5; eauto; 
  unfold cachepred at 2 in H5; rewrite Heqo in H5.
  destruct p_2; destruct_lift H5;
  symmetry; eapply upd_nop; eauto.
  eexists; eapply hashmap_subset_trans; eauto.
  rewrite <- H1; cancel; eauto.
  eassign r_.
  unfold rep; cancel.
  erewrite mem_pred_pimpl; cancel.
  unfold cachepred.
  unfold block_mem_subset in *; cleanup.
  destruct (find a0 (CSMap r_)); cancel.
  destruct p_3; cancel;
  specialize (H8 p_0); cleanup; auto.
  eexists; eapply hashmap_subset_trans; eauto.

  safestep.
  unfold rep in *; erewrite mem_pred_extract with (a := a); eauto; 
  unfold cachepred at 2; rewrite Heqo.
  eassign (t0, x).
  eassign (F_ * [[ size_valid r_ ]] *
                   [[ addr_valid d (CSMap r_) ]] *
                   mem_pred (HighAEQ:=addr_eq_dec)
                            (cachepred (CSMap r_) bm) (mem_except d a))%pred.
  cancel.
  eauto.
  unfold rep in *; hoare.
  
  rewrite sep_star_comm.
  eapply mem_pred_cachepred_add_absorb_clean; eauto.
  apply size_valid_add; auto.
  eapply addr_valid_add; eauto.
  eexists; eapply hashmap_subset_trans; eauto.
  eapply hashmap_subset_trans; eauto.
  
  rewrite <- H1; cancel; eauto.
  (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
  unfold cachepred at 3; rewrite Heqo;
  cancel; eauto.
  erewrite mem_pred_pimpl; cancel.
  unfold cachepred.
  eapply block_mem_subset_trans in H10; try apply H11.
  unfold block_mem_subset in *; cleanup.
  destruct (find a0 (CSMap r_)); cancel.
  destruct p_2; cancel;
  specialize (H10 p_1); cleanup; auto.
  eexists; eapply hashmap_subset_trans; eauto.
  eapply hashmap_subset_trans; eauto.
  
  rewrite <- H1; cancel; eauto.
  unfold rep; cancel; eauto.
  (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
  unfold cachepred at 3; rewrite Heqo;
  cancel; eauto.
  erewrite mem_pred_pimpl; cancel.
  unfold cachepred.
  unfold block_mem_subset in *; cleanup.
  destruct (find a0 (CSMap r_)); cancel.
  destruct p_2; cancel;
  specialize (H8 p_1); cleanup; auto.
  eexists; eapply hashmap_subset_trans; eauto.
  Unshelve.
  unfold EqDec.
  intros; apply handle_eq_dec.
Qed.

Hint Extern 1 (corr2 _ _ (Bind (read _ _) _)) => apply read_ok : prog.

Theorem write_ok':
  forall cs a h pr,
    {< d F tb0 tb,
     PERM: pr
     PRE: bm, hm,
            rep cs d bm *
            [[ bm h = Some tb ]] *
            [[ (F * a |+> tb0)%pred d ]]
    POST: bm', hm', RET:cs'
      exists d',
        rep cs' d' bm' * [[ bm' = bm ]] *
        [[ (sep_star (AEQ:= addr_eq_dec) F  (a |+> (tb, vsmerge tb0)))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm'' 
     >} write a h cs.
Proof.
    unfold write; intros.
    safestep; eauto.
    
    eapply ptsto_subset_valid' in H0 as Hx; cleanup; simpl in *.
    hoare.
    {
      unfold rep; simpl;
      erewrite mem_pred_extract with (a := a) at 1; eauto.
      unfold cachepred at 2; rewrite Heqo; eauto; cancel.
      (rewrite mem_pred_pimpl_except;
       [ | intros; apply cachepred_add_invariant with (v':=(h, true)); eassumption]).
      rewrite <- mem_pred_absorb with (hm := d) (a := a);
      unfold cachepred at 3;
      rewrite MapFacts.add_eq_o by reflexivity.
      destruct p_2.
      cancel.
      eassign (tb, vsmerge(t0, l)).
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      simpl; auto.
      simpl; right; eapply In_incl; eauto.

      cancel.
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      
      eapply size_valid_add_in; eauto.
      eapply addr_valid_upd_add; eauto.
    }
    eapply ptsto_subset_upd; eauto; apply incl_refl.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel; eauto.
     eassign r_.
     unfold rep; cancel.
     erewrite mem_pred_pimpl; cancel.
     unfold cachepred.
     unfold block_mem_subset in *; cleanup.
     destruct (find a0 (CSMap r_)); cancel.
     destruct p_3; cancel;
     specialize (H9 p_0); cleanup; auto.
     eexists; eapply hashmap_subset_trans; eauto.
    
    {
      unfold rep; simpl;
      erewrite mem_pred_extract with (a := a) at 1; eauto.
      unfold cachepred at 2; rewrite Heqo; eauto; cancel.
      (rewrite mem_pred_pimpl_except;
       [ | intros; apply cachepred_add_invariant with (v':=(h, true)); eassumption]).
      rewrite <- mem_pred_absorb with (hm := d) (a := a);
      unfold cachepred at 3;
      rewrite MapFacts.add_eq_o by reflexivity.
      cancel.
      eassign (tb, vsmerge(t0, l)).
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      simpl; auto.
      simpl; auto.

      eapply size_valid_add; eauto.
      eapply addr_valid_upd_add; eauto.
    }
    eapply ptsto_subset_upd; eauto; apply incl_refl.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel; eauto.
    eassign r_.
    unfold rep; cancel.
    erewrite mem_pred_pimpl; cancel.
    unfold cachepred.
    unfold block_mem_subset in *; cleanup.
    destruct (find a0 (CSMap r_)); cancel.
    destruct p_2; cancel;
    specialize (H9 p_1); cleanup; auto.
    eexists; eapply hashmap_subset_trans; eauto.    
Qed.    

Hint Extern 1 (corr2 _ _ (Bind (write _ _ _) _)) => apply write_ok' : prog.

Theorem begin_sync_ok :
  forall cs pr,
    {< d F,
     PERM: pr   
     PRE:bm, hm,
       rep cs d bm * [[ F d /\ sync_invariant F ]]
     POST:bm', hm', RET:cs
       exists d',
         synrep cs d d' bm * [[ bm' = bm ]] * [[ F d' ]]
     CRASH:bm'', hm'',
       exists cs', rep cs' d bm''
    >} begin_sync cs.
  Proof.
    unfold begin_sync, synrep.
    step.
    prestep.
    norml; unfold stars; simpl.
    rewrite rep_synrep by eauto.
    cancel; eauto.
    rewrite <-H1; cancel; eauto.
     eassign cs.
     unfold rep; cancel.
     erewrite mem_pred_pimpl; cancel.
     unfold cachepred.
     unfold block_mem_subset in *; cleanup.
     destruct (find a (CSMap cs)); cancel.
     destruct p_2; cancel;
     specialize (H5 p_1); cleanup; auto.
  Qed.
  
Theorem end_sync_ok :
  forall cs pr,
   {< d0 d,
    PERM: pr
    PRE:bm, hm,
      synrep cs d0 d bm
    POST:bm', hm', RET:cs
      rep cs d bm' * [[ bm' = bm ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} end_sync cs.
  Proof.
    unfold end_sync; intros.
    hoare.
    unfold rep, synrep, synrep', mem_pred, mem_pred_one; simpl.
    rewrite sync_xform_sep_star_dist, sync_xform_and_dist. rewrite pimpl_r_and.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    norml; unfold stars; simpl.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    cancel; auto.
    rewrite sync_xform_listpred_synpred_cachepred; auto.
    rewrite sync_xform_sync_invariant by auto.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel; eauto.
    rewrite sync_xform_sep_star_dist.
    repeat rewrite sync_xform_sync_invariant by auto; cancel.
    unfold synrep.
    rewrite pimpl_l_and.
    eassign cs.
    unfold rep; cancel.
    erewrite mem_pred_pimpl; cancel.
    unfold cachepred.
    unfold block_mem_subset in *; cleanup.
    destruct (find a (CSMap cs)); cancel.
    destruct p_2; cancel;
    specialize (H5 p_1); cleanup; auto.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel; eauto.
    unfold synrep.
    rewrite pimpl_l_and.
    eassign cs.
    unfold rep; cancel.
    erewrite mem_pred_pimpl; cancel.
    unfold cachepred.
    unfold block_mem_subset in *; cleanup.
    destruct (find a (CSMap cs)); cancel.
    destruct p_2; cancel;
    specialize (H4 p_1); cleanup; auto.
  Qed.

  
  Theorem sync_ok' :
    forall cs a pr,
   {< d0 d (F F' : rawpred) v0 v',
    PERM: pr   
    PRE:bm, hm,
      synrep cs d0 d bm * [[ sync_invariant F ]] *
      [[ (F * a |+> v0)%pred d ]] *
      [[ (F' * a |+> v')%pred d0 ]]
    POST:bm', hm', RET:cs
      exists d,
        synrep cs d0 d bm' * [[ bm' = bm ]] *
        [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH:bm'', hm'',
      exists cs', (rep cs' d0 bm'' \/
              exists v, ([[ forall hb, find a (CSMap cs) = Some hb -> bm (fst hb) = Some v ]] *
                    rep cs' (upd d0 a (v, vsmerge v')) bm''))
    >} sync a cs.
  Proof.
    unfold sync; intros.
    eapply pimpl_ok2; monad_simpl. apply writeback_ok'.
    intros.
    norml; unfold stars; simpl.
    denote (_ d) as Hx; apply ptsto_subset_valid' in Hx as Hy; repeat deex.
    denote (_ d0) as Hz; apply ptsto_subset_valid' in Hz as Hy; repeat deex.
    unfold synrep, rep, synrep'.
    rewrite sep_star_lift_empty.
    rewrite sep_star_lift_empty.
    rewrite lift_empty_and_distr_l; norml; unfold stars; simpl.
    rewrite mem_pred_extract with (a := a) (hm := d) by eauto.
    rewrite mem_pred_extract with (a := a) (hm := d0) by eauto.
    unfold cachepred at 2; unfold synpred at 2; simpl in *.
    destruct (Map.find a (CSMap cs)) eqn:?; try destruct p, b.
    - unfold ptsto_subset at 1 2.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      safecancel; simpl in *; cleanup.
      eassign (t2, l2).
      unfold ptsto_subset;
      cancel; simpl; eauto.
      auto.

      
      hoare.
      repeat cleanup.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply cachepred_add_invariant; eassumption.
        cancel.        
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply synpred_add_invariant; eassumption.
        eassign (v, old); simpl.
        cancel.
        simpl; auto.
        simpl; auto.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
        rewrite upd_eq; auto.
        apply addr_valid_upd; auto.
      + eexists; eapply hashmap_subset_trans; eauto.
      + (* crash *)
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_r.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H19 p_1); cleanup; auto.
        unfold vsmerge in *; simpl in *; auto.
        eapply incl_tran; eauto.         
        apply incl_cons; eauto.
        right; eapply In_incl; eauto. 
        right; auto.
        apply addr_valid_upd; eauto.
        eexists; eapply hashmap_subset_trans; eauto.
      +
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_l.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H10 p_1); cleanup; auto.
       (* crash 3 *)
        specialize (H9 (h, true) (eq_refl (Some (h,true)))); simpl in *; cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_r.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a1 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H10 p_1); cleanup; auto.
        unfold vsmerge in *; simpl in *; auto.
        eapply incl_tran; eauto.         
        apply incl_cons; eauto.
        right; eapply In_incl; eauto. 
        right; auto.
        apply addr_valid_upd; eauto.

    - unfold ptsto_subset at 1 2.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      safecancel; simpl in *; cleanup.
      eassign (t2, l2).
      unfold ptsto_subset;
      cancel; simpl; eauto.
      auto.

      hoare.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_comm, sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
      
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eassign (t2, old); cancel.
        simpl; auto.
        simpl; auto.
        apply addr_valid_upd; auto.
      + eexists; eapply hashmap_subset_trans; eauto.
      +
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_l.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H11 p_1); cleanup; auto.
        eexists; eapply hashmap_subset_trans; eauto.
       (* crash 3 *)
      + 
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_l.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H10 p_1); cleanup; auto.

        specialize (H9 (h, false) (eq_refl (Some (h,false)))); simpl in *; cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_r.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a1 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H10 p_1); cleanup; auto.
        apply addr_valid_upd; eauto.

    - unfold ptsto_subset at 1 2.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      safecancel; simpl in *; cleanup.
      eassign (t2, l2).
      unfold ptsto_subset;
      cancel; simpl; eauto.
      auto.

      hoare.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.

      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eassign (t2, old); cancel.
        simpl; auto.
        apply addr_valid_upd; auto.
      + eexists; eapply hashmap_subset_trans; eauto.
      +
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_l.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H11 p_1); cleanup; auto.
        eexists; eapply hashmap_subset_trans; eauto.
       (* crash 3 *)
      + 
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        or_l.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a0 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H10 p_1); cleanup; auto.

        rewrite sep_star_and_distr, pimpl_l_and.
        or_r.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        erewrite mem_pred_pimpl; cancel.
        unfold cachepred.
        destruct (find a1 (CSMap cs)); cancel.
        destruct p_2; cancel;
        specialize (H10 p_1); cleanup; auto.
        apply addr_valid_upd; eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem sync_synrep_helper_1 : forall m cs d0 d a (F : @pred _ addr_eq_dec _) bm v,
    synrep cs d0 d bm m ->
    (F * a |+> v)%pred d ->
    exists (F0 : @pred _ addr_eq_dec _) v0,
    (F0 * a |+> v0)%pred d0.
  Proof.
    unfold synrep, rep, synrep', ptsto_subset; intros.
    case_eq (d0 a); intros.
    - destruct v0.
      eapply any_sep_star_ptsto in H1.
      pred_apply.
      safecancel.
      eassign (t0, l).
      eassign l.
      cancel.
      firstorder.
    - destruct H.
      destruct_lift H.
      destruct_lift H2.
      destruct_lift H0.
      apply ptsto_valid' in H0.
      eapply mem_pred_absent_lm in H; eauto.
      eapply mem_pred_absent_hm in H2; eauto.
      congruence.

      unfold synpred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.

      unfold cachepred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.
  Qed.

  Theorem sync_synrep_helper_2 : forall cs d0 d bm a (F : @pred _ addr_eq_dec _) v,
    (F * a |+> v)%pred d ->
    synrep cs d0 d bm =p=> synrep cs d0 d bm * exists (F0 : @pred _ addr_eq_dec _) v0,
    [[ (F0 * a |+> v0)%pred d0 ]].
  Proof.
    unfold pimpl; intros.
    eapply sync_synrep_helper_1 in H; eauto; repeat deex.
    pred_apply; cancel.
    eassign F0; cancel.
  Qed.


  Theorem sync_ok :
    forall cs pr a,
   {< d0 d (F : rawpred) v0,
    PERM: pr                 
    PRE:bm, hm,
      synrep cs d0 d bm *
      [[ (F * a |+> v0)%pred d ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:cs exists d,
      synrep cs d0 d bm' * [[ bm' = bm ]] *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH: bm'', hm'',
      exists cs', (rep cs' d0 bm'' \/
      exists F' v v', ([[ (sep_star (AEQ:= addr_eq_dec) F' (a |+> v'))%pred d0 ]] *
                  rep cs' (upd d0 a (v, vsmerge v')) bm''))
    >} sync a cs.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply sync_ok'.
    intros; norml; unfold stars; simpl.
    rewrite sync_synrep_helper_2 by eauto.
    safecancel.
    eassign F_; cancel.
    apply H5.
    eauto.
    eauto.
    eauto.
    step.
    rewrite <- H1.
    cancel.
    or_l; cancel.
    eexists; eapply hashmap_subset_trans; eauto.
    or_r; cancel.
    eauto.
  Qed.



Definition init_load := init.
Definition init_recover := init.
  

Theorem init_load_ok :
  forall cachesize pr,
    {!< disk,
    PERM: pr   
    PRE: bm, hm,
      arrayS 0 disk *
      [[ cachesize <> 0 ]]
    POST:bm',hm', RET:cs
      exists d,
      rep cs d bm' * [[ bm' = bm ]] *
      [[ arrayS 0 disk d ]]
    CRASH:bm'', hm'',
      arrayS 0 disk 
    >!} init_load cachesize.
  Proof.
    unfold init_load, init; step.
    step.
    
    eapply pimpl_ok2; monad_simpl; eauto.
    simpl; intros.

    unfold pimpl; intros.
    destruct_lift H0; subst.

    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    exists m.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm.
    apply sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sync_xform_arrayS in H0.
    eapply mem_pred_cachepred_refl_arrayS; eauto.
    apply size_valid_cache0; eauto.
    apply addr_valid_empty.
    apply sync_xform_arrayS in H0; eauto.
    cleanup.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel.
    apply sync_xform_arrayS.
    eexists; eapply hashmap_subset_trans; eauto.
  Qed.


    Lemma sync_xform_cachepred : forall m bm a vs,
    sync_xform (cachepred m bm a vs) =p=> 
      exists v, [[ List.In v (vsmerge vs) ]] * a |=> v.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros; try destruct p, b.
    - rewrite sync_xform_exists_comm.
      apply pimpl_exists_l; intro.
      repeat rewrite sync_xform_sep_star_dist, sync_xform_lift_empty.
      rewrite sync_xform_ptsto_subset_precise; simpl.
      cancel.
    - rewrite sync_xform_sep_star_dist, sync_xform_lift_empty.
      rewrite sync_xform_ptsto_subset_precise; simpl.
      cancel.
    - rewrite sync_xform_ptsto_subset_precise; cancel.
  Qed.



Theorem sync_xform_mem_pred : forall prd (hm : rawdisk),
  sync_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => sync_xform (prd a v)) hm.
Proof.
  unfold mem_pred; intros; split.
  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.

  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  apply pimpl_exists_r; eexists.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.
Qed.

  
  Lemma sync_xform_mem_pred_cachepred : forall cm bm m,
    sync_xform (mem_pred (HighAEQ:=addr_eq_dec) (cachepred cm bm) m) =p=> exists m',
      mem_pred (HighAEQ:=addr_eq_dec) (cachepred (Map.empty (handle * bool)) bm) m' * [[ possible_crash m m' ]].
  Proof.
    intros.
    rewrite sync_xform_mem_pred.
    unfold mem_pred at 1.
    xform_norm; subst.

    rename hm_avs into l.
    revert H; revert l.
    induction l; simpl; intros.
    cancel.
    apply mem_pred_empty_mem.
    unfold possible_crash; intuition.

    inversion H; destruct a; subst; simpl in *.
    unfold mem_pred_one; simpl.

    rewrite IHl by auto.
    xform_norm.
    rewrite sync_xform_cachepred.
    norml; unfold stars; simpl.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    cleanup.
    apply possible_crash_upd; eauto.
    apply possible_crash_upd; eauto.
    unfold vsmerge; simpl; auto.
  Qed.


  Theorem init_recover_ok :
    forall cachesize pr,
    {< d F,
    PERM: pr                           
    PRE:bm, hm,
      exists cs, rep cs d bm *
      [[ F d ]] * [[ cachesize <> 0 ]]
    POST:bm', hm', RET:cs'
      exists d', rep cs' d' bm' * [[ bm' = bm ]] *
             [[ (crash_xform F) d' ]]
    CRASH:bm'', hm'',
      exists cs, rep cs d bm'' \/ (exists d', rep cs d' bm'' * [[ (crash_xform F) d' ]])
    >} init_recover cachesize.
  Proof.
    unfold init_recover, init, rep.
    step.
    
    prestep; norml; unfold stars; simpl.
    rewrite sync_xform_sep_star_dist.
    rewrite sync_xform_mem_pred_cachepred; norm.
    cancel.
    intuition eauto.
    step.
    rewrite sync_xform_sync_invariant; auto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
    unfold crash_xform; eexists; eauto.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite sync_xform_sync_invariant; auto.
    rewrite <- H1; safecancel.
    or_r; safecancel.
    eassign (cache0 cachesize); simpl.
    eassign m'.
    cancel.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    simpl in *; eapply MapFacts.empty_in_iff; eauto.
    unfold crash_xform; eexists; eauto.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel; eauto.
    or_l; cancel; eauto.
    erewrite mem_pred_pimpl; cancel.
    unfold cachepred.
    destruct (find a (CSMap cs)); cancel.
    destruct p_2; cancel;
    specialize (H7 p_1); cleanup; auto.
  Qed.


  Theorem write_ok :
    forall cs a h pr,
    {< d (F : rawpred) v v0,
    PERM: pr   
    PRE:bm, hm,
        rep cs d bm * [[ bm h = Some v ]] *
        [[ (F * a |+> v0)%pred d ]]
    POST:bm', hm', RET:cs
      exists d',
        rep cs d' bm' [[ bm' = bm ]] *
        [[ (F * a |+> (v, vsmerge v0))%pred d' ]]
    XCRASH:bm'', hm''
      exists cs' d', rep cs' d' bm'' *
      [[  (F * a |+> (v, vsmerge v0))%pred d' ]]
    >} write a h cs.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.
    cancel.
    xcrash_rewrite.

    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.
    edestruct ptsto_subset_valid' with (a := a); eauto; intuition.
    edestruct possible_crash_sel_exis; eauto; intuition.
    rewrite mem_pred_extract with (a := a) by eauto.

    cancel; xform_normr.
    rewrite <- crash_xform_rep_r.
    unfold rep; cancel.
    eapply pimpl_trans2.
    eapply mem_pred_absorb_nop with (a := a).
    2: apply pimpl_refl.
    eauto.
    eauto.
    eauto.
    eapply ptsto_subset_upd; eauto.
    2: eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    2: apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.
  Qed.







  
  Hint Extern 1 ({{_}} Bind (init_recover _) _) => apply init_recover_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_load _) _) => apply init_load_ok : prog.




  
  Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (begin_sync _) _) => apply begin_sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (end_sync _) _) => apply end_sync_ok : prog.

