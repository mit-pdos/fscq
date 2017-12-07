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
       a |+> vs0
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

    norml.
    edestruct H5; eauto; cleanup; simpl in *.
    unfold stars; norm.
    unfold stars; cancel.
    intuition; eauto.
    step.
    rewrite <- H1; cancel; eauto.

    norm.
    unfold stars; cancel.
    intuition; eauto.
    hoare.
    rewrite <- H1; cancel; eauto.
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
  unfold writeback; intros; cleanup.
  destruct (find a (CSMap cs)) eqn:D.
  {
    destruct p.
    destruct b.
    {
      prestep. (* step not smart enough *)
      unfold rep, addr_valid; norml.
      assert (A: In a (CSMap cs)). {        
        apply MapFacts.in_find_iff.
        intuition; congruence.
      }
      specialize (H6 _ A) as Hx.
      destruct (d a) eqn: D0; try congruence; clear Hx.
      unfold stars; simpl. rewrite mem_pred_extract'; eauto.
      unfold mem_pred_one, cachepred at 2; simpl; cleanup.
      destruct v; simpl in *.

      norm.
      unfold stars; simpl; cancel.
      eassign (tb0, l); cancel.
      intuition; eauto.

      hoare.
      erewrite <- mem_pred_absorb_nop with (hm:= d)(a:= a); eauto.
      unfold cachepred at 3; simpl; eauto.
      rewrite MapFacts.add_eq_o; eauto; simpl.
      erewrite ptsto_subset_pimpl.
      eassign l.
      simpl; cancel; eauto.
      unfold ptsto_subset; cancel.
      apply mem_pred_pimpl_except; intros.
      unfold cachepred.
      rewrite MapFacts.add_neq_o; eauto.
      unfold vsmerge; simpl.
      eapply incl_cons; eauto.
      apply incl_refl.

      unfold size_valid in *; simpl; auto.
      repeat rewrite map_add_dup_cardinal; auto.      
      destruct (Nat.eq_dec a a0); subst; try congruence.
      apply add_neq_in_iff in H5; eauto.
      unfold addr_clean.
      right; eexists; apply add_eq_o; eauto.
      apply add_in_iff; intuition.
      eexists; eapply hashmap_subset_trans; eauto.

      rewrite <- H1.
      cancel; eauto.
      erewrite <- mem_pred_absorb_nop with (hm:= d)(a:= a); eauto.
      unfold cachepred at 3; simpl; eauto; cleanup.
      cancel; eauto; cancel; eauto.
    }

    unfold addr_clean; hoare.
  }
  unfold addr_clean; hoare.
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
  step.
  apply H9; apply in_find_iff; intuition; congruence.
  step_r.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  rewrite cardinal_1 in *; cleanup; rewrite Heql in *; simpl in *; omega.
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
  
  rewrite <- H1; unfold rep; cancel; eauto.
  (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
  unfold cachepred at 3; rewrite Heqo;
  cancel; eauto.
  eexists; eapply hashmap_subset_trans; eauto.
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
    unfold synrep.
    rewrite pimpl_l_and.
    eassign cs; eauto.
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
      exists cs', rep cs' d0 bm''
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
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

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
      + rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

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
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
    Unshelve. all: eauto.
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
      exists cs', rep cs' d0 bm''
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
    eexists; eapply hashmap_subset_trans; eauto.
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
    apply sync_invariant_arrayS.
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
      exists cs, rep cs d bm''
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
    cancel; eauto.
    rewrite <- H1; cancel; eauto.
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
        rep cs d' bm' * [[ bm' = bm ]] *
        [[ (F * a |+> (v, vsmerge v0))%pred d' ]]
    XCRASH:bm'', hm'',
      exists cs' d', rep cs' d' bm'' *
      [[  (F * a |+> (v, vsmerge v0))%pred d' ]]
    >} write a h cs.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel; auto.
    cancel.
    rewrite <- H1.
    eassign ((exists cs' : cachestate, rep cs' d bm'')%pred).
    cancel; eauto.
    rewrite crash_xform_exists_comm.
    cancel.
    
    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.
    edestruct ptsto_subset_valid' with (a := a); eauto; intuition.
    edestruct possible_crash_sel_exis; eauto; intuition.
    rewrite mem_pred_extract with (a := a) by eauto.

    cancel; xform_normr; cleanup.
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

    rewrite <- crash_xform_rep_r.
    cancel.
    eapply pimpl_trans2.
    unfold rep; cancel; eauto.
    eapply mem_pred_absorb_nop with (a := a).
    eauto.
    eapply ptsto_subset_upd; eauto.
    2: eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    2: apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.
  Qed.

  Hint Extern 1 ({{_ | _}} Bind (init_recover _) _) => apply init_recover_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (init_load _) _) => apply init_load_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (begin_sync _) _) => apply begin_sync_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (end_sync _) _) => apply end_sync_ok : prog.

  
  Theorem read_array_ok :
    forall a i cs pr,
    {< d F vs,
    PERM: pr
    PRE:bm, hm,
        rep cs d bm *
        [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
        [[ i < length vs ]]
    POST:bm', hm', RET:^(cs, h)
        rep cs d bm' * [[ bm' = upd bm h (fst (selN vs i ((Public, $0), nil)))]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm''
    >} read_array a i cs.
  Proof.
    unfold read_array.
    hoare.
    rewrite isolateN_fwd with (i:=i) by auto.
    eassign (F * arrayS a (firstn i vs) *  arrayS (a + i + 1) (skipn (S i) vs))%pred.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto. 
  Qed.



  Theorem sync_invariant_arrayN_subset : forall vs a,
    sync_invariant (arrayN ptsto_subset a vs).
  Proof.
    induction vs; simpl; auto.
  Qed.

  Lemma arrayN_subset_oob': forall l a i m,
    i >= length l
    -> arrayN ptsto_subset a l m
    -> m (a + i) = None.
  Proof.
    induction l; intros; auto; simpl in *.
    destruct (eq_nat_dec i 0); auto.
    subst; simpl in *; omega.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto_subset in H2.
    destruct_lift H2.
    unfold ptsto in H1; destruct H1.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
    destruct (m1 (a0 + i)) eqn:?.
    contradict Heqo.
    rewrite H2; try congruence.
    omega.
    apply H3.
    omega.
    auto.
  Qed.

  Lemma arrayN_subset_oob: forall l i m,
    i >= length l
    -> arrayN ptsto_subset 0 l m
    -> m i = None.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_subset_oob'; eauto.
  Qed.

  Lemma arrayN_selN_subset : forall F a st l m def,
    (F * arrayN ptsto_subset st l)%pred m ->
    a >= st ->
    a < st + length l ->
    let vs0 := (selN l (a - st) def) in
    exists vs, m a = Some vs /\ fst vs = fst vs0 /\ incl (snd vs) (snd vs0).
  Proof.
    cbn; intros.
    rewrite arrayN_isolate with (i := a - st) in H by omega.
    unfold ptsto_subset at 2 in H; destruct_lift H; simpl in *.
    eexists; split; try split.
    eapply ptsto_valid.
    pred_apply; replace (st + (a - st)) with a by omega.
    eassign ((fst (selN l (a - st) def), dummy)).
    cancel.
    simpl; auto.
    auto.
  Qed.

  Lemma arrayN_subset_memupd : forall F l a i v vs vs' m,
    (F * arrayN ptsto_subset a l)%pred m ->
    incl vs' vs ->
    i < length l ->
    (F * arrayN ptsto_subset a (updN l i (v, vs)))%pred (Mem.upd m (a + i) (v, vs')).
  Proof.
    intros.
    rewrite arrayN_isolate with (i := i) in H by auto.
    unfold ptsto_subset at 2 in H; destruct_lift H.
    setoid_rewrite sep_star_comm in H.
    apply sep_star_assoc in H.
    apply ptsto_upd with (v := (v, vs')) in H.
    pred_apply' H.
    setoid_rewrite arrayN_isolate with (i := i) at 3.
    unfold ptsto_subset at 4.
    rewrite selN_updN_eq by auto.
    cancel.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    cancel.
    rewrite length_updN; auto.
    Grab Existential Variables. all: apply (v, nil).
  Qed.

(*  
  Lemma crash_xform_arrayN_subset: forall l st,
    crash_xform (arrayN ptsto_subset st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN ptsto_subset st (synced_list l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto. auto.

    xform.
    rewrite IHl.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset, synced_list.
    cancel; [ instantiate (1 := v' :: l') | .. ]; simpl; auto; try cancel;
    destruct i; simpl; auto;
    destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_subset_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN ptsto_subset st (synced_list l) =p=>
     crash_xform (arrayN ptsto_subset st l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_subset_r with (v := a) by (apply H1'; omega).
      rewrite ptsto_subset_pimpl_ptsto.
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. omega.
  Qed.

  Hint Resolve incl_refl.

  Lemma crash_xform_synced_arrayN_subset: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN ptsto_subset st l) =p=> arrayN ptsto_subset st l.
  Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
    cancel.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H0.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma crash_xform_arrayN_subset_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (List.combine l (repeat nil (length l)))) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_subset_synced: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (synced_list l)) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

*)










  Definition vsupd vs i v :=  updN vs i (v, vsmerge (selN vs i ((Public, $0), nil))).
  Definition vssync (vs: list valuset) i :=  updN vs i (fst (selN vs i ((Public, $0), nil)), nil).
  
  Lemma write_array_xcrash_ok : forall cs d bm F a i v vs,
    (F * arrayN ptsto_subset a vs)%pred d ->
    i < length vs ->
    crash_xform (rep cs d bm) =p=>
    crash_xform (exists cs' d', rep cs' d' bm *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]).
  Proof.
    intros.
    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.

    edestruct arrayN_selN_subset with (a := a + i); eauto; try omega; intuition.
    replace (a + i - a) with i in * by omega.
    edestruct possible_crash_sel_exis; eauto; intuition.
    
    xcrash.
    2: apply arrayN_subset_memupd; eauto.
    rewrite <- crash_xform_rep_r; eauto.
    unfold rep; cancel; eauto.    
    eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.

     2: apply arrayN_subset_memupd; eauto.
    rewrite <- crash_xform_rep_r; eauto.
    unfold rep; cancel; eauto.    
    eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.    
  Qed.

  Theorem write_array_ok :
    forall a i h cs pr,
    {< d F v vs,
    PERM: pr
    PRE: bm, hm,
         rep cs d bm * [[ bm h = Some v ]] *
         [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
         [[ i < length vs ]]
    POST:bm', hm', RET:cs
      exists d', rep cs d' bm' * [[ bm' = bm ]] *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]
    XCRASH:bm'', hm'', exists cs' d',
      rep cs' d' bm'' *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]
    >} write_array a i h cs.
  Proof.
    unfold write_array, vsupd.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.
    eauto.

    rewrite isolateN_fwd with (i:=i) by auto.
    eassign (arrayS a (firstn i vs) * arrayS (a + i + 1) (skipn (S i) vs) * F)%pred; cancel.
    
    hoare.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto.

    xcrash.
    rewrite <- H1.
    2:apply write_array_xcrash_ok; eauto.
    cancel; eauto.
  Qed.


  Theorem sync_array_ok :
    forall a i cs pr,
    {< d0 d (F : rawpred) vs,
    PERM: pr
    PRE:bm, hm,
      synrep cs d0 d bm *
      [[ (F * arrayN ptsto_subset a vs)%pred d ]] * 
      [[ i < length vs /\ sync_invariant F ]]
    POST:bm', hm', RET:cs exists d',
      synrep cs d0 d' bm' * [[ bm' = bm ]] *
      [[ (F * arrayN ptsto_subset a (vssync vs i))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} sync_array a i cs.
  Proof.
    unfold sync_array, vssync.
    safestep.
    4: eauto.
    cancel.
    pred_apply;
    rewrite isolateN_fwd with (i:=i) by auto.
    eassign (arrayS a (firstn i vs) * arrayS (a + i + 1) (skipn (S i) vs) * F)%pred; cancel.
    repeat apply sync_invariant_sep_star; eauto; apply sync_invariant_arrayS.
  
    hoare.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
     eexists; eapply hashmap_subset_trans; eauto.

    xcrash.
    rewrite <- H1.
    cancel; eauto.
  Qed.

  Hint Extern 1 ({{_ | _}} Bind (write _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (read_array _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (write_array _ _ _ _) _) => apply write_array_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (sync_array _ _ _) _) => apply sync_array_ok : prog.


  Definition read_range A a nr (vfold : A -> valu -> A) a0 cs :=
    let^ (cs, r) <- ForN i < nr
    Ghost [ F crash d vs ]
    Loopvar [ cs pf ]
    Invariant
      rep cs d * [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) a0 ]]
    OnCrash  crash
    Begin
      let^ (cs, v) <- read_array a i cs;
      Ret ^(cs, vfold pf v)
    Rof ^(cs, a0);
    Ret ^(cs, r).


  Definition write_range a l cs :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd_range vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- write_array a i (selN l i $0) cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition sync_range a nr cs :=
    let^ (cs) <- ForN i < nr
    Ghost [ F crash vs d0 ]
    Loopvar [ cs ]
    Invariant
      exists d', synrep cs d0 d' *
      [[ (F * arrayN ptsto_subset a (vssync_range vs i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition write_vecs a l cs :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      let v := selN l i (0, $0) in
      cs <- write_array a (fst v) (snd v) cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition sync_vecs a l cs :=
    let^ (cs) <- ForEach i irest l
    Ghost [ F crash vs d0 ]
    Loopvar [ cs ]
    Invariant
      exists d' iprefix, synrep cs d0 d' *
      [[ iprefix ++ irest = l ]] *
      [[ (F * arrayN ptsto_subset a (vssync_vecs vs iprefix))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition sync_vecs_now a l cs :=
    cs <- begin_sync cs;
    cs <- sync_vecs a l cs;
    cs <- end_sync cs;
    Ret cs.

  Definition sync_all cs :=
    cs <- sync_vecs_now 0 (map fst (Map.elements (CSMap cs))) cs;
    Ret cs.

  Hint Extern 0 (okToUnify (arrayN ?pts ?a _) (arrayN ?pts ?a _)) => constructor : okToUnify.
