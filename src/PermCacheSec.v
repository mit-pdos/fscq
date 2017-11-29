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
    forall a cs,
    {< vs0,
    PERM: None                       
    PRE:bm
        a |+> vs0 * [[ forall hb, Map.find a (CSMap cs) = Some hb -> exists v, bm (fst hb) = Some v ]]
    POST:bm' RET:cs'
      [[ bm' = bm ]] *
      exists h v,
      ([[ Map.find a (CSMap cs) = Some (h, true) /\ bm' h = Some v /\
          cs' = mk_cs (Map.add a (h, false) (CSMap cs))
                      (CSMaxCount cs) (CSCount cs) (CSEvict cs) ]] *
         a |+> (v, vsmerge vs0)) \/
      ([[ (Map.find a (CSMap cs) = None \/
           Map.find a (CSMap cs) = Some (h, false)) /\ cs' = cs ]] * a |+> vs0) 
    CRASH:
      a |+> vs0 \/ (exists v, a |+> (v, vsmerge vs0))
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
    eassign (emp (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)).
    cancel.
    intuition; eauto.
    hoare.
    cancel.
    cancel.

    norml.
    edestruct H5; eauto; cleanup; simpl in *.
    unfold stars; norm.
    unfold stars; cancel.
    norm.
    unfold stars; cancel.
    intuition; eauto.
    intuition.
    intuition; eauto.
    hoare.
    cancel.
    cancel.

    norm.
    unfold stars; cancel.
    rewrite sep_star_comm; eauto.
    intuition; eauto.
    hoare.
    cancel.
    cancel.
  Qed.

Theorem writeback_ok :
  forall a cs,
    {< d,
     PERM: None
     PRE: bm
       rep cs d bm
     POST: bm'
       RET:cs'
         rep cs' d bm' * [[ bm' = bm ]] *
          [[ addr_clean (CSMap cs') a ]] * 
          [[ In a (CSMap cs) -> In a (CSMap cs')]]
     CRASH:
       exists cs', rep cs' d bm
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
      unfold mem_pred_one, cachepred in H; simpl in H.
      rewrite D in H.
      destruct_lift H.

      pred_apply; norm.
      unfold stars; simpl; cancel.
      Existential 3 := dummy.
      Existential 5 := (dummy1, l).
      cancel.
      intuition; eauto.

      step.
      step; eauto.
      erewrite <- mem_pred_absorb_nop with (hm:= dummy0)(a:= a); eauto.
      unfold cachepred; simpl; eauto.
      rewrite MapFacts.add_eq_o; eauto; simpl.
      erewrite ptsto_subset_pimpl.
      Existential 10:= l.
      simpl; cancel; eauto.
      apply mem_pred_pimpl_except; intros.
      rewrite MapFacts.add_neq_o; auto.
      unfold vsmerge; simpl.
      eapply incl_cons; eauto.
      apply incl_refl.

      unfold size_valid in *; simpl; auto.
      repeat rewrite map_add_dup_cardinal; auto.      
      destruct (Nat.eq_dec a a0); subst; try congruence.
      apply add_neq_in_iff in H0; eauto.
      unfold addr_clean.
      right; eexists; apply add_eq_o; eauto.
      apply add_in_iff; intuition.

      { (* Crash 1 *)
        unfold pimpl; intros; apply H2;
        pred_apply; cancel.
        Existential 4 := {| CSMap := add a (h, false) (CSMap cs);
                            CSMaxCount := CSMaxCount cs;
                            CSCount := CSCount cs;
                            CSEvict := CSEvict cs |}.
        simpl; erewrite <- mem_pred_absorb_nop with (hm:= dummy0)(a:= a); eauto.
        unfold cachepred; simpl; eauto.
        rewrite MapFacts.add_eq_o; eauto; simpl.
        erewrite ptsto_subset_pimpl.
        Existential 7:= l.
        simpl; cancel; eauto.
        apply mem_pred_pimpl_except; intros.
        rewrite MapFacts.add_neq_o; auto.
        unfold vsmerge; simpl.
        eapply incl_cons; eauto.
        apply incl_refl.

        unfold size_valid in *; simpl; auto.
        repeat rewrite map_add_dup_cardinal; auto.      
        simpl in *; destruct (Nat.eq_dec a a0); subst; try congruence.
        apply add_neq_in_iff in H1; eauto.
      }
      {
        apply H2;
        pred_apply; cancel; eauto.
        erewrite <- mem_pred_absorb_nop with (hm:= dummy0)(a:= a); eauto.
        unfold cachepred; simpl; eauto.
        rewrite D; cancel; eauto.
      }
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
  forall a cs,
    {< d ,
     PERM: None
     PRE: bm
      rep cs d bm
    POST: bm'
      RET:cs'
        rep cs' d bm' * [[ bm' = bm ]] *
        [[ ~ In a (CSMap cs') ]] *
        [[ In a (CSMap cs) -> cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH:
       exists cs', rep cs' d bm
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
    }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (evict _ _) _)) => apply evict_ok : prog.



Theorem maybe_evict_ok :
  forall cs,
  {< d,
    PERM: None                          
    PRE: bm
      rep cs d bm
    POST: bm' RET:cs'
      rep cs' d bm'* [[ bm' = bm ]] *
      [[ cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH:
        exists cs', rep cs' d bm
    >} maybe_evict cs.
Proof.
  unfold maybe_evict; step; step_r.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  apply H8; apply in_find_iff; intuition; congruence.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  rewrite cardinal_1 in *; cleanup; rewrite Heql in *; simpl in *; omega.
  apply find_elements_hd in Heql;
  apply H8; apply in_find_iff; intuition; congruence.  
Qed.

Hint Extern 1 (corr2 _ _ (Bind (maybe_evict _) _)) => apply maybe_evict_ok : prog.


Theorem read_ok :
  forall cs a,
  {< d F tbs,
    PERM: None                 
    PRE: bm
      rep cs d bm *
      [[ (sep_star (AEQ:= addr_eq_dec) F (a |+> tbs))%pred d ]]
    POST: bm' (RET:^(cs', r)
      rep cs' d bm' * [[ bm' = upd bm r (fst tbs) ]])%pred
    CRASH:
      exists cs', rep cs' d bm
  >} read a cs.
Proof.
  unfold read; intros.
  safestep; eauto.
  eapply ptsto_subset_valid' in H4 as Hx; cleanup; simpl in *.
  repeat destruct_branch.
  eapply pimpl_ok2. eapply ret_secure. safecancel; eauto.
  step_r.
  unfold rep in *; erewrite mem_pred_extract with (a := a) in H5; eauto; 
  unfold cachepred at 2 in H5; rewrite Heqo in H5.
  destruct b; destruct_lift H5;
  symmetry; eapply upd_nop; eauto.
  cancel; eauto.  

  safestep.
  unfold rep in *; erewrite mem_pred_extract with (a := a); eauto; 
  unfold cachepred at 2; rewrite Heqo.
  eassign (t0, x).
  eassign F_.
  eassign ([[ size_valid r_ ]] *
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
  (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
  unfold cachepred at 3; rewrite Heqo;
  cancel; eauto.
  cancel.
  unfold rep; cancel; eauto.
  (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
  unfold cachepred at 3; rewrite Heqo;
  cancel; eauto.
Qed.

Hint Extern 1 (corr2 _ _ (Bind (read _ _) _)) => apply read_ok : prog.

Theorem write_ok:
  forall cs a h,
    {< d F tb0 tb,
     PERM: None
     PRE: bm
            rep cs d bm *
            [[ bm h = Some tb ]] *
            [[ (F * a |+> tb0)%pred d ]]
    POST: bm' RET:cs'
      exists d',
        rep cs' d' bm' * [[ bm' = bm ]] *
        [[ (sep_star (AEQ:= addr_eq_dec) F  (a |+> (tb, vsmerge tb0)))%pred d' ]]
    CRASH:
      exists cs', rep cs' d bm    
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
      Existential 7:= (tb, vsmerge(t0, l)).
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
      Existential 4:= (tb, vsmerge(t0, l)).
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      simpl; auto.
      simpl; auto.

      eapply size_valid_add; eauto.
      eapply addr_valid_upd_add; eauto.
    }
    eapply ptsto_subset_upd; eauto; apply incl_refl.
Qed.    

Hint Extern 1 (corr2 _ _ (Bind (write _ _ _) _)) => apply write_ok : prog.

Theorem begin_sync_ok :
  forall cs,
    {< d F,
     PERM: None   
     PRE:bm
       rep cs d bm * [[ F d /\ sync_invariant F ]]
     POST:bm' RET:cs
       exists d',
         synrep cs d d' bm * [[ bm' = bm ]] * [[ F d' ]]
     CRASH:
       exists cs', rep cs' d bm
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
  forall cs,
   {< d0 d,
    PERM: None
    PRE:bm
      synrep cs d0 d bm
    POST:bm' RET:cs
      rep cs d bm' * [[ bm' = bm ]]
    CRASH:
      exists cs', rep cs' d0 bm
    >} end_sync cs.
  Proof.
    unfold end_sync; intros.
    safestep.
    eassign (fun x => synrep cs (fst x) (fst (snd x)) (snd (snd x))).
    eassign F_.
    eassign (d0, (d, bm)).
    simpl; cancel; eauto.
    simpl; auto.
    auto.
    step.
    step.
    
    unfold rep, synrep, synrep', mem_pred, mem_pred_one; simpl.
    rewrite sync_xform_and_dist. rewrite pimpl_r_and.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    norml; unfold stars; simpl.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    cancel; auto.
    rewrite sync_xform_listpred_synpred_cachepred; auto.
    rewrite sync_xform_sync_invariant by auto.
    apply synrep_rep.
    simpl; cancel.
    apply synrep_rep.
  Qed.

  
  Theorem sync_ok' :
    forall cs a,
   {< d0 d (F F' : rawpred) v0 v',
    PERM: None   
    PRE:bm
      synrep cs d0 d bm * [[ sync_invariant F ]] *
      [[ (F * a |+> v0)%pred d ]] *
      [[ (F' * a |+> v')%pred d0 ]]
    POST:bm' RET:cs
      exists d,
        synrep cs d0 d bm' * [[ bm' = bm ]] *
        [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH:
      exists cs', rep cs' d0 bm
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
    - unfold ptsto_subset.
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
      eassign (t2, x3).
      eassign x3.
      cancel; simpl; eauto.
      simpl; apply incl_refl.
      auto.

      step.
      step.
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
        eassign (a1, old); simpl.
        cancel.
        simpl; auto.
        simpl; auto.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
        rewrite upd_eq; auto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        repeat cleanup.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        repeat cleanup.
        unfold ptsto_subset; cancel; eauto.
        repeat cleanup.
        eapply incl_tran; eauto.
        unfold vsmerge; simpl; auto.
        apply incl_cons; eauto.

    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl;
      intuition; repeat deex; try congruence; inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
        eapply incl_tran; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eapply incl_tran; eauto.

    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl;
      intuition; repeat deex; try congruence; inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
        eapply incl_tran; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eapply incl_tran; eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem sync_synrep_helper_1 : forall m cs d0 d a (F : @pred _ addr_eq_dec _) v,
    synrep cs d0 d m ->
    (F * a |+> v)%pred d ->
    exists (F0 : @pred _ addr_eq_dec _) v0,
    (F0 * a |+> v0)%pred d0.
  Proof.
    unfold synrep, rep, synrep', ptsto_subset; intros.
    case_eq (d0 a); intros.
    - destruct p.
      eapply any_sep_star_ptsto in H1.
      pred_apply.
      safecancel.
      eassign (w, l).
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

  Theorem sync_synrep_helper_2 : forall cs d0 d a (F : @pred _ addr_eq_dec _) v,
    (F * a |+> v)%pred d ->
    synrep cs d0 d =p=> synrep cs d0 d * exists (F0 : @pred _ addr_eq_dec _) v0,
    [[ (F0 * a |+> v0)%pred d0 ]].
  Proof.
    unfold pimpl; intros.
    eapply sync_synrep_helper_1 in H; eauto; repeat deex.
    pred_apply; cancel.
  Qed.


  Theorem sync_ok : forall cs a,
    {< d0 d (F : rawpred) v0,
    PRE:hm
      synrep cs d0 d *
      [[ (F * a |+> v0)%pred d ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:cs exists d,
      synrep cs d0 d *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH:hm'
      exists cs', rep cs' d0
    >} sync a cs.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply sync_ok'.
    intros; norml; unfold stars; simpl.
    rewrite sync_synrep_helper_2 by eauto.
    safecancel.
    eauto.
    step.
  Qed.


  Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (begin_sync _) _) => apply begin_sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (end_sync _) _) => apply end_sync_ok : prog.
