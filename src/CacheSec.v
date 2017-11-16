Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred.
Require Import WordAuto.
Require Import Omega.
Require Import AsyncDisk.
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

Theorem h_writeback_ok :
  forall a cs,
    {< d bm',
     PERM: None
     PRE:
       fun bm => rep cs d bm * [[ bm = bm' ]]
     POST:
       fun bm => RET:cs'
         rep cs' d bm * [[ bm = bm' ]] *
          [[ addr_clean (HCSMap cs') a ]] * 
          [[ In a (HCSMap cs) -> In a (HCSMap cs')]]
      >} h_writeback a cs.
Proof.
  
  unfold h_writeback, rep, addr_valid; intros; cleanup.
  destruct (find a (HCSMap cs)) eqn:D.
  {
    destruct p.
    destruct b.
    {
      prestep. (* step not smart enough *)
      unfold pimpl; intros m Hp; destruct_lift Hp.
      assert (A: In a (HCSMap cs)). {        
        apply MapFacts.in_find_iff.
        intuition; congruence.
      }
      specialize (H6 _ A) as Hx.
      destruct (dummy a) eqn: D0; try congruence; clear Hx.
      rewrite mem_pred_extract' in H; eauto.
      unfold mem_pred_one, cachepred in H; simpl in H.
      rewrite D in H.
      destruct_lift H.

      
      pred_apply; norm.
      unfold stars; simpl; cancel.
      Existential 6 := dummy1.
      cancel.
      intuition; eauto.

      step.
      step.
      erewrite <- mem_pred_absorb_nop with (hm:= dummy)(a:= a).
      unfold cachepred; simpl; eauto.
      rewrite MapFacts.add_eq_o; eauto; simpl.
      cancel; eauto.
      unfold pimpl; intros; eauto.
      admit. (* Cumbersome *)

      auto.
      unfold size_valid in *; simpl; auto.
      repeat rewrite map_add_dup_cardinal; auto.      
      destruct (Nat.eq_dec a a0); subst; try congruence.
      apply add_neq_in_iff in H0; auto.
      eauto.
      unfold addr_clean.
      right; eexists; apply add_eq_o; eauto.
      apply add_in_iff; intuition.
    }
    hoare.
    unfold addr_clean; right; eexists; eauto.
  }
  hoare.
  unfold addr_clean; left; auto.
Admitted.


Hint Extern 1 (corr2 _ _ (Bind (h_writeback _ _) _)) => apply h_writeback_ok : prog.


Theorem h_evict'_ok :
  forall a cs,
    {< d bm',
     PERM: None
     PRE:
      fun bm => rep cs d bm * [[ bm = bm' ]] *
          [[ addr_clean (HCSMap cs) a]]
    POST:
      fun bm => RET:cs'
      rep cs' d bm * [[ bm = bm' ]] *
      [[ ~ In a (HCSMap cs') ]] *
      [[ In a (HCSMap cs) -> cardinal (HCSMap cs') < HCSMaxCount cs' ]]
    >} h_evict' a cs.
Proof.
  unfold h_evict', rep; intros; cleanup.
  destruct (find a (HCSMap cs)) eqn:D.
  {
    hoare.
    eapply addr_valid_ptsto_exists in H6 as Hx;
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
    eapply in_find_iff in H; congruence.
    apply addr_valid_remove; auto.
    eapply remove_1; eauto.
    eapply size_valid_remove_cardinal_ok; eauto.
  }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (h_evict' _ _) _)) => apply h_evict'_ok : prog.


Theorem h_evict_ok :
  forall a cs,
    {< d bm',
     PERM: None
     PRE:
      fun bm => rep cs d bm' * [[ bm = bm' ]]
    POST:
      fun bm => RET:cs'
      rep cs' d bm * [[ bm = bm' ]] *
      [[ ~ In a (HCSMap cs') ]] *
      [[ In a (HCSMap cs) -> cardinal (HCSMap cs') < HCSMaxCount cs' ]]
    >} h_evict a cs.
  Proof.
    unfold h_evict; intros; hoare.
  Qed.

  Hint Extern 1 (corr2 _ _ (Bind (h_evict _ _) _)) => apply h_evict_ok : prog.



  Theorem h_maybe_evict_ok :
    forall cs,
  {< d bm',
    PERM: None                          
    PRE: 
      fun bm => rep cs d bm * [[ bm = bm' ]]
    POST: fun bm =>
      RET:cs'
          rep cs' d bm * [[ bm = bm' ]] *
          [[ cardinal (HCSMap cs') < HCSMaxCount cs' ]]
    >} h_maybe_evict cs.
  Proof.
    unfold h_maybe_evict; intros.
    step.
    unfold rep, size_valid in *; step.
    step.
    apply H4; apply in_find_iff; intuition; congruence.
    unfold rep, size_valid in *; step.
    rewrite Map.cardinal_1, Heql; simpl; omega.

    step.
    apply find_elements_hd in Heql.
    apply H4; apply in_find_iff; intuition; congruence.
  Qed.

  Hint Extern 1 (corr2 _ _ (Bind (h_maybe_evict _) _)) => apply h_maybe_evict_ok : prog.


Theorem h_read_ok :
  forall cs a,
  {< d F tb bm',
    PERM: None                 
    PRE: fun bm =>
      rep cs d bm * [[ bm = bm' ]] *
      [[ (sep_star (AEQ:= addr_eq_dec) F (a |-> tb))%pred d ]]
    POST: fun bm =>
      RET:csr
      let cs' := fst csr in
      let r := snd csr in
      rep cs' d bm * [[ bm = upd bm' r tb ]]
    >} h_read a cs.
Proof.
  unfold h_read, rep; intros.
  safestep; eauto.
  unfold rep; cancel.
  Existential 1:= d.
  cancel; auto.
  apply H6.
  apply ptsto_valid' in H0.

  prestep; unfold rep; norml; unfold stars; simpl;
  eauto; intuition simpl in *;
  erewrite mem_pred_extract with (a := a) at 1 by eauto;  
  unfold cachepred at 2; rewrite Heqo; eauto.

    (* found in cache *)
  - destruct b; simpl; cancel;
    (step; [ | cleanup; symmetry; eapply upd_nop; eauto]);
    rewrite sep_star_comm;
    (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
    unfold cachepred at 3; rewrite Heqo;
    cancel; eauto.
    
    (* not found *)
  - cancel.
    Existential 1 := F_.
    cancel.
    hoare.
    rewrite sep_star_comm;
    eapply mem_pred_cachepred_add_absorb_clean; eauto.
    apply size_valid_add; auto.
    eapply addr_valid_add; eauto.
  Qed.

Hint Extern 1 (corr2 _ _ (Bind (h_read _ _) _)) => apply h_read_ok : prog.

Theorem h_write_ok:
  forall cs a h,
    {< d F bm' tb0 tb,
     PERM: None
     PRE: fun bm =>
            rep cs d bm * [[ bm = bm' ]] *
            [[ bm h = Some tb ]] *
            [[ (F * a |-> tb0)%pred d ]]
    POST: fun bm => RET:cs'
      exists d',
        rep cs' d' bm * [[ bm = bm' ]] *
        [[ (sep_star (AEQ:= addr_eq_dec) F  (a |-> tb))%pred d' ]]
    >} h_write a h cs.
  Proof.
    unfold h_write, rep; intros.
    safestep; eauto.
    unfold rep; cancel.
    Existential 1:= d.
    cancel; auto.
    apply H7.
    apply ptsto_valid' in H2 as Hx.

    step;
    (step; [ | admit | admit | eapply ptsto_upd'; eauto]);
    unfold rep;
    erewrite mem_pred_extract with (a := a) at 1 by eauto;
    unfold cachepred at 2; rewrite Heqo; eauto; cancel;
    [ destruct p_2 | ];
    (rewrite mem_pred_pimpl_except;
    [ | intros; apply cachepred_add_invariant; eassumption]);
    rewrite <- mem_pred_absorb with (hm := d) (a := a);
    unfold cachepred at 3;
    rewrite MapFacts.add_eq_o by reflexivity; safecancel;
    eauto.
Admitted.    

Hint Extern 1 (corr2 _ _ (Bind (h_write _ _ _) _)) => apply h_write_ok : prog.