Require Import Mem List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Pred.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import ListPred. 
Require Import FunctionalExtensionality.
Require Import DestructPair DestructVarname.

Require Export CacheSec.


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
    match goal with | [H: ?x c= ?x |- _] => clear H end.
    erewrite <- extract_blocks_subset_trans; eauto.
    rewrite H14; auto.
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
    rewrite <- H16; eauto.
    eapply handles_valid_subset_trans; eauto.
    auto.

    rewrite vsupd_range_length; try omega.
    eapply Nat.lt_le_trans; eauto.
    rewrite firstn_length_l; try omega.
    eapply Nat.le_trans; [|eauto]; omega.
    erewrite extract_blocks_length; eauto; omega.

    step.
    prestep; unfold rep; cancel.
    erewrite firstn_S_selN_expand.
    setoid_rewrite <- vsupd_range_progress; auto.

    
    cancel.
    all: apply extract_blocks_length in H6; try rewrite H6; auto.
    solve_hashmap_subset.
    
    rewrite <- H1; cancel; eauto.
    solve_hashmap_subset.
    repeat xcrash_rewrite.
    setoid_rewrite vsupd_range_progress; auto.
    rewrite <- firstn_plusone_selN.

    apply vsupd_range_xcrash_firstn; auto.
    all: try rewrite H6; auto.

    step. step.
    rewrite firstn_oob; auto.
    rewrite H6; auto.
    solve_hashmap_subset.
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
    rewrite vssync_range_length; try omega.
    eapply Nat.lt_le_trans; eauto.
    eapply Nat.le_trans; [|eauto]; omega.

    all: auto.

    step. step.
    apply arrayN_unify.
    apply vssync_range_progress; try omega.
    eapply Nat.lt_le_trans; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel; eauto.
    solve_hashmap_subset.

    step. step.
    solve_hashmap_subset.
    rewrite <- H1; cancel; eauto.
    
    Unshelve.
    exact tt.
    unfold EqDec; apply handle_eq_dec.
    auto.
  Qed.
  
  Local Hint Resolve vsupd_vecs_length_ok.
  Local Hint Resolve vssync_vecs_length_ok.

  Lemma vsupd_vecs_mem_exis : forall F a l vs d,
    (F * arrayN ptsto_subset a vs)%pred d ->
    Forall (fun e => fst e < length vs) l ->
    exists d', (F * arrayN ptsto_subset a (vsupd_vecs vs l))%pred d' /\ mem_incl d d'.
  Proof.
    induction l using rev_ind; simpl; intros.
    exists d; split; auto.
    apply mem_incl_refl.
    rewrite vsupd_vecs_app; simpl.
    destruct x as [k v].
    apply forall_app_l in H0 as Hx; apply forall_app_r in H0 as Hy.
    apply Forall_inv in Hx; simpl in Hx.
    edestruct IHl; eauto; intuition.
    eexists; split; simpl in *.
    apply arrayN_subset_memupd; eauto.
    rewrite vsupd_vecs_length; auto.
    edestruct arrayN_selN_subset with (m := d) (a := a + k); eauto; try omega.
    intuition; replace (a + k - a) with k in * by omega.
    erewrite <- upd_nop with (m := d); eauto.
    apply mem_incl_upd; auto.

    destruct x0; simpl in *; subst.
    apply incl_cons.
    - apply in_cons.
      apply vsupd_vecs_selN_vsmerge_in.
      constructor; simpl; auto.
    - eapply incl_tran; eauto.
      apply vsupd_vecs_incl in H0.
      eapply forall2_selN in H0; eauto.
      rewrite vsupd_vecs_app in H0; simpl in H0; unfold vsupd in H0.
      rewrite selN_updN_eq in H0 by (rewrite vsupd_vecs_length; auto).
      eapply incl_tran; try eassumption.
      apply incl_tl; apply incl_refl.
    Unshelve. exact valuset0.
  Qed.


  Lemma vsupd_vecs_xcrash_firstn' : forall F a l n vs cs' d' bm',
    (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn n l)))%pred d' ->
    Forall (fun e => fst e < length vs) l ->
    crash_xform (rep cs' d' bm') =p=>
    crash_xform (exists cs d, rep cs d bm'* 
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs l))%pred d ]]).
  Proof.
    induction l; simpl; intros.
    rewrite firstn_nil in H; cbn in *.
    apply crash_xform_pimpl; cancel.

    destruct n; simpl in *.
    - inversion H0; subst; simpl in *.
      rewrite crash_xform_rep.
      unfold rep at 1; xform_norm.
      edestruct arrayN_selN_subset with (a := a + a0_1); eauto; try omega; intuition.

      edestruct possible_crash_sel_exis; eauto; intuition.
      rewrite mem_pred_extract with (a := a + a0_1) by eauto.
      rewrite <- vsupd_vecs_cons.
      edestruct vsupd_vecs_mem_exis with (l := (a0_1, a0_2) :: l); eauto; intuition.
      clear H11.
      cancel; xform_normr.
      rewrite <- crash_xform_rep_r.
      unfold rep; cancel.
      eapply pimpl_trans2.
      eapply mem_pred_absorb_nop with (a := a + a0_1).
      2: apply pimpl_refl.
      eauto.
      eauto.
      eauto.
      eauto.
      eapply possible_crash_incl_trans; eauto.
    - rewrite IHl; eauto.
      inversion H0; subst.
      rewrite vsupd_length; auto.
    Unshelve. exact valuset0.
  Qed.

  Lemma vsupd_vecs_xcrash_firstn : forall F a n l vs bm,
    Forall (fun e => fst e < length vs) l ->
    crash_xform (exists cs' d', rep cs' d' bm *
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn n l)))%pred d' ]]) =p=>
    crash_xform (exists cs d, rep cs d bm * 
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs l))%pred d ]]).
  Proof.
    intros.
    xform_norm.
    erewrite vsupd_vecs_xcrash_firstn'; eauto.
    xform_norm.
    do 2 (xform_normr; cancel).
  Qed.


  Theorem write_vecs_ok :
    forall a l cs pr,
    {< d F vs,
    PERM:pr                         
    PRE:bm, hm,
      rep cs d bm * [[ (F * arrayS a vs)%pred d ]] *
      [[ handles_valid_list bm l ]] *
      [[ Forall (fun e => fst e < length vs) l ]]
    POST:bm', hm', RET:cs                    
      exists d', rep cs d' bm' *
      [[ (F * arrayS a (vsupd_vecs vs (extract_blocks_list bm' l)))%pred d' ]]
    XCRASH:bm'', hm'',
      exists cs' d', rep cs' d' bm'' *
      [[ (F * arrayS a (vsupd_vecs vs (extract_blocks_list bm'' l)))%pred d' ]]
    >} write_vecs a l cs.
  Proof.
    unfold write_vecs.
    safestep.
    rewrite app_nil_l; auto.
    simpl; cancel.
    eauto.
    eauto.
    
    prestep; norml.
    unfold handles_valid_list, handles_valid in *;
    pose proof H7 as Hy.
    rewrite Forall_forall in Hy.
    edestruct Hy.
    apply in_map.
    apply in_app_middle; eauto.
    norm. cancel.
    intuition eauto.
    rewrite vsupd_vecs_length.
    pose proof H6 as Hx.
    apply forall_app_l in Hx.
    inversion Hx; simpl in *; eauto.
    step.
    prestep; unfold rep; cancel.
    apply cons_nil_app.
    unfold extract_blocks_list.
    repeat rewrite map_app.
    rewrite extract_blocks_app, combine_app.
    setoid_rewrite vsupd_vecs_app; simpl.
    erewrite block_mem_subset_extract_some; eauto.
    erewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
    rewrite map_app in H7;
    apply forall_app_r in H7; eauto.
    denote block_mem_subset as Hss; clear Hss;
      eapply handles_valid_subset_trans; eauto.
    solve_hashmap_subset.

    cancel; rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    xcrash_rewrite.
    erewrite <- vsupd_vecs_xcrash_firstn.
    simpl.
    eassign (S (length iprefix)).
    unfold extract_blocks_list.
    repeat rewrite map_app.
    rewrite extract_blocks_app, combine_app.
    simpl List.map.
    simpl extract_blocks.
    erewrite block_mem_subset_extract_some; eauto.
    simpl List.combine.
    rewrite <- cons_nil_app.
    rewrite firstn_app_l.
    rewrite firstn_oob.
    setoid_rewrite vsupd_vecs_app; simpl.
    xcrash.

    erewrite extract_blocks_subset_trans; eauto.
    rewrite map_app in H7;
    apply forall_app_r in H7; eauto.
    eapply handles_valid_subset_trans; eauto.
    rewrite app_length; simpl.
    rewrite combine_length_eq.
    rewrite map_length; omega.
    erewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
    eapply handles_valid_subset_trans; eauto.
    rewrite map_app in H7;
    apply forall_app_r in H7; eauto.
    eapply handles_valid_subset_trans; eauto.
    rewrite app_length; simpl.
    rewrite combine_length_eq.
    rewrite map_length; omega.
    erewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
    eapply handles_valid_subset_trans; eauto.
    rewrite map_app in H7;
    apply forall_app_r in H7; eauto.
    eapply handles_valid_subset_trans; eauto.
    erewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
    eapply handles_valid_subset_trans; eauto.
    rewrite map_app in H7;
    apply forall_app_r in H7; eauto.
    eapply handles_valid_subset_trans; eauto.  
    apply Forall_extract_blocks_list_length_le; auto.
    eapply handles_valid_subset_trans; eauto.

    step.
    step.
    rewrite app_nil_r; eauto.
    solve_hashmap_subset.
    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)).
    unfold false_pred; cancel.

    Unshelve.
    all: auto.
    exact tt.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem sync_vecs_ok :
    forall a l cs pr,
    {< d d0 F vs,
    PERM:pr   
    PRE:bm, hm,
      synrep cs d0 d bm *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l /\ sync_invariant F ]]
    POST:bm', hm', RET:cs
      exists d', synrep cs d0 d' bm' *
      [[ (F * arrayS a (vssync_vecs vs l))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} sync_vecs a l cs.
  Proof.
    unfold sync_vecs; intros.
    step.
    apply app_nil_l.
    pred_apply; cancel.
    safestep.
    eassign F_; cancel.
    eauto.
    rewrite vssync_vecs_length.
    eapply Forall_inv with (P := fun x => x < length vs).
    eauto using forall_app_l.
    auto.
    auto.
    step.
    step.
    apply cons_nil_app.
    rewrite vssync_vecs_app; cancel.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    step.
    step.
    rewrite app_nil_r. cancel.
    solve_hashmap_subset.
    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)).
    unfold false_pred; cancel.
    Unshelve.
    exact tt.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem sync_vecs_now_ok :
    forall a l cs pr,
    {< d F vs,
    PERM:pr   
    PRE:bm, hm,
      rep cs d bm *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l /\ sync_invariant F ]]
    POST:bm', hm', RET:cs
      exists d', rep cs d' bm' *
      [[ (F * arrayS a (vssync_vecs vs l))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm''
    >} sync_vecs_now a l cs.
  Proof.
    unfold sync_vecs_now; intros.
    step.
    eapply pimpl_ok2; monad_simpl. apply sync_vecs_ok.
    safecancel.
    eassign F_; cancel.
    all: eauto.
    safestep.
    eassign F_; cancel.
    all: eauto.
    step.
    step.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

  
  Hint Extern 1 ({{_|_}} Bind (read_range _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write_range _ _ _) _) => apply write_range_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (sync_range _ _ _) _) => apply sync_range_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write_vecs _ _ _) _) => apply write_vecs_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (sync_vecs _ _ _) _) => apply sync_vecs_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (sync_vecs_now _ _ _) _) => apply sync_vecs_now_ok : prog.