Require Export SecurityBasic2.
Require Export Cache.
Require Export MapUtils.
Require Export ListPred.
Require Export MemPred.


Set Implicit Arguments.

Import AddrMap.
Import BUFCACHE.

Open Scope pred_scope.
    
(* Definition deterministic {AT AEQ V} (F: @pred AT AEQ V) :=
forall m m', F m -> F m' -> m = m'. *)

Lemma mem_disjoint_ptsto_mem_union_eq:
  forall AT AEQ V (m0 m1 m2 m4: @mem AT AEQ V) a vs vs',
  mem_disjoint m1 m2
  -> mem_disjoint m0 m4
  -> (a |-> vs) m2
  -> (a |-> vs') m4
  -> mem_union m1 m2 = mem_union m0 m4
  -> m1 = m0.
Proof.
  intros; extensionality x.
  destruct (AEQ a x); subst.
  Search mem_disjoint None.
  rewrite mem_disjoint_comm in H.
  rewrite mem_disjoint_comm in H0.
  erewrite mem_disjoint_either; eauto.
  erewrite mem_disjoint_either; eauto.
  eapply ptsto_valid'; pred_apply; cancel.
  eapply ptsto_valid'; pred_apply; cancel.
  
  Search mem_union mem_disjoint.
  erewrite <- mem_union_sel_l; eauto.
  symmetry; erewrite <- mem_union_sel_l; eauto.
  rewrite H3; auto.
  destruct H2; eauto.
  destruct H1; eauto.
Qed.




Theorem writeback_secure:
  forall a cs d F vs,
  @prog_secure _ addr_eq_dec _ _ 
  (fun m m' => (rep cs d * [[ (F * diskIs m')%pred m]])%pred m)
  (fun m m' => (exists cs', rep cs' d * [[ (F * diskIs m')%pred m]])%pred m)
  (writeback a cs) (a|-> vs) (match Map.find a (CSMap cs) with
                                              | Some (v, true) => a|->(v, vsmerge vs)
                                              | _ => a|->vs
                                              end).
Proof.
  unfold writeback; intuition.
  destruct (Map.find a (CSMap cs)) eqn:D; eauto.
  
  Focus 2.
      eapply world_impl_secure; eauto.
      intros. apply H.
      simpl; intros.
      eexists; eauto.

  destruct p; eauto.
  destruct b0; eauto.
  
  Focus 2.
    eapply world_impl_secure; eauto.
    intros; apply H.
    simpl; intros.
    eexists; eauto.
  

  eapply bind_secure; intros; eauto.
  -
    eapply world_impl_secure. 
    3: eauto.
    
    + instantiate (1:= (fun m => ([[ rep cs d (insert m a (a0,b))]] * F)%pred m)).
    
    simpl; intros.
    destruct_lift H.
    pose proof H as Hs.
    unfold rep in H.
    destruct_lift H.
    eapply addr_valid_mem_valid in H5 as Hz. deex.
    2: eauto.
    eapply mem_pred_extract in H.
    2: eauto.
    destruct vs.
    unfold cachepred in H at 2.
    rewrite D in H; simpl in H.
    
    unfold ptsto_subset in H; destruct_lift H.
    sep_unfold H.
    rewrite (diskIs_pred _ H0) in H2.
    sep_unfold H2.
    eapply mem_disjoint_ptsto_mem_union_eq in H as Hx; eauto; subst.
    eapply mem_disjoint_union_cancel in H4 as Hy; eauto; subst.
    rewrite diskIs_ptsto_eq; eauto.
    apply sep_star_mem_union; eauto.
    pred_apply; cancel.
    replace (insert m1 a (a0, b)) with (mem_union m1 m3); auto.
    extensionality x.
    destruct (addr_eq_dec a x); subst.
    rewrite insert_eq.
    rewrite mem_union_sel_r; eauto.
    destruct H12; auto.
    apply mem_disjoint_comm in H2.
    eapply mem_disjoint_either; eauto.
    destruct H12; eauto.
    apply (a0, b).
    apply mem_disjoint_comm in H2.
    eapply mem_disjoint_either; eauto.
    destruct H12; eauto.
    auto.
    rewrite insert_ne; auto.
    rewrite mem_union_sel_l; eauto.
    destruct H12; eauto.
    
    + eauto.

  - eapply world_impl_secure; eauto.
    + simpl; intros; eauto.
        apply H0.
    + simpl; intros.
        unfold rep.
        sep_unfold H3.
        apply emp_star in H7; destruct_lift H7.
        apply emp_empty_mem_only in H6; subst.
        repeat rewrite mem_union_empty_mem in *.
        clear H5.
        unfold rep in *.
        destruct_lift H9.
        eapply addr_valid_mem_valid in H9 as Hy; eauto; deex.
        eapply mem_pred_extract with (a:= a) in H5; eauto.
        destruct vs.
        unfold cachepred at 2 in H5.
        rewrite D in H5.
        simpl in H5.
        unfold ptsto_subset in H5; destruct_lift H5.
        
        exists {| CSMap := Map.add a (w0, false) (CSMap cs);
                  CSMaxCount := CSMaxCount cs;
                  CSCount := CSCount cs;
                  CSEvict := CSEvict cs |}; simpl.
                  
        apply sep_star_lift_apply'.
        apply sep_star_comm; apply sep_star_lift_apply'; auto.
        eapply mem_pred_cachepred_add_absorb_clean; eauto.
        apply sep_star_mem_union; eauto.
        Search mem_except ptsto.
        apply sep_star_comm in H5; apply ptsto_mem_except in H5.
        rewrite mem_except_insert in H5.
        rewrite mem_except_none with (m:= m4) in H5; auto.
        eapply mem_disjoint_either with (m1:= m3); eauto.
        rewrite mem_disjoint_comm; auto.
        destruct H4; eauto.
        
        rewrite mem_disjoint_comm in H3; unfold ptsto_subset; pred_apply; cancel.
        unfold vsmerge; simpl.
        apply ptsto_valid' in H5.
        rewrite insert_eq in H5; auto.
        inversion H5.
        apply incl_cons; auto.
        eapply mem_disjoint_either; eauto.
        destruct H4; eauto.
        split.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
        apply sep_star_mem_union; eauto.
Qed.
