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
  rewrite mem_disjoint_comm in H.
  rewrite mem_disjoint_comm in H0.
  erewrite mem_disjoint_either; eauto.
  erewrite mem_disjoint_either; eauto.
  eapply ptsto_valid'; pred_apply; cancel.
  eapply ptsto_valid'; pred_apply; cancel.
  
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
  - eapply world_impl_secure. 
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

Hint Resolve writeback_secure.

(* Definition evict a (cs : cachestate) :=
    cs <- writeback a cs;
    match Map.find a (CSMap cs) with
    | Some _ =>
      Ret (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs - 1) (CSEvict cs))
    | None =>
      Ret (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs) (CSEvict cs))
    end.
*)

Theorem evict_secure:
  forall a cs d F vs,
  @prog_secure _ addr_eq_dec _ _ 
  (fun m m' => (rep cs d * [[ (F * diskIs m')%pred m]])%pred m)
  (fun m m' => (exists cs', rep cs' d * [[ (F * diskIs m')%pred m]])%pred m)
  (evict a cs) (a|-> vs) (match Map.find a (CSMap cs) with
                          | Some (v, true) => a|->(v, vsmerge vs)
                          | _ => a|->vs
                          end).
Proof.
  unfold evict; intros.
  eapply bind_secure; eauto; intros.
  destruct (Map.find a (CSMap x)); eauto.
Qed.
Hint Resolve evict_secure.

(* Definition maybe_evict (cs : cachestate) :=
    If (lt_dec (CSCount cs) (CSMaxCount cs)) {
      Ret cs
    } else {
      let (victim, evictor) := eviction_choose (CSEvict cs) in
      match (Map.find victim (CSMap cs)) with
      | Some _ =>
        cs <- evict victim (mk_cs (CSMap cs) (CSMaxCount cs) (CSCount cs) evictor);
        Ret cs
      | None => (* evictor failed, evict first block *)
        match (Map.elements (CSMap cs)) with
        | nil => Ret cs
        | (a, v) :: tl =>
          cs <- evict a cs;
          Ret cs
        end
      end
    }.
    
     (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
       | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
       | None =>  match elements (CSMap cs) with
                         | nil => Empty_set _
                         | (a, _) :: _ => Singleton _ a
                         end
       end). *)
    
Theorem maybe_evict_secure:
  forall cs d F vs,
  let (victim, _) := eviction_choose (CSEvict cs) in
  @prog_secure _ addr_eq_dec _ _ 
  (fun m m' => (rep cs d * [[ (F * diskIs m')%pred m]])%pred m)
  (fun m m' => (exists cs', rep cs' d * [[ (F * diskIs m')%pred m]])%pred m)
  (maybe_evict cs) 
  (* pre*)
  (match (Map.find victim (CSMap cs)) with
  | Some _ => victim |-> vs
  | None => (* evictor failed, evict first block *)
    match (Map.elements (CSMap cs)) with
    | nil => emp
    | (a, _) :: _ => a|-> vs
    end
  end)
  (* post*)
  (if (lt_dec (CSCount cs) (CSMaxCount cs)) then
       match (Map.find victim (CSMap cs)) with
        | Some _ => victim |-> vs
        | None => (* evictor failed, evict first block *)
          match (Map.elements (CSMap cs)) with
          | nil => emp
          | (a, _) :: _ => a|-> vs
          end
        end
  else
      match (Map.find victim (CSMap cs)) with
      | Some (v, true) => victim |-> (v, vsmerge vs)
      | Some (v, false) => victim |-> vs
      | None => (* evictor failed, evict first block *)
        match (Map.elements (CSMap cs)) with
        | nil => emp
        | (a, _) :: _ => 
          match Map.find a (CSMap cs) with
          | Some (v, true) => a|->(v, vsmerge vs)
          | _ => a|->vs
          end
        end
      end).
Proof.
  unfold maybe_evict; intros.
  destruct (lt_dec (CSCount cs) (CSMaxCount cs)); simpl; eauto.
  - eapply world_impl_secure; eauto.
    intros.
    apply H.
    intros.
    eexists; apply H2.
    
  - destruct (Map.find 0 (CSMap cs)) eqn:D.
    + destruct p.
        replace ({|  CSMap := CSMap cs;
                           CSMaxCount := CSMaxCount cs;
                           CSCount := CSCount cs;
                           CSEvict := CSEvict cs |}) with cs by (destruct cs; simpl; auto).
        eapply bind_secure; eauto; intros.
        rewrite D; eauto.
    + destruct (Map.elements (CSMap cs)) eqn:D0; eauto.
        * eapply world_impl_secure; eauto.
           intros.
           apply H.
           intros.
           eexists; apply H2.
        * destruct p.
           eapply bind_secure; eauto.
Qed.



Definition read a (cs : cachestate) :=
  cs <- maybe_evict cs;
  match Map.find a (CSMap cs) with
  | Some (v, dirty) => Ret ^(cs, v)
  | None =>
    AlertModified;;
    v <- Read a;
    Ret ^(mk_cs (Map.add a (v, false) (CSMap cs))
               (CSMaxCount cs) (CSCount cs + 1) (eviction_update (CSEvict cs) a), v)
  end.

Definition write a v (cs : cachestate) :=
  cs <- maybe_evict cs;
  match Map.find a (CSMap cs) with
  | Some _ =>
    Ret (mk_cs (Map.add a (v, true) (CSMap cs))
               (CSMaxCount cs) (CSCount cs) (eviction_update (CSEvict cs) a))
  | None =>
    Ret (mk_cs (Map.add a (v, true) (CSMap cs))
               (CSMaxCount cs) (CSCount cs + 1) (eviction_update (CSEvict cs) a))
  end.

Definition begin_sync (cs : cachestate) :=
  Ret cs.

Definition sync a (cs : cachestate) :=
  cs <- writeback a cs;
  Ret cs.

Definition end_sync (cs : cachestate) :=
  Sync;;
  Ret cs.


Definition cache0 sz := mk_cs (Map.empty _) sz 0 eviction_init.

Definition init (cachesize : nat) :=
  Sync;;
  Ret (cache0 cachesize).

Definition read_array a i cs :=
  r <- read (a + i) cs;
  Ret r.

Definition write_array a i v cs :=
  cs <- write (a + i) v cs;
  Ret cs.

Definition sync_array a i cs :=
  cs <- sync (a + i) cs;
  Ret cs.


