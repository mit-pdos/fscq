Require Import Eqdep_dec Arith Omega List ListUtils MapUtils Rounding Psatz.
Require Import Word WordAuto AsyncDisk Pred GenSepN Array SepAuto.
Require Import Rec Prog BasicProg Hoare RecArrayUtils Log.
Import ListNotations.

Set Implicit Arguments.


Module LogRecArray (RA : RASig).

  Module Defs := RADefs RA.
  Import RA Defs.

  Definition items_valid xp (items : itemlist) :=
    xparams_ok xp /\ RAStart xp <> 0 /\
    length items = (RALen xp) * items_per_val /\
    Forall Rec.well_formed items.

  (** rep invariant *)
  Definition rep xp (items : itemlist) :=
    ( exists vl, [[ vl = ipack items ]] *
      [[ items_valid xp items ]] *
      arrayN (RAStart xp) (synced_list vl))%pred.

  Definition get T lxp xp ix ms rx : prog T :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- LOG.read_array lxp (RAStart xp) bn ms;
    rx ^(ms, selN (val2block v) off item0).

  Definition put T lxp xp ix item ms rx : prog T :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- LOG.read_array lxp (RAStart xp) bn ms;
    let v' := block2val (updN (val2block v) off item) in
    ms <- LOG.write_array lxp (RAStart xp) bn v' ms;
    rx ms.

  (** read n blocks starting from the beginning *)
  Definition read T lxp xp nblocks ms rx : prog T :=
    let^ (ms, r) <- LOG.read_range lxp (RAStart xp) nblocks iunpack nil ms;
    rx ^(ms, r).

  (** write full blocks starting from the beginning *)
  Definition write T lxp xp items ms rx : prog T :=
    ms <- LOG.write_range lxp (RAStart xp) (ipack items) ms;
    rx ms.

  Fixpoint ifind_block (cond : item -> addr -> bool) (vs : block) start : option (addr * item ) :=
    match vs with
    | nil => None
    | x :: rest =>
        if (cond x start) then Some (start, x)
                          else ifind_block cond rest (S start)
    end.

  (* find the first item that satisfies cond *)
  Definition ifind T lxp xp (cond : item -> addr -> bool) ms rx : prog T :=
    let^ (ms) <- ForN i < (RALen xp)
    Ghost [ F crash m1 m2 ]
    Loopvar [ ms ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m1 m2) ms
    OnCrash  crash
    Begin
      let^ (ms, v) <- LOG.read_array lxp (RAStart xp) i ms;
      let r := ifind_block cond (val2block v) (i * items_per_val) in
      match r with
      | None => lrx ^(ms)
      | Some ifs => rx ^(ms, Some ifs)
      end
    Rof ^(ms);
    rx ^(ms, None).

  Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.


  Lemma items_valid_updN : forall xp items a v,
    items_valid xp items ->
    Rec.well_formed v ->
    items_valid xp (updN items a v).
  Proof.
    unfold items_valid; intuition.
    rewrite length_updN; auto.
    rewrite Forall_forall in *; intuition.
    apply in_updN in H3; destruct H3; subst; eauto.
  Qed.

  Lemma ifind_length_ok : forall xp i items,
    i < RALen xp ->
    items_valid xp items ->
    i < length (synced_list (ipack items)).
  Proof.
    unfold items_valid; intuition.
    rewrite synced_list_length, ipack_length.
    setoid_rewrite H2.
    rewrite divup_mul; auto.
  Qed.

  Lemma ifind_block_ok_mono : forall cond vs start r,
    ifind_block cond vs start = Some r ->
    fst r >= start.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; auto.
    apply le_Sn_le.
    apply IHvs; auto.
  Qed.

  Lemma ifind_block_ok_bound : forall cond vs start r,
    ifind_block cond vs start = Some r ->
    fst r < start + length vs.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; omega.
    replace (start + S (length vs)) with (S start + length vs) by omega.
    apply IHvs; auto.
  Qed.

  Lemma ifind_block_ok_cond : forall cond vs start r,
    ifind_block cond vs start = Some r ->
    cond (snd r) (fst r) = true.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; auto.
    eapply IHvs; eauto.
  Qed.

  Lemma ifind_block_ok_item : forall cond vs start r,
    ifind_block cond vs start = Some r ->
    selN vs ((fst r) - start) item0 = (snd r).
  Proof.
    induction vs; intros.
    simpl in *; try congruence.
    simpl in H; destruct (cond a) eqn: C.
    inversion H; simpl; auto.
    rewrite Nat.sub_diag; simpl; auto.
    replace (fst r - start) with ((fst r - S start) + 1).
    rewrite selN_cons, Nat.add_sub by omega.
    apply IHvs; auto.
    apply ifind_block_ok_mono in H; omega.
  Qed.


  Lemma ifind_block_ok_facts : forall cond vs start r,
    ifind_block cond vs start = Some r ->
    (fst r) >= start /\
    (fst r) < start + length vs /\
    cond (snd r) (fst r) = true /\
    selN vs ((fst r) - start) item0 = (snd r).
  Proof.
    intros; intuition.
    eapply ifind_block_ok_mono; eauto.
    eapply ifind_block_ok_bound; eauto.
    eapply ifind_block_ok_cond; eauto.
    eapply ifind_block_ok_item; eauto.
  Qed.


  Lemma ifind_result_inbound :  forall xp bn items cond r,
    items_valid xp items ->
    bn < RALen xp ->
    ifind_block cond (val2block (fst (selN (synced_list (ipack items)) bn ($0, nil))))
      (bn * items_per_val) = Some r ->
    fst r < length items.
  Proof.
    intros.
    apply ifind_block_ok_facts in H1 as [Hm [ Hb [ Hc Hi ] ] ].
    unfold items_valid in H; intuition.
    apply list_chunk_wellformed in H4.
    rewrite synced_list_selN in Hb; simpl in Hb.
    unfold ipack in *; rewrite val2block2val_selN_id in * by auto.
    rewrite list_chunk_spec, setlen_length in *.

    rewrite H2.
    eapply lt_le_trans; eauto.
    setoid_rewrite <- Nat.mul_1_l at 5.
    rewrite <- Nat.mul_add_distr_r.
    apply Nat.mul_le_mono_r; omega.
  Qed.


  Lemma ifind_result_item_ok : forall xp bn items cond r,
    items_valid xp items ->
    bn < RALen xp ->
    ifind_block cond (val2block (fst (selN (synced_list (ipack items)) bn ($0, nil))))
      (bn * items_per_val) = Some r ->
    (snd r) = selN items (fst r) item0.
  Proof.
    intros.
    apply ifind_block_ok_facts in H1 as [Hm [ Hb [ Hc Hi ] ] ].
    rewrite <- Hi.
    rewrite synced_list_selN; simpl.
    unfold items_valid in H; intuition.
    apply list_chunk_wellformed in H4.
    rewrite synced_list_selN in Hb; simpl in Hb.
    unfold ipack in *; rewrite val2block2val_selN_id in * by auto.
    rewrite list_chunk_spec, setlen_length in *.
    unfold setlen; rewrite selN_app1.
    rewrite selN_firstn, skipn_selN, le_plus_minus_r by omega; auto.
    rewrite firstn_length, skipn_length.
    apply Nat.min_glb_lt; try omega.
    setoid_rewrite H2.
    apply lt_add_lt_sub in Hb; auto.
    eapply lt_le_trans; eauto.
    rewrite <- Nat.mul_sub_distr_r, <- Nat.mul_1_l at 1.
    apply Nat.mul_le_mono_r; omega.
  Qed.

  Lemma items_valid_length_eq : forall xp a b,
    items_valid xp a ->
    items_valid xp b ->
    length (ipack a) = length (ipack b).
  Proof.
    unfold items_valid; intuition.
    repeat rewrite ipack_length.
    setoid_rewrite H3; setoid_rewrite H4; auto.
  Qed.


  Lemma vsupsyn_range_synced_list : forall a b,
    length a = length b ->
    vsupsyn_range a b = synced_list b.
  Proof.
    unfold vsupsyn_range, synced_list; intros.
    rewrite skipn_oob by omega.
    rewrite app_nil_r; auto.
  Qed.


  Theorem get_ok : forall lxp xp ix ms,
    {< F Fm m0 m items,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ ix < length items ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' *
          [[ r = selN items ix item0 ]]
    CRASH LOG.intact lxp F m0
    >} get lxp xp ix ms.
  Proof.
    unfold get, rep.
    hoare.

    rewrite synced_list_length, ipack_length.
    apply div_lt_divup; auto.
    subst; rewrite synced_list_selN; simpl.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
  Qed.


  Theorem put_ok : forall lxp xp ix e ms,
    {< F Fm m0 m items,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ ix < length items /\ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' *
          [[[ m' ::: Fm * rep xp (updN items ix e) ]]]
    CRASH LOG.intact lxp F m0
    >} put lxp xp ix e ms.
  Proof.
    unfold put, rep.
    hoare; subst.

    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    unfold items_valid in *; intuition auto.

    apply arrayN_unify.
    rewrite synced_list_selN, synced_list_updN; f_equal; simpl.
    apply ipack_updN_divmod; auto.
    apply list_chunk_wellformed.
    unfold items_valid in *; intuition; auto.
    apply items_valid_updN; auto.
  Qed.


  Theorem read_ok : forall lxp xp nblocks ms,
    {< F Fm m0 m items,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ nblocks <= RALen xp ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' *
          [[ r = firstn (nblocks * items_per_val) items ]]
    CRASH LOG.intact lxp F m0
    >} read lxp xp nblocks ms.
  Proof.
    unfold read, rep.
    hoare.

    rewrite synced_list_length, ipack_length.
    unfold items_valid in *; intuition.
    setoid_rewrite H3; rewrite divup_mul; auto.

    subst; rewrite synced_list_map_fst.
    unfold items_valid in *; intuition.
    eapply iunpack_ipack_firstn; eauto.
  Qed.

  Theorem write_ok : forall lxp xp items ms,
    {< F Fm m0 m old,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ items_valid xp items ]] *
          [[[ m ::: Fm * rep xp old ]]]
    POST RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' *
          [[[ m' ::: Fm * rep xp items ]]]
    CRASH LOG.intact lxp F m0
    >} write lxp xp items ms.
  Proof.
    unfold write, rep.
    hoare.

    unfold items_valid in *; intuition; auto.
    erewrite synced_list_length, items_valid_length_eq; eauto.
    rewrite vsupsyn_range_synced_list; auto.
    erewrite synced_list_length, items_valid_length_eq; eauto.
  Qed.


  Theorem ifind_ok : forall lxp xp cond ms,
    {< F Fm m0 m items,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[[ m ::: Fm * rep xp items ]]]
    POST RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true
                         /\ (fst st) < length items
                         /\ snd st = selN items (fst st) item0 ]])
    CRASH LOG.intact lxp F m0
    >} ifind lxp xp cond ms.
  Proof.
    unfold ifind, rep.
    step.
    step.
    eapply ifind_length_ok; eauto.

    step.
    or_r; cancel.
    replace i with (snd (n, i)) by auto.
    eapply ifind_block_ok_cond; eauto.
    replace n with (fst (n, i)) by auto.
    eapply ifind_result_inbound; eauto.
    replace i with (snd (n, i)) by auto.
    eapply ifind_result_item_ok; eauto.
    step.
    Unshelve. exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_}} progseq (put _ _ _ _ _) _) => apply put_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (ifind _ _ _ _) _) => apply ifind_ok : prog.


  (** operations using array spec *)

  Definition get_array T lxp xp ix ms rx : prog T :=
    r <- get lxp xp ix ms;
    rx r.

  Definition put_array T lxp xp ix item ms rx : prog T :=
    r <- put lxp xp ix item ms;
    rx r.

  Definition read_array T lxp xp nblocks ms rx : prog T :=
    r <- read lxp xp nblocks ms;
    rx r.

  Definition ifind_array T lxp xp cond ms rx : prog T :=
    r <- ifind lxp xp cond ms;
    rx r.

  Theorem get_array_ok : forall lxp xp ix ms,
    {< F Fm Fi m0 m items e,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e) ]]]
    POST RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' * [[ r = e ]]
    CRASH LOG.intact lxp F m0
    >} get_array lxp xp ix ms.
  Proof.
    unfold get_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    subst; apply eq_sym.
    eapply list2nmem_sel; eauto.
  Qed.


  Theorem put_array_ok : forall lxp xp ix e ms,
    {< F Fm Fi m0 m items e0,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e0) ]]]
    POST RET:ms' exists m' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' *
          [[ items' = updN items ix e ]] *
          [[[ m' ::: Fm * rep xp items' ]]] *
          [[[ items' ::: Fi * (ix |-> e) ]]]
    CRASH LOG.intact lxp F m0
    >} put_array lxp xp ix e ms.
  Proof.
    unfold put_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    eapply list2nmem_updN; eauto.
  Qed.


  Lemma read_array_length_ok : forall l xp Fm Fi m items nblocks,
    length l = nblocks * items_per_val ->
    (Fm * rep xp items)%pred (list2nmem m) ->
    (Fi * arrayN 0 l)%pred (list2nmem items) ->
    nblocks <= RALen xp.
  Proof.
    unfold rep; intuition.
    destruct_lift H0.
    unfold items_valid in *; subst; intuition.
    apply list2nmem_arrayN_length in H1.
    rewrite H, H3 in H1.
    eapply Nat.mul_le_mono_pos_r.
    apply items_per_val_gt_0.
    auto.
  Qed.

  Lemma read_array_list_ok : forall (l : list item) nblocks items Fi,
    length l = nblocks * items_per_val ->
    (Fi ✶ arrayN 0 l)%pred (list2nmem items) ->
    firstn (nblocks * items_per_val) items = l.
  Proof.
    intros.
    eapply arrayN_list2nmem in H0.
    rewrite <- H; simpl in *; auto.
    exact item0.
  Qed.


  Theorem read_array_ok : forall lxp xp nblocks ms,
    {< F Fm Fi m0 m items l,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ length l = (nblocks * items_per_val)%nat ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * arrayN 0 l ]]]
    POST RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' *
          [[ r = l ]]
    CRASH LOG.intact lxp F m0
    >} read_array lxp xp nblocks ms.
  Proof.
    unfold read_array.
    hoare.
    eapply read_array_length_ok; eauto.
    subst; eapply read_array_list_ok; eauto.
  Qed.

  Theorem ifind_array_ok : forall lxp xp cond ms,
    {< F Fm m0 m items,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[[ m ::: Fm * rep xp items ]]]
    POST RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true ]] *
          [[[ items ::: arrayN_ex items (fst st) * (fst st) |-> (snd st) ]]] )
    CRASH LOG.intact lxp F m0
    >} ifind_array lxp xp cond ms.
  Proof.
    unfold ifind_array; intros.
    hoare.
    or_r; cancel.
    apply list2nmem_ptsto_cancel; auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (get_array _ _ _ _) _) => apply get_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (put_array _ _ _ _ _) _) => apply put_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (ifind_array _ _ _ _) _) => apply ifind_array_ok : prog.

  (* If two arrays are in the same spot, their contents have to be equal *)
  Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.


  Lemma items_wellforemd : forall F xp l m,
    (F * rep xp l)%pred m -> Forall Rec.well_formed l.
  Proof.
    unfold rep, items_valid; intuition.
    destruct_lift H; auto.
  Qed.

  Lemma items_wellforemd_pimpl : forall xp l,
    rep xp l =p=> [[ Forall Rec.well_formed l ]] * rep xp l.
  Proof.
    unfold rep, items_valid; cancel.
  Qed.

  Lemma item_wellforemd : forall F xp m l i,
    (F * rep xp l)%pred m -> Rec.well_formed (selN l i item0).
  Proof.
    intros.
    destruct (lt_dec i (length l)).
    apply Forall_selN; auto.
    eapply items_wellforemd; eauto.
    rewrite selN_oob by omega.
    apply item0_wellformed.
  Qed.

  Lemma items_length_ok : forall F xp l m,
    (F * rep xp l)%pred m ->
    length l = (RALen xp) * items_per_val.
  Proof.
    unfold rep, items_valid; intuition.
    destruct_lift H; auto.
  Qed.

  Lemma items_length_ok_pimpl : forall xp l,
    rep xp l =p=> [[ length l = ((RALen xp) * items_per_val)%nat ]] * rep xp l.
  Proof.
    unfold rep, items_valid; cancel.
  Qed.

End LogRecArray.


