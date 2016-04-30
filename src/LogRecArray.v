Require Import Eqdep_dec Arith Omega List ListUtils Rounding Psatz.
Require Import Word WordAuto AsyncDisk Pred PredCrash GenSepN Array SepAuto.
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
    rx ^(ms, selN_val2block v off).

  Definition put T lxp xp ix item ms rx : prog T :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- LOG.read_array lxp (RAStart xp) bn ms;
    let v' := block2val_updN_val2block v off item in
    ms <- LOG.write_array lxp (RAStart xp) bn v' ms;
    rx ms.

  (** read n blocks starting from the beginning *)
  Definition read T lxp xp nblocks ms rx : prog T :=
    let^ (ms, r) <- LOG.read_range lxp (RAStart xp) nblocks iunpack nil ms;
    rx ^(ms, r).

  (** write all items starting from the beginning *)
  Definition write T lxp xp items ms rx : prog T :=
    ms <- LOG.write_range lxp (RAStart xp) (ipack items) ms;
    rx ms.

  (** set all items to item0 *)
  Definition init T lxp xp ms rx : prog T :=
    ms <- LOG.write_range lxp (RAStart xp) (repeat $0 (RALen xp)) ms;
    rx ms.

  (* find the first item that satisfies cond *)
  Definition ifind T lxp xp (cond : item -> addr -> bool) ms rx : prog T :=
    let^ (ms) <- ForN i < (RALen xp)
    Hashmap hm
    Ghost [ F crash m1 m2 ]
    Loopvar [ ms ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m1 m2) ms hm
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
    apply Forall_wellformed_updN; auto.
  Qed.

  Lemma ifind_length_ok : forall xp i items,
    i < RALen xp ->
    items_valid xp items ->
    i < length (synced_list (ipack items)).
  Proof.
    unfold items_valid; intuition.
    eapply synced_list_ipack_length_ok; eauto.
  Qed.

  Lemma items_valid_length_eq : forall xp a b,
    items_valid xp a ->
    items_valid xp b ->
    length (ipack a) = length (ipack b).
  Proof.
    unfold items_valid; intuition.
    eapply ipack_length_eq; eauto.
  Qed.

  Theorem get_ok : forall lxp xp ix ms,
    {< F Fm m0 m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ ix < length items ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
          [[ r = selN items ix item0 ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} get lxp xp ix ms.
  Proof.
    unfold get, rep.
    hoare.

    (* [rewrite selN_val2block_equiv] somewhere *)

    rewrite synced_list_length, ipack_length.
    apply div_lt_divup; auto.
    subst; rewrite synced_list_selN; simpl.
    erewrite selN_val2block_equiv.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
  Qed.


  Theorem put_ok : forall lxp xp ix e ms,
    {< F Fm m0 m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ ix < length items /\ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
          [[[ m' ::: Fm * rep xp (updN items ix e) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} put lxp xp ix e ms.
  Proof.
    unfold put, rep.
    hoare; subst.

    (* [rewrite block2val_updN_val2block_equiv] somewhere *)

    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    unfold items_valid in *; intuition auto.

    apply arrayN_unify.
    rewrite synced_list_selN, synced_list_updN; f_equal; simpl.
    rewrite block2val_updN_val2block_equiv.
    apply ipack_updN_divmod; auto.
    apply list_chunk_wellformed.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
    apply items_valid_updN; auto.
  Qed.


  Theorem read_ok : forall lxp xp nblocks ms,
    {< F Fm m0 m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ nblocks <= RALen xp ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
          [[ r = firstn (nblocks * items_per_val) items ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
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
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ items_valid xp items ]] *
          [[[ m ::: Fm * rep xp old ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
          [[[ m' ::: Fm * rep xp items ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} write lxp xp items ms.
  Proof.
    unfold write, rep.
    hoare.

    unfold items_valid in *; intuition; auto.
    erewrite synced_list_length, items_valid_length_eq; eauto.
    rewrite vsupsyn_range_synced_list; auto.
    erewrite synced_list_length, items_valid_length_eq; eauto.
  Qed.


  Theorem init_ok : forall lxp xp ms,
    {< F Fm m0 m vsl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ xparams_ok xp /\ RAStart xp <> 0 /\ length vsl = RALen xp ]] *
          [[[ m ::: Fm * arrayN (RAStart xp) vsl ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
          [[[ m' ::: Fm * rep xp (repeat item0 ((RALen xp) * items_per_val) ) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep.
    hoare.

    rewrite repeat_length; omega.
    rewrite vsupsyn_range_synced_list by (rewrite repeat_length; auto).
    apply arrayN_unify; f_equal.
    apply repeat_ipack_item0.

    unfold items_valid; intuition.
    rewrite repeat_length; auto.
    apply Forall_repeat.
    apply item0_wellformed.
  Qed.


  Theorem ifind_ok : forall lxp xp cond ms,
    {< F Fm m0 m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true
                         /\ (fst st) < length items
                         /\ snd st = selN items (fst st) item0 ]])
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} ifind lxp xp cond ms.
  Proof.
    unfold ifind, rep.
    safestep. eauto.
    safestep.
    eapply ifind_length_ok; eauto.

    step.
    unfold items_valid in *; intuition.
    or_r; cancel.
    replace p_2 with (snd (p_1, p_2)) by auto.
    eapply ifind_block_ok_cond; eauto.
    replace p_1 with (fst (p_1, p_2)) by auto.
    eapply ifind_result_inbound; eauto.
    replace p_2 with (snd (p_1, p_2)) by auto.
    eapply ifind_result_item_ok; eauto.
    cancel.

    step.

    (*XXX: why is anon0 created so early? *)

    Unshelve. exact tt.
  Admitted.

  Hint Extern 1 ({{_}} progseq (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_}} progseq (put _ _ _ _ _) _) => apply put_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (init _ _ _) _) => apply init_ok : prog.
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
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e) ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' * [[ r = e ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
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
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e0) ]]]
    POST:hm' RET:ms' exists m' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
          [[ items' = updN items ix e ]] *
          [[[ m' ::: Fm * rep xp items' ]]] *
          [[[ items' ::: Fi * (ix |-> e) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
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
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ length l = (nblocks * items_per_val)%nat ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * arrayN 0 l ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
          [[ r = l ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} read_array lxp xp nblocks ms.
  Proof.
    unfold read_array.
    hoare.
    eapply read_array_length_ok; eauto.
    subst; eapply read_array_list_ok; eauto.
  Qed.


  Theorem ifind_array_ok : forall lxp xp cond ms,
    {< F Fm m0 m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true ]] *
          [[[ items ::: arrayN_ex items (fst st) * (fst st) |-> (snd st) ]]] )
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
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

  Theorem xform_rep : forall xp l,
    crash_xform (rep xp l) <=p=> rep xp l.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite crash_xform_arrayN_synced; cancel.
    cancel.
    xform_normr; cancel.
    rewrite <- crash_xform_arrayN_r; eauto.
    apply possible_crash_list_synced_list.
  Qed.

End LogRecArray.

