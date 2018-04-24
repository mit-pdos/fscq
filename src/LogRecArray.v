Require Import Eqdep_dec Arith Omega List ListUtils Rounding Psatz.
Require Import Word WordAuto Mem Pred.
Require Import Rec.
Require Import FMapAVL FMapMem.
Require Import MapUtils.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Export Log.
Import ListNotations.

Set Implicit Arguments.


Lemma Forall_can_access_public:
  forall pr n,
    Forall (can_access pr) (repeat Public n).
Proof.
  intros; rewrite Forall_forall in *; intros.
  apply repeat_spec in H; subst; eauto.
Qed.

Lemma can_access_repeat_public_selN:
  forall pr n i,
    can_access pr (selN (repeat Public n) i Public).
Proof.
  intros.
  destruct (lt_dec i n).
  rewrite repeat_selN; auto.
  rewrite selN_oob; eauto.
  rewrite repeat_length; omega.
Qed.


Lemma repeat_updN_noop:
  forall T (x:T) n a,
    updN (repeat x n) a x = repeat x n.
Proof.
  intros.
  eapply selN_eq_updN_eq; auto.
  destruct (lt_dec a n).
  rewrite repeat_selN; auto.
  rewrite selN_oob; eauto.
  rewrite repeat_length; omega.
Qed.


    
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
      arrayN (@ptsto _ addr_eq_dec valuset) (RAStart xp) (synced_list (List.combine (repeat Public (length (ipack items))) vl)))%pred.

  Definition get lxp xp ix ms :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, h) <- LOG.read_array lxp (RAStart xp) bn ms;;
    v <- Unseal h;;             
    Ret ^(ms, selN_val2block v off).

  Definition put lxp xp ix item ms :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, h) <- LOG.read_array lxp (RAStart xp) bn ms;;
    v <- Unseal h;;           
    let v' := block2val_updN_val2block v off item in
    h' <- Seal Public v';;
    ms <- LOG.write_array lxp (RAStart xp) bn h' ms;;
    Ret ms.

  (** read n blocks starting from the beginning *)
  Definition read lxp xp nblocks ms :=
    let^ (ms, r) <- LOG.read_range lxp (RAStart xp) nblocks ms;;
    r <- unseal_all r;;
    Ret ^(ms, fold_left iunpack r nil).

  (** write all items starting from the beginning *)
  Definition write lxp xp items ms :=
    hl <- seal_all (repeat Public (length (ipack items))) (ipack items);;     
    ms <- LOG.write_range lxp (RAStart xp) hl ms;;
    Ret ms.

  (** set all items to item0 *)
  Definition init lxp xp ms :=
    hl <- seal_all (repeat Public (RALen xp)) (repeat $0 (RALen xp));; 
    ms <- LOG.write_range lxp (RAStart xp) hl ms;;
    Ret ms.

  (* find the first item that satisfies cond *)
  Definition ifind lxp xp (cond : item -> addr -> bool) ms :=
    let^ (ms, ret) <- ForN i < (RALen xp)
    Blockmem bm
    Hashmap hm
    Ghost [ F m xp items Fm crash sm m1 m2]
    Loopvar [ ms ret ]
    Invariant
    LOG.rep lxp F (LOG.ActiveTxn m1 m2) ms sm bm hm *
    [[[ m ::: Fm * rep xp items ]]] *                          
    [[ forall st,
       ret = Some st ->
       cond (snd st) (fst st) = true
       /\ (fst st) < length items
       /\ snd st = selN items (fst st) item0 ]]
    OnCrash  crash
    Begin
      If (is_some ret) {
        Ret ^(ms, ret)
      } else {
        let^ (ms, h) <- LOG.read_array lxp (RAStart xp) i ms;;
        v <- Unseal h;;
        let r := ifind_block cond (val2block v) (i * items_per_val) in
        match r with
        (* loop call *)
        | None => Ret ^(ms, None)
        (* break *)
        | Some ifs => Ret ^(ms, Some ifs)
        end
      }
    Rof ^(ms, None);;
    Ret ^(ms, ret).
  
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

  Lemma items_valid_upd_range : forall xp items len a v,
    items_valid xp items ->
    Rec.well_formed v ->
    items_valid xp (upd_range items a len v).
  Proof.
    induction len; simpl; intros; auto using items_valid_updN.
  Qed.

  Lemma ifind_length_ok : forall xp i tags items,
    i < RALen xp ->
    items_valid xp items ->
    length tags = length (ipack items) ->
    i < length (synced_list (List.combine tags (ipack items))).
  Proof.
    unfold items_valid; intuition.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    rewrite H1, ipack_length; setoid_rewrite H3; rewrite divup_mul; auto.
  Qed.

  Lemma items_valid_length_eq : forall xp a b,
    items_valid xp a ->
    items_valid xp b ->
    length (ipack a) = length (ipack b).
  Proof.
    unfold items_valid; intuition.
    eapply ipack_length_eq; eauto.
  Qed.

  Theorem get_ok :
    forall lxp xp ix ms pr,
    {< F Fm m0 sm m items,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ ix < length items ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:bm', hm', RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
          [[ r = selN items ix item0 ]]
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} get lxp xp ix ms.
  Proof.
    unfold get, rep.
    safestep.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    cleanup; rewrite ipack_length.
    rewrite repeat_length; apply div_lt_divup; auto.
    apply repeat_length.

    safestep.
    eauto.
    cleanup.
    subst; setoid_rewrite synced_list_selN; simpl.
    setoid_rewrite selN_combine; eauto.
    rewrite repeat_selN.
    eauto.
    rewrite ipack_length.
    apply div_lt_divup; auto.
    apply repeat_length.

    erewrite selN_val2block_equiv.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
    solve_hashmap_subset.
    apply Nat.mod_upper_bound; auto.
    cancel.
  Qed.


  Theorem put_ok :
    forall lxp xp ix e ms pr,
    {< F Fm m0 sm m items,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ ix < length items /\ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:bm', hm', RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
          [[[ m' ::: Fm * rep xp (updN items ix e) ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} put lxp xp ix e ms.
  Proof.
    unfold put, rep.
    step.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    cleanup; rewrite ipack_length.
    rewrite repeat_length; apply div_lt_divup; auto.
    apply repeat_length.

    safestep.
    eauto.
    cleanup.
    subst; setoid_rewrite synced_list_selN; simpl.
    setoid_rewrite selN_combine; eauto.
    rewrite repeat_selN; eauto.
    rewrite ipack_length.
    apply div_lt_divup; auto.
    apply repeat_length.

    step.
    safestep.
    erewrite LOG.rep_blockmem_subset; eauto.
    erewrite LOG.rep_hashmap_subset; eauto.
    erewrite LOG.rep_hashmap_subset; eauto.
    eassign F_; eassign F; eassign m0; eassign m; cancel.
    rewrite upd_eq; eauto.
    eauto.
    eauto.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    rewrite ipack_length.
    rewrite repeat_length; apply div_lt_divup; auto.
    apply repeat_length.
    unfold items_valid in *; intuition.
    eauto.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.

    pred_apply.
    cancel.
    rewrite synced_list_updN; f_equal; simpl.
    rewrite block2val_updN_val2block_equiv.
    setoid_rewrite <- combine_updN.
    rewrite ipack_updN_divmod; auto.
    repeat rewrite ipack_length.
    setoid_rewrite length_updN.
    rewrite repeat_updN_noop; eauto.
    apply list_chunk_wellformed.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
    apply items_valid_updN; auto.
    solve_hashmap_subset.

    rewrite <- H1; safecancel.
    apply LOG.active_intact.
    solve_hashmap_subset.
    solve_blockmem_subset.
    cancel.

    rewrite <- H1; cancel.
    apply LOG.active_intact.
    solve_hashmap_subset.

    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.    
  Qed.


  Theorem read_ok :
    forall lxp xp nblocks ms pr,
    {< F Fm m0 sm m items,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ nblocks <= RALen xp ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:bm', hm', RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
          [[ r = firstn (nblocks * items_per_val) items ]]
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} read lxp xp nblocks ms.
  Proof.
    unfold read, rep.
    step.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    rewrite ipack_length.
    rewrite repeat_length; auto.
    cleanup.
    unfold items_valid in *; intuition; cleanup.
    setoid_rewrite H4.
    rewrite divup_mul; auto.
    apply repeat_length.

    step.
    rewrite H13 in H4.
    rewrite synced_list_map_fst in H4.
    rewrite <- firstn_map_comm in H4.
    setoid_rewrite map_fst_combine in H4; auto.
    apply in_firstn_in in H4; apply repeat_spec in H4; auto.
    apply repeat_length.

    step.
    step.
    rewrite LOG.rep_blockmem_subset; eauto.
    erewrite LOG.rep_hashmap_subset; eauto.
    solve_hashmap_subset.   
    
    cleanup; rewrite synced_list_map_fst.
    rewrite <- firstn_map_comm.
    setoid_rewrite map_snd_combine; auto.
    unfold items_valid in *; intuition.
    eapply iunpack_ipack_firstn; eauto.
    apply repeat_length.
    solve_hashmap_subset.

    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem write_ok :
    forall lxp xp items ms pr,
    {< F Fm m0 sm m old,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ items_valid xp items ]] *
          [[[ m ::: Fm * rep xp old ]]]
    POST:bm', hm', RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
          [[[ m' ::: Fm * rep xp items ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} write lxp xp items ms.
  Proof.
    unfold write, rep.
    step.
    apply repeat_length.
    apply repeat_spec in H; auto.

    safestep.
    rewrite LOG.rep_blockmem_subset; [|eauto].
    erewrite LOG.rep_hashmap_subset; eauto.
    
    cleanup.
    rewrite map_fst_combine by apply repeat_length.
    rewrite Forall_forall; intros x Hin.
    apply repeat_spec in Hin; auto.
    
    eauto.
    unfold items_valid in *; intuition; auto.

    unfold items_valid in *; intuition; auto.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    erewrite <- extract_blocks_length; eauto.    
    cleanup.
    setoid_rewrite combine_length_eq; auto.
    cleanup; repeat rewrite ipack_length.
    setoid_rewrite H7. setoid_rewrite H10; eauto.
    apply repeat_length.
    apply repeat_length.
    auto.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    subst; clear H16.
    pred_apply; cancel.
    rewrite vsupsyn_range_synced_list; auto.
    erewrite <- extract_blocks_subset_trans; eauto.
    cleanup; auto.
    erewrite <- extract_blocks_subset_trans; eauto.
    cleanup; auto.
    unfold items_valid in *; intuition; auto.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    cleanup; repeat rewrite ipack_length.
    setoid_rewrite H14. setoid_rewrite H16; eauto.
    apply repeat_length.
    apply repeat_length.
    solve_hashmap_subset.
    
    rewrite <- H1; cancel.
    apply LOG.active_intact.
    solve_hashmap_subset.
    solve_blockmem_subset.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem init_ok :
    forall lxp xp ms pr,
    {< F Fm m0 sm m vsl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ xparams_ok xp /\ RAStart xp <> 0 /\ length vsl = RALen xp ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) (RAStart xp) vsl ]]]
    POST:bm', hm', RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
          [[[ m' ::: Fm * rep xp (repeat item0 ((RALen xp) * items_per_val)) ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep.
    step.
    
    repeat rewrite repeat_length; omega.
    apply repeat_spec in H; cleanup; auto.

    safestep.
    rewrite LOG.rep_blockmem_subset; [|eauto].
    erewrite LOG.rep_hashmap_subset; eauto.
    cleanup.
    rewrite map_fst_combine by (repeat rewrite repeat_length; auto).
    rewrite Forall_forall; intros x Hin.
    apply repeat_spec in Hin; auto.
    eauto.
    cleanup.
    erewrite <- extract_blocks_length; eauto.
    cleanup.
    setoid_rewrite combine_length_eq; auto.
    rewrite repeat_length; auto.
    repeat rewrite repeat_length; auto.
    auto.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    pred_apply; cancel.
    rewrite vsupsyn_range_synced_list; auto.
    erewrite <- extract_blocks_subset_trans; eauto.
    cleanup; auto.
    rewrite repeat_ipack_item0; auto.
    rewrite ipack_length, repeat_length.
    rewrite divup_mul; auto.
    erewrite <- extract_blocks_subset_trans; eauto.
    cleanup; auto.
    setoid_rewrite combine_length_eq; auto.
    rewrite repeat_length; eauto.
    repeat rewrite repeat_length; auto.
    unfold items_valid; intuition.
    rewrite repeat_length; auto.
    apply Forall_repeat.
    apply item0_wellformed.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    apply LOG.active_intact.
    solve_hashmap_subset.
    solve_blockmem_subset.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  
  Hint Extern 0 (okToUnify (LOG.arrayP (RAStart _) _) (LOG.arrayP (RAStart _) _)) =>
  constructor : okToUnify.


  Hint Resolve
       ifind_list_ok_cond
       ifind_result_inbound
       ifind_result_item_ok.

  Theorem ifind_ok :
    forall lxp xp cond ms pr,
    {< F Fm m0 sm m items,
    PERM:pr   
    PRE: bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: Fm * rep xp items ]]]
    POST:bm', hm', RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true
                         /\ (fst st) < length items
                         /\ snd st = selN items (fst st) item0 ]])
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} ifind lxp xp cond ms.
  Proof.
    unfold ifind, rep.
    safestep.
    eassign m.
    pred_apply; cancel.
    solve_hashmap_subset.
    eauto.

    safestep.
    safestep.
    safestep.
    erewrite LOG.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    cancel.

    unfold items_valid in *; intuition idtac.
    safestep.
    rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    cleanup; rewrite repeat_length, ipack_length.
    setoid_rewrite H9; rewrite divup_mul; auto.
    apply repeat_length.

    safestep.
    pose proof Forall_can_access_public as Hx.
    auto.
    
    cleanup.
    subst; setoid_rewrite synced_list_selN; simpl.
    setoid_rewrite selN_combine; eauto.
    rewrite repeat_selN; eauto.
    cleanup; rewrite ipack_length.
    setoid_rewrite H9; rewrite divup_mul; auto.
    apply repeat_length.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    solve_hashmap_subset.

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    solve_hashmap_subset.
    cancel.
    
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    step.
    step.
    
    erewrite LOG.rep_hashmap_subset; eauto.
    destruct a; cancel.
    match goal with
    | [ H: forall _, Some _ = Some _ -> _ |- _ ] =>
      edestruct H; eauto
    end.
    or_r; cancel.
    or_l; cancel.
    solve_hashmap_subset.
    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset))%pred.
    unfold false_pred; cancel.

    Unshelve. exact tt.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.
  
  Hint Extern 1 ({{_|_}} Bind (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (put _ _ _ _ _) _) => apply put_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (ifind _ _ _ _) _) => apply ifind_ok : prog.


  (** operations using array spec *)

  Definition get_array lxp xp ix ms :=
    r <- get lxp xp ix ms;;
    Ret r.

  Definition put_array lxp xp ix item ms :=
    r <- put lxp xp ix item ms;;
    Ret r.

  Definition read_array lxp xp nblocks ms :=
    r <- read lxp xp nblocks ms;;
    Ret r.

  Definition ifind_array lxp xp cond ms :=
    r <- ifind lxp xp cond ms;;
    Ret r.

  Theorem get_array_ok :
    forall lxp xp ix ms pr,
    {< F Fm Fi m0 sm m items e,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e) ]]]
    POST:bm', hm', RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' * [[ r = e ]]
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} get_array lxp xp ix ms.
  Proof.
    unfold get_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    erewrite LOG.rep_hashmap_subset; eauto.
    subst; apply eq_sym.
    eapply list2nmem_sel; eauto.
    solve_hashmap_subset.
  Qed.


  Theorem put_array_ok :
    forall lxp xp ix e ms pr,
    {< F Fm Fi m0 sm m items e0,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e0) ]]] 
    POST:bm', hm', RET:ms' exists m' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
          [[ items' = updN items ix e ]] *
          [[[ m' ::: Fm * rep xp  items' ]]] *
          [[[ items' ::: Fi * (ix |-> e) ]]] 
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} put_array lxp xp ix e ms.
  Proof.
    unfold put_array.
    safestep.
    eapply list2nmem_ptsto_bound; eauto.
    eassign Fm; cancel.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.  
    eapply list2nmem_updN; eauto.
    solve_hashmap_subset.
  Qed.


  Lemma read_array_length_ok : forall l xp Fm Fi m items nblocks,
    length l = nblocks * items_per_val ->
    (Fm * rep xp items)%pred (list2nmem m) ->
    (Fi * arrayN (@ptsto _ addr_eq_dec _) 0 l)%pred (list2nmem items) ->
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
    (Fi ✶ arrayN (@ptsto _ addr_eq_dec _) 0 l)%pred (list2nmem items) ->
    firstn (nblocks * items_per_val) items = l.
  Proof.
    intros.
    eapply arrayN_list2nmem in H0.
    rewrite <- H; simpl in *; auto.
    exact item0.
  Qed.

  Lemma read_array_list_ok2 : forall (l : list tag) nblocks items Fi,
    length l = nblocks  ->
    (Fi ✶ arrayN (@ptsto _ addr_eq_dec _) 0 l)%pred (list2nmem items) ->
    firstn nblocks items = l.
  Proof.
    intros.
    eapply arrayN_list2nmem in H0.
    rewrite <- H; simpl in *; auto.
    exact Public.
  Qed.

  Theorem read_array_ok :
    forall lxp xp nblocks ms pr,
    {< F Fm Fi m0 sm m items l,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ length l = (nblocks * items_per_val)%nat ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * arrayN (@ptsto _ addr_eq_dec _) 0 l ]]]
    POST:bm', hm', RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
          [[ r = l ]]
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} read_array lxp xp nblocks ms.
  Proof.
    unfold read_array.
    hoare.
    eapply read_array_length_ok; eauto.
    erewrite LOG.rep_hashmap_subset; eauto.  
    subst; eapply read_array_list_ok; eauto.
    solve_hashmap_subset.
  Qed.

  Theorem ifind_array_ok :
    forall lxp xp cond ms pr,
    {< F Fm m0 sm m items,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: Fm * rep xp items ]]]
    POST:bm', hm', RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true ]] *
          [[[ items ::: arrayN_ex (@ptsto _ addr_eq_dec _) items (fst st) * (fst st) |-> (snd st) ]]] )
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} ifind_array lxp xp cond ms.
  Proof.
    unfold ifind_array; intros.
    hoare.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    or_l; cancel.
    solve_hashmap_subset.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    or_r; cancel.
    apply list2nmem_ptsto_cancel; auto.
    solve_hashmap_subset.
  Qed.
  
  Fact eq_rect_eq : forall (a : nat) (f : nat -> Type) v1 v2 c H,
    eq_rect a f v1 c H = eq_rect a f v2 c H -> v1 = v2.
  Proof.
    intros a f v1 v2 c H.
    subst; auto.
  Qed.

  Ltac eq_rect_eq := match goal with [H : eq_rect _ _ _ _ _ = eq_rect _ _ _ _ _ |- _] =>
      apply eq_rect_eq in H;
      eapply f_equal in H;
      rewrite Rec.of_to_id in H;
      rewrite Rec.of_to_id in H
    end.

  Lemma ipack_inj : forall ra l1 l2,
    items_valid ra l1 ->
    items_valid ra l2 ->
    ipack l1 =ipack l2 -> l1 = l2.
  Proof.
    unfold items_valid.
    intros ra.
    generalize (RALen ra) as r; intro r; destruct r.
    intros; subst; simpl in *; intuition.
    rewrite length_nil with (l := l2); auto.
    rewrite length_nil with (l := l1); auto.
    induction r; intros; intuition.
    simpl in *; rewrite plus_0_r in *.
    rewrite ipack_one in *; auto.
    rewrite ipack_one in *; auto.
    match goal with [H : _::_ = _::_ |- _] => inversion H; clear H end.
    unfold block2val, word2val, eq_rec_r, eq_rec in *.
    simpl in *.
    eq_rect_eq; auto; unfold Rec.well_formed; simpl; intuition.
    repeat match goal with
      [ lx : itemlist,
        Hl : length ?lx = _,
        H : context [ipack ?lx] |- _] =>
        erewrite <- firstn_skipn with (l := lx) (n := items_per_val) in H;
        erewrite ipack_app with (na := 1) in H;
        [> erewrite <- firstn_skipn with (l := lx) | ];
        [> erewrite ipack_one with (l := firstn _ _) in H | ]
    end; simpl in *; try rewrite plus_0_r in *.
    match goal with [H: _::_ = _::_ |- _ ] => inversion H end.
    unfold block2val, word2val, eq_rec_r, eq_rec in *.
    simpl in *.
    eq_rect_eq.
    f_equal; eauto.
    apply IHr; intuition.
    all : repeat (
          auto || lia || split  ||
          unfold item in *      ||
          rewrite skipn_length  ||
          apply forall_skipn    ||
          apply forall_firstn   ||
          apply firstn_length_l ).
  Qed.

  Hint Extern 1 ({{_|_}} Bind (get_array _ _ _ _) _) => apply get_array_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (put_array _ _ _ _ _) _) => apply put_array_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (ifind_array _ _ _ _) _) => apply ifind_array_ok : prog.

  (* If two arrays are in the same spot, their contents have to be equal *)
  Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.

  Theorem rep_inj : forall F1 F2 l1 l2 ra m,
    (F1 * rep ra l1)%pred m -> (F2 * rep ra l2)%pred m -> l1 = l2.
  Proof.
    intros.
    unfold rep in *.
    repeat match goal with
      [ H : (_ * (exis _))%pred _ |- _ ] => destruct_lift H
      end.
    match goal with
      [ H : context[synced_list _] |- _] =>  eapply arrayN_unify', synced_list_inj in H
    end.
    3: apply H0.    
    apply combine_eq in H; cleanup; intuition.
    eapply ipack_inj; eauto.
    repeat rewrite ipack_length.
    f_equal.
    unfold items_valid in *; intuition.
    unfold item in *.
    setoid_rewrite H4; setoid_rewrite H6; auto.
    repeat rewrite ipack_length.
    f_equal.
    unfold items_valid in *; intuition.
    setoid_rewrite H4; setoid_rewrite H6; auto.
    apply repeat_length.
    repeat rewrite synced_list_length.
    setoid_rewrite combine_length_eq; auto.
    repeat rewrite repeat_length.
    cleanup.
    repeat rewrite ipack_length.
    f_equal.
    unfold items_valid in *; intuition.
    setoid_rewrite H4; setoid_rewrite H6; auto.
    all: apply repeat_length.
  Qed.

  Lemma items_wellformed : forall F xp l m,
    (F * rep xp l)%pred m -> Forall Rec.well_formed l.
  Proof.
    unfold rep, items_valid; intuition.
    destruct_lift H; auto.
  Qed.

  Lemma items_wellformed_pimpl : forall xp l,
    rep xp l =p=> [[ Forall Rec.well_formed l ]] * rep xp l.
  Proof.
    unfold rep, items_valid; cancel.
  Qed.

  Lemma item_wellformed : forall F xp m l i,
    (F * rep xp l)%pred m -> Rec.well_formed (selN l i item0).
  Proof.
    intros.
    destruct (lt_dec i (length l)).
    apply Forall_selN; auto.
    eapply items_wellformed; eauto.
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




Module LogRecArrayCache (RA : RASig).

  Module LRA := LogRecArray RA.
  Module Defs := LRA.Defs.
  Import RA LRA.Defs.

  Module Cache := FMapAVL.Make(Nat_as_OT).
  Module CacheDefs := MapDefs Nat_as_OT Cache.
  Definition Cache_type := Cache.t item.
  Module M := MapMem Nat_as_OT Cache.
  Definition cache0 : Cache_type := Cache.empty item.

  Definition cache_ptsto i (v : item) : @pred _ addr_eq_dec _ :=
    ( i |-> v \/ emp )%pred.

  Definition cache_rep (items : itemlist) (c : Cache_type) :=
     arrayN cache_ptsto 0 items (M.mm _ c).

  Definition rep xp (items : itemlist) c :=
    ( LRA.rep xp items * [[ cache_rep items c ]] )%pred.

  Definition get lxp xp ix cache ms :=
    match Cache.find ix cache with
    | Some v =>
      Ret ^(cache, ms, v)
    | None =>
      let^ (ms, v) <- LRA.get lxp xp ix ms;;
      Ret ^(Cache.add ix v cache, ms, v)
    end.

  Definition put lxp xp ix item cache ms :=
    ms <- LRA.put lxp xp ix item ms;;
    Ret ^(Cache.add ix item cache, ms).

  Definition read := LRA.read.
  Definition write := LRA.write.
  Definition init := LRA.init.
  Definition ifind := LRA.ifind.

  Definition get_array lxp xp ix cache ms :=
    r <- get lxp xp ix cache ms;;
    Ret r.

  Definition put_array lxp xp ix item cache ms :=
    r <- put lxp xp ix item cache ms;;
    Ret r.

  Definition read_array lxp xp nblocks ms :=
    r <- read lxp xp nblocks ms;;
    Ret r.

  Definition ifind_array lxp xp cond ms :=
    r <- ifind lxp xp cond ms;;
    Ret r.

  Definition read_ok := LRA.read_ok.

  Definition write_ok := LRA.write_ok.

  Definition init_ok := LRA.init_ok.

  Definition ifind_ok := LRA.ifind_ok.

  Hint Extern 1 ({{_|_}} Bind (read _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.

  Lemma item_wellformed : forall F xp m i l cache,
    (F ✶ rep xp l cache)%pred m ->
    Rec.well_formed (selN l i item0).
  Proof.
    unfold rep.
    intros.
    destruct_lifts.
    eauto using LRA.item_wellformed.
  Qed.

  Lemma items_length_ok_pimpl : forall xp l cache,
    rep xp l cache =p=>
    [[ length l = (RALen xp * items_per_val)%nat ]] ✶ rep xp l cache.
  Proof.
    unfold rep.
    intros xp l c m H.
    rewrite LRA.items_length_ok_pimpl in H.
    pred_apply.
    cancel.
  Qed.

  Lemma xform_rep : forall xp l c,
    crash_xform (rep xp  l c) <=p=> rep xp l c.
  Proof.
    unfold rep.
    intros.
    xform_norm.
    rewrite LRA.xform_rep.
    split; cancel.
  Qed.

  Lemma cache_rep_empty : forall l,
    cache_rep l (Cache.empty _).
  Proof.
    unfold cache_rep, M.mm.
    intro l. generalize 0. revert l.
    induction l; intros.
    intro; auto.
    simpl. unfold_sep_star.
    repeat exists (M.mm _ (Cache.empty _)).
    intuition.
    cbv. intro. repeat deex. congruence.
    right.
    intro; auto.
  Qed.

  Lemma rep_clear_cache: forall xp items cache,
    rep xp items cache =p=> rep xp items cache0.
  Proof.
    unfold rep. cancel.
    apply cache_rep_empty.
  Qed.

  Lemma arrayN_cache_ptsto_oob: forall l i m x,
    arrayN (cache_ptsto) x l m -> i >= length l + x \/ i < x -> m i = None.
  Proof.
    induction l; cbn; intros; auto.
    unfold sep_star in H.
    rewrite sep_star_is in H.
    unfold sep_star_impl in H.
    repeat deex.
    all: eapply mem_union_sel_none.
    all : solve [
      cbv in H2; intuition auto; apply H3; omega |
      eapply IHl; eauto; omega].
  Qed.

  Lemma cache_rep_some : forall items i cache v d,
    Cache.find i cache = Some v ->
    i < length items ->
    cache_rep items cache ->
    v = selN items i d.
  Proof.
    unfold cache_rep.
    intros items i cache v d.
    change (Cache.find i cache) with (M.mm _ cache i).
    generalize (M.mm item cache).
    clear cache.
    intros.
    eapply isolateN_fwd in H1; eauto.
    autorewrite with core in *.
    unfold cache_ptsto in H1 at 2.
    eapply pimpl_trans in H1.
    2 : rewrite sep_star_assoc, sep_star_comm, sep_star_assoc; reflexivity.
    2 : reflexivity.
    unfold sep_star in H1.
    rewrite sep_star_is in H1.
    unfold sep_star_impl, or, ptsto, emp in H1.
    intuition repeat deex.
    erewrite mem_union_addr in H by eauto.
    inversion H. eauto.
    rewrite mem_union_sel_none in H; try congruence.
    apply mem_union_sel_none.
    eapply arrayN_cache_ptsto_oob; eauto. omega.
    eapply arrayN_cache_ptsto_oob; eauto.
    rewrite firstn_length_l; omega.
  Qed.

  Lemma cache_rep_add : forall items i cache d,
    i < length items ->
    cache_rep items cache ->
    cache_rep items (Cache.add i (selN items i d) cache).
  Proof.
    unfold cache_rep in *.
    intros.
    rewrite M.mm_add_upd.
    destruct (M.mm _ cache i) eqn:?.
    eapply cache_rep_some in H0 as ?; eauto.
    rewrite Mem.upd_nop; eauto.
    rewrite Heqo. f_equal. eauto.
    generalize dependent (M.mm _ cache). clear cache.
    intros.
    eapply arrayN_mem_upd_none; eauto.
    edestruct arrayN_except as [H' _]; eauto; apply H' in H0; clear H'.
    unfold sep_star in *.
    rewrite sep_star_is in *.
    unfold sep_star_impl in *.
    repeat deex.
    apply mem_union_none_sel in Heqo.
    cbv [cache_ptsto or ptsto] in *.
    intuition try congruence.
    apply emp_empty_mem_only in H5. subst.
    rewrite mem_union_empty_mem'. auto.
    cbv [cache_ptsto ptsto or].
    left.
    intuition (destruct addr_eq_dec); eauto; congruence.
  Unshelve.
    exact item0.
  Qed.

  Lemma cache_ptsto_upd : forall i v0 v m,
    cache_ptsto i v0 m -> cache_ptsto i v (Mem.upd m i v).
  Proof.
    cbv [cache_ptsto or].
    intros.
    left.
    intuition auto.
    pose proof (@ptsto_upd _ addr_eq_dec _ i v v0 emp).
    eapply pimpl_trans; try apply H; try pred_apply; cancel.
    pose proof (@ptsto_upd_disjoint _ addr_eq_dec _ emp i v).
    eapply pimpl_trans; try apply H; try pred_apply; try cancel.
    cbv in *; auto.
  Qed.

  Lemma cache_rep_updN : forall items cache i v,
    i < length items ->
    cache_rep items cache ->
    cache_rep (updN items i v) (Cache.add i v cache).
  Proof.
    unfold cache_rep in *.
    intros.
    rewrite M.mm_add_upd.
    generalize dependent (M.mm _ cache). clear cache.
    intros.
    edestruct arrayN_isolate as [H' _]; eauto; apply H' in H0; clear H'.
    edestruct arrayN_isolate as [_ H']; [| apply H'; clear H'].
    rewrite length_updN; eauto.
    simpl in *.
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    revert H0.
    unfold_sep_star.
    intuition repeat deex.
    assert (mem_disjoint m0 (Mem.upd m3 i v)).
    cbv [cache_ptsto or ptsto] in H6.
    cbv [mem_disjoint Mem.upd] in *.
    intuition repeat deex.
    destruct addr_eq_dec; subst; eauto 10.
    destruct addr_eq_dec; subst; eauto 10.
    erewrite arrayN_cache_ptsto_oob in H6; eauto; try congruence.
    rewrite firstn_length_l; omega.
    apply mem_disjoint_union in H0 as ?.
    assert (mem_disjoint (Mem.upd m3 i v) m2).
    cbv [cache_ptsto or ptsto] in H6.
    cbv [mem_disjoint Mem.upd] in *.
    intuition repeat deex.
    destruct addr_eq_dec; subst; eauto 10.
    destruct addr_eq_dec; subst; eauto 10.
    erewrite arrayN_cache_ptsto_oob in H9; eauto; try congruence; omega.
    repeat eexists; try eapply cache_ptsto_upd; eauto.
    rewrite mem_union_comm with (m1 := m0) by auto.
    repeat rewrite <- mem_union_upd.
    f_equal.
    apply mem_union_comm, mem_disjoint_comm; auto.
    apply mem_disjoint_mem_union_split_l; auto.
    apply mem_disjoint_comm.
    eapply mem_disjoint_union_2.
    apply mem_disjoint_comm.
    eauto.
  Unshelve. all : eauto.
  Qed.

  Theorem get_array_ok :
    forall lxp xp ix cache ms pr,
    {< F Fm m0 sm m items,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ ix < length items ]] *
          [[[ m ::: Fm * rep xp items cache ]]]
    POST:bm', hm', RET:^(cache', ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm' *
          [[[ m ::: Fm * rep xp items cache' ]]] *
          [[ r = selN items ix item0 ]]
    CRASH:bm', hm', exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} get_array lxp xp ix cache ms.
  Proof.
    unfold get_array, get, rep.
    hoare.
    all: try erewrite LOG.rep_hashmap_subset; eauto.
    all: solve_hashmap_subset.
    all: eauto using cache_rep_some, cache_rep_add.
  Qed.

  Theorem put_array_ok :
    forall lxp xp ix e cache ms pr,
    {< F Fm Fi m0 sm m items e0,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items cache ]]] *
          [[[ items ::: Fi * (ix |-> e0) ]]] 
    POST:bm', hm', RET:^(cache', ms') exists m' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm bm' hm' *
          [[ items' = updN items ix e ]] *
          [[[ m' ::: Fm * rep xp items' cache' ]]] *
          [[[ items' ::: Fi * (ix |-> e) ]]] 
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} put_array lxp xp ix e cache ms.
  Proof.
    unfold put_array, put, rep.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    erewrite LOG.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    pred_apply; cancel.
    eapply cache_rep_updN; eauto.
    eapply list2nmem_ptsto_bound; eauto.
    eapply list2nmem_updN; eauto.
    solve_hashmap_subset.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (get_array _ _ _ _ _) _) => apply get_array_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (put_array _ _ _ _ _ _) _) => apply put_array_ok : prog.

  Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.

End LogRecArrayCache.

