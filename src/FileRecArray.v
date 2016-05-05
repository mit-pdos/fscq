Require Import Eqdep_dec Arith Omega List ListUtils Rounding Psatz.
Require Import Word WordAuto AsyncDisk Pred PredCrash GenSepN Array SepAuto.
Require Import Rec Prog BasicProg Hoare RecArrayUtils Log.
Require Import ProofIrrelevance.
Require Import Inode BFile MemMatch.
Import ListNotations EqNotations.

Set Implicit Arguments.


Module Type FileRASig.

  Parameter itemtype : Rec.type.
  Parameter items_per_val : nat.
  Parameter blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).

End FileRASig.



Module FileRecArray (FRA : FileRASig).

  (* Transform simplified file-based RecArray sig to general RASig *)
  Module RA <: RASig.

    Definition xparams := BFILE.bfile.
    Definition RAStart := fun (_ : xparams) => 0.
    Definition RALen := fun f => length (BFILE.BFData f).
    Definition xparams_ok := fun (_ : xparams) => True.

    Definition itemtype := FRA.itemtype.
    Definition items_per_val := FRA.items_per_val.
    Definition blocksz_ok := FRA.blocksz_ok.

    Definition RAData f := (BFILE.BFData f).
    Definition RAAttr f := (BFILE.BFAttr f).
  End RA.


  Module Defs := RADefs RA.
  Import RA Defs.

  Definition items_valid f (items : itemlist) :=
    length items = (RALen f) * items_per_val /\
    Forall Rec.well_formed items.


  (** rep invariant *)
  Definition rep f (items : itemlist) :=
    ( exists vl, [[ vl = ipack items ]] *
      [[ items_valid f items ]] *
      arrayN 0 (synced_list vl))%pred.

  Definition get T lxp ixp inum ix ms rx : prog T :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- BFILE.read_array lxp ixp inum 0 bn ms;
    rx ^(ms, selN_val2block v off).

  Definition put T lxp ixp inum ix item ms rx : prog T :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- BFILE.read_array lxp ixp inum 0 bn ms;
    let v' := block2val_updN_val2block v off item in
    ms <- BFILE.write_array lxp ixp inum 0 bn v' ms;
    rx ms.

  (* extending one block and put item at the first entry *)
  Definition extend T lxp bxp ixp inum item ms rx : prog T :=
    let v := block2val (updN block0 0 item) in
    let^ (ms, r) <- BFILE.grow lxp bxp ixp inum v ms;
    rx ^(ms, r).

  Definition readall T lxp ixp inum ms rx : prog T :=
    let^ (ms, nr) <- BFILE.getlen lxp ixp inum ms;
    let^ (ms, r) <- BFILE.read_range lxp ixp inum 0 nr iunpack nil ms;
    rx ^(ms, r).

  Definition init T lxp bxp ixp inum ms rx : prog T :=
    let^ (ms, nr) <- BFILE.getlen lxp ixp inum ms;
    ms <- BFILE.shrink lxp bxp ixp inum nr ms;
    rx ms.

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  (* find the first item that satisfies cond *)
  Definition ifind T lxp ixp inum (cond : item -> addr -> bool) ms rx : prog T :=
    let^ (ms, nr) <- BFILE.getlen lxp ixp inum ms;
    let^ (ms) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi crash m0 m flist f items ilist frees ]
    Loopvar [ ms ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
      [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[[ RAData f ::: rep f items ]]] *
      [[ forall ix, ix < i * items_per_val ->
                    cond (selN items ix item0) ix = false ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- BFILE.read_array lxp ixp inum 0 i ms;
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


  Theorem get_ok : forall lxp ixp bxp inum ix ms,
    {< F Fm Fi m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[ ix < length items ]] *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
          [[ r = selN items ix item0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} get lxp ixp inum ix ms.
  Proof.
    unfold get, rep.
    safestep.

    (* [rewrite selN_val2block_equiv] somewhere *)
    rewrite synced_list_length, ipack_length.
    apply div_lt_divup; auto.
    subst; rewrite synced_list_selN; simpl.

    safestep.
    erewrite selN_val2block_equiv.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
  Qed.


  Theorem put_ok : forall lxp ixp bxp inum ix e ms,
    {< F Fm Fi m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[ ix < length items /\ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:ms' exists m' flist' f',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist frees) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' (updN items ix e) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} put lxp ixp inum ix e ms.
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
    unfold items_valid, RALen in *; simpl; intuition.
    rewrite length_updN; auto.
  Qed.


  Lemma extend_ok_helper : forall f e items,
    items_valid f items ->
    length (BFILE.BFData f) |-> (block2val (updN block0 0 e), []) *
    arrayN 0 (synced_list (ipack items)) =p=>
    arrayN 0 (synced_list (ipack (items ++ (updN block0 0 e)))).
  Proof.
    intros.
    unfold items_valid, RALen in *; intuition.
    erewrite ipack_app, synced_list_app by eauto.
    rewrite arrayN_app, Nat.add_0_l; cancel.
    rewrite synced_list_length, ipack_length.
    substl (length items); rewrite divup_mul; auto.
    assert (length (synced_list (ipack (updN block0 O e))) = 1).
    rewrite synced_list_length, ipack_length.
    rewrite block0_repeat, length_updN, repeat_length, divup_same; auto.

    rewrite arrayN_ptsto_selN_0; auto.
    rewrite synced_list_selN; unfold ipack.
    erewrite selN_map, list_chunk_spec; simpl.
    rewrite setlen_exact; eauto.
    rewrite length_updN, block0_repeat, repeat_length; auto.
    setoid_rewrite list_chunk_length.
    rewrite length_updN, block0_repeat, repeat_length, divup_same; auto.
    Unshelve. exact $0.
  Qed.

  Lemma extend_item_valid : forall f e items,
    Rec.well_formed e ->
    items_valid f items ->
    items_valid {| BFILE.BFData := BFILE.BFData f ++ [(block2val (updN block0 0 e), [])];
                   BFILE.BFAttr := BFILE.BFAttr f |}  (items ++ (updN block0 0 e)).
  Proof.
    unfold items_valid, RALen in *; intuition; simpl.
    repeat rewrite app_length; simpl.
    rewrite block0_repeat, length_updN, repeat_length.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l; omega.
    apply Forall_append; auto.
    apply Forall_updN; auto.
    rewrite block0_repeat.
    apply Forall_repeat.
    apply item0_wellformed.
  Qed.

  Theorem extend_ok : forall lxp ixp bxp inum e ms,
    {< F Fm Fi m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET: ^(ms', r) exists m',
          [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
          [[ r = true  ]] * exists flist' f' ilist' frees',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' (items ++ (updN block0 0 e)) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} extend lxp bxp ixp inum e ms.
  Proof.
    unfold extend, rep.
    prestep. norm. cancel. intuition. eauto. eauto. eauto.
    safestep.

    or_l; safecancel.
    or_r; norm; [ cancel | intuition; eauto ].
    simpl; pred_apply; norm; [ | intuition ].
    cancel; apply extend_ok_helper; auto.
    apply extend_item_valid; auto.
  Qed.


  Theorem readall_ok : forall lxp ixp bxp inum ms,
    {< F Fm Fi m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
          [[ r = items ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} readall lxp ixp inum ms.
  Proof.
    unfold readall, rep.
    safestep.
    step.

    rewrite synced_list_length, ipack_length; subst.
    unfold items_valid in *; intuition.
    substl (length items); rewrite divup_mul; auto.

    step.
    subst; rewrite synced_list_map_fst.
    unfold items_valid, RALen in *; intuition.
    erewrite iunpack_ipack_firstn; eauto.
    rewrite firstn_oob; auto.
    substl (length items); auto.
  Qed.


  Theorem init_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist f ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms' exists m' flist' f' ilist' frees',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: emp ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init lxp bxp ixp inum ms.
  Proof.
    unfold init, rep.
    hoare.

    subst; rewrite Nat.sub_diag; simpl.
    unfold list2nmem; simpl.
    apply emp_empty_mem.
  Qed.


  Theorem ifind_ok : forall lxp bxp ixp inum cond ms,
    {< F Fm Fi m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
        ( [[ r = None /\ forall i, i < length items ->
                         cond (selN items i item0) i = false  ]]
          \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true
                         /\ (fst st) < length items
                         /\ snd st = selN items (fst st) item0 ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} ifind lxp ixp inum cond ms.
  Proof.
    unfold ifind, rep.
    safestep.
    safestep. auto. auto. eauto.
    safestep.
    eapply ifind_length_ok; eauto.
    safestep.

    unfold items_valid in *; intuition.
    or_r; cancel.
    replace p_2 with (snd (p_1, p_2)) by auto.
    eapply ifind_block_ok_cond; eauto.
    replace p_1 with (fst (p_1, p_2)) by auto.
    eapply ifind_result_inbound; eauto.
    replace p_2 with (snd (p_1, p_2)) by auto.
    eapply ifind_result_item_ok; eauto.

    unfold items_valid, RALen in *; intuition.
    eapply ifind_block_none_progress; eauto.
    cancel.

    safestep.
    or_l; cancel.
    unfold items_valid, RALen in *; intuition.
    cancel.
    apply LOG.rep_hashmap_subset; auto.
    Unshelve.  all: try exact tt; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (get _ _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_}} progseq (put _ _ _ _ _ _) _) => apply put_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _ _ _ _) _) => apply extend_ok : prog.
  Hint Extern 1 ({{_}} progseq (readall _ _ _ _) _) => apply readall_ok : prog.
  Hint Extern 1 ({{_}} progseq (init _ _ _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} progseq (ifind _ _ _ _ _) _) => apply ifind_ok : prog.


  (** operations using array spec *)

  Definition get_array T lxp ixp inum ix ms rx : prog T :=
    r <- get lxp ixp inum ix ms;
    rx r.

  Definition put_array T lxp ixp inum ix item ms rx : prog T :=
    r <- put lxp ixp inum ix item ms;
    rx r.

  Definition extend_array T lxp bxp ixp inum item ms rx : prog T :=
    r <- extend lxp bxp ixp inum item ms;
    rx r.

  Definition ifind_array T lxp ixp inum cond ms rx : prog T :=
    r <- ifind lxp ixp inum cond ms;
    rx r.

  Theorem get_array_ok : forall lxp ixp bxp inum ix ms,
    {< F Fm Fi Fe m0 m flist f items e ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]] *
          [[[ items ::: Fe * ix |-> e ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
          [[ r = e ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} get_array lxp ixp inum ix ms.
  Proof.
    unfold get_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    subst; apply eq_sym.
    eapply list2nmem_sel; eauto.
  Qed.


  Theorem put_array_ok : forall lxp ixp bxp inum ix e ms,
    {< F Fm Fi Fe m0 m flist f items e0 ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]] *
          [[[ items ::: Fe * ix |-> e0 ]]]
    POST:hm' RET:ms' exists m' flist' f' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist frees) ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' items' ]]] *
          [[[ items' ::: Fe * ix |-> e ]]] *
          [[ items' = updN items ix e ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} put_array lxp ixp inum ix e ms.
  Proof.
    unfold put_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    eapply list2nmem_updN; eauto.
  Qed.

  Theorem extend_array_ok : forall lxp bxp ixp inum e ms,
    {< F Fm Fi Fe m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]] *
          [[[ items ::: Fe ]]]
    POST:hm' RET:^(ms', r) exists m',
          [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
          [[ r = true  ]] * exists flist' f' items' ilist' frees',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
          [[[ flist' ::: (Fi * inum |-> f') ]]] *
          [[[ RAData f' ::: rep f' items' ]]] *
          [[[ items' ::: Fe * (length items) |-> e *
                arrayN (length items + 1) (repeat item0 (items_per_val - 1)) ]]] *
          [[ items' = items ++ (updN block0 0 e)  ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} extend_array lxp bxp ixp inum e ms.
  Proof.
    unfold extend_array.
    hoare.
    or_r; cancel.

    rewrite block0_repeat.
    replace (updN (repeat item0 items_per_val) 0 e) with
            ([e] ++ (repeat item0 (items_per_val - 1))).
    replace (length items + 1) with (length (items ++ [e])).
    rewrite app_assoc.
    apply list2nmem_arrayN_app.
    apply list2nmem_app; auto.
    rewrite app_length; simpl; auto.
    rewrite updN_0_skip_1 by (rewrite repeat_length; auto).
    rewrite skipn_repeat; auto.
  Qed.


  Theorem ifind_array_ok : forall lxp bxp ixp inum cond ms,
    {< F Fm Fi m0 m flist f items ilist frees,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[[ RAData f ::: rep f items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
        ( [[ r = None    /\ forall i, i < length items ->
                            cond (selN items i item0) i = false ]] \/
          exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true ]] *
          [[[ items ::: arrayN_ex items (fst st) * (fst st) |-> (snd st) ]]] )
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} ifind_array lxp ixp inum cond ms.
  Proof.
    unfold ifind_array; intros.
    hoare.
    or_r; cancel.
    apply list2nmem_ptsto_cancel; auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (get_array _ _ _ _ _) _) => apply get_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (put_array _ _ _ _ _ _) _) => apply put_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend_array _ _ _ _ _ _) _) => apply extend_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (ifind_array _ _ _ _ _) _) => apply ifind_array_ok : prog.

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


  (* equality of items given the rep invariant *)

  Definition unpack blocks := fold_left iunpack blocks nil.

  Definition pack_unpack_cond (items : list item) :=
    Forall Rec.well_formed items /\ exists nr, length items = nr * items_per_val.

  Lemma pack_unpack_id : forall items,
    pack_unpack_cond items ->
    unpack (ipack items) = items.
  Proof.
    unfold pack_unpack_cond; intuition.
    destruct H1.
    eapply iunpack_ipack; eauto.
  Qed.

  Lemma ipack_injective :
    cond_injective (ipack) (pack_unpack_cond).
  Proof.
    eapply cond_left_inv_inj with (f' := unpack) (PB := fun _ => True).
    unfold cond_left_inverse; intuition.
    apply pack_unpack_id; auto.
  Qed.

  Lemma synced_list_injective :
    cond_injective (synced_list) (fun _ => True).
  Proof.
    eapply cond_left_inv_inj with (f' := map fst) (PB := fun _ => True).
    unfold cond_left_inverse; intuition.
    apply synced_list_map_fst; auto.
  Qed.

  Lemma rep_items_eq : forall m f vs1 vs2,
    rep f vs1 m ->
    rep f vs2 m ->
    vs1 = vs2.
  Proof.
    unfold rep, items_valid; intros.
    destruct_lift H; destruct_lift H0; subst.
    apply ipack_injective; unfold pack_unpack_cond; eauto.
    apply synced_list_injective; auto.
    eapply arrayN_list_eq; eauto.
  Qed.

  Lemma xform_rep : forall f vs,
    crash_xform (rep f vs) =p=> rep f vs.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite crash_xform_arrayN_synced.
    cancel.
  Qed.

  Lemma file_crash_rep : forall f f' vs,
    BFILE.file_crash f f' ->
    rep f vs (list2nmem (BFILE.BFData f)) ->
    rep f' vs (list2nmem (BFILE.BFData f')).
  Proof.
    unfold rep; intros.
    destruct_lift H0; subst.
    erewrite <- BFILE.file_crash_synced with (f' := f'); eauto.
    pred_apply; cancel.
    eapply BFILE.arrayN_synced_list_fsynced; eauto.
  Qed.

  Lemma file_crash_rep_eq : forall f f' vs1 vs2,
    BFILE.file_crash f f' ->
    rep f  vs1 (list2nmem (BFILE.BFData f)) ->
    rep f' vs2 (list2nmem (BFILE.BFData f')) ->
    vs1 = vs2.
  Proof.
    intros.
    apply eq_sym.
    eapply rep_items_eq; eauto.
    eapply file_crash_rep; eauto.
  Qed.


End FileRecArray.


