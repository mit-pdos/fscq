Require Import Arith.
Require Import Bool.
Require Import Pred.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import WordAuto.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz. 
Require Import Classes.SetoidTactics.
Require Export PermCacheRangeSec PermRecArrayUtils.

Import ListNotations.

Set Implicit Arguments.


(* RecArray on raw, async disk *)

Module AsyncRecArray (RA : RASig).

  Module Defs := RADefs RA.
  Import RA Defs.

  Definition read_all xp count cs :=
    let^ (cs, r) <- PermCacheDef.read_range (RAStart xp) count cs;;
    vl <- unseal_all r;;
    Ret ^(cs, fold_left iunpack vl nil).
       
  (** write items from a given block index, 
      slots following the items will be cleared *)
  Definition write_aligned xp start (items: itemlist) cs :=
    let chunks := nopad_list_chunk items items_per_val in
    hl <- seal_all (repeat Public (length chunks)) (map block2val chunks);;
    cs <- PermCacheDef.write_range ((RAStart xp) + start) hl cs;;
    Ret cs.

  (** sync count blocks starting from start *)
  Definition sync_aligned xp start count cs :=
    cs <- PermCacheDef.sync_range ((RAStart xp) + start) count cs;;
    Ret cs.
  
  Definition items_valid xp start (items : itemlist) :=
    xparams_ok xp /\  start <= (RALen xp) /\
    Forall Rec.well_formed items /\
    length items <= (RALen xp - start) * items_per_val.

  (** rep invariant *)
  Inductive state : Type :=
  | Synced : itemlist -> state
  | Unsync : itemlist -> state
  .

  (* This rep states that there is a packed and tagged version of the itemlist *)
  Definition rep_common xp start items (vl: list tagged_block)
             (vsl : list (list tagged_block)) :=
    items_valid xp start items /\
    vl = combine (repeat Public (length (ipack items))) (ipack items)
    /\ eqlen vl vsl.

  Definition synced_array xp start items :=
    (exists (vl: list tagged_block) vsl, [[ rep_common xp start items vl vsl /\
        vsl = nils (length vl) ]] *
    arrayS ((RAStart xp ) + start) (combine vl vsl))%pred.

  Definition unsync_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl ]] *
    [[ Forall (fun vs => Forall (fun tb => fst tb = Public) vs) vsl ]] *
    arrayS ((RAStart xp ) + start) (combine vl vsl))%pred.

  Definition array_rep xp start (st : state) :=
   (match st with
    | Synced items => synced_array xp start items
    | Unsync items => unsync_array xp start items
    end)%pred.

  Definition avail_rep xp start nr : rawpred :=
    (exists vsl, [[ length vsl = nr ]] *
     [[ Forall (fun vs => Forall (fun tb => fst tb = Public) (vsmerge vs)) vsl ]] *
     arrayS ((RAStart xp) + start) vsl)%pred.

  Definition nr_blocks st :=
    match st with
    | Synced l => (divup (length l) items_per_val)
    | Unsync l => (divup (length l) items_per_val)
    end.

  Lemma items_valid_app : forall xp st a b,
    items_valid xp st (a ++ b) ->
    items_valid xp st a /\ items_valid xp st b.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.
  Qed.

  Lemma le_add_helper: forall a b c d,
    b <= d -> a + d <= c -> a + b <= c.
  Proof.
    intros; omega.
  Qed.

  Lemma le_add_le_sub : forall a b c,
    a <= c -> b <= c - a -> a + b <= c.
  Proof.
    intros. omega.
  Qed.

  Lemma items_valid_app2 : forall xp st a b,
    length b <= (roundup (length a) items_per_val - length a)
    -> items_valid xp st a
    -> Forall Rec.well_formed b
    -> items_valid xp st (a ++ b).
  Proof.
    unfold items_valid, roundup; intuition.
    pose proof (well_formed_app_iff itemtype a b); intuition.
    rewrite app_length.
    eapply le_add_helper. apply H.
    rewrite le_plus_minus_r.
    apply mult_le_compat_r.
    apply divup_le; lia.
    apply roundup_ge.
    apply items_per_val_gt_0.
  Qed.

  Lemma items_valid_app3 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st (a ++ b) -> items_valid xp (st + na) b.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.

    apply le_add_le_sub; auto.
    eapply Nat.mul_le_mono_pos_r.
    apply items_per_val_gt_0.
    rewrite <- H; omega.

    rewrite Nat.sub_add_distr.
    rewrite Nat.mul_sub_distr_r.
    apply Nat.le_add_le_sub_l.
    setoid_rewrite <- H; auto.
  Qed.

  Lemma items_valid_app4 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st a ->
    items_valid xp (st + na) b ->
    items_valid xp st (a ++ b).
  Proof.
    unfold items_valid, roundup; intuition.
    apply well_formed_app_iff; intuition.
    rewrite app_length.
    rewrite Nat.sub_add_distr in H8.
    rewrite Nat.mul_sub_distr_r in H8.
    rewrite <- H in H8.
    omega.
  Qed.

  Lemma synced_array_is : forall xp start items,
    synced_array xp start items =p=>
  arrayS ((RAStart xp) + start) (combine (combine (repeat Public (length (ipack items))) (ipack items))
                                         (nils (length (ipack items)))).
  Proof.
    unfold synced_array, rep_common; cancel; subst; auto.
    setoid_rewrite combine_length.
    rewrite min_r; auto.
    rewrite repeat_length; auto.
  Qed.

  Lemma array_rep_sync_nil : forall xp a,
    xparams_ok xp -> a <= (RALen xp) ->
    array_rep xp a (Synced nil) <=p=> emp.
  Proof.
    unfold array_rep, synced_array, rep_common; intros.
    split; cancel; subst; simpl; unfold items_valid, eqlen;
      try setoid_rewrite ipack_nil; simpl; intuition; auto.
  Qed.

  Lemma array_rep_sync_nil_emp : forall xp a,
    array_rep xp a (Synced nil) =p=> emp.
  Proof.
    unfold array_rep, synced_array, rep_common; intros.
    cancel; subst; simpl; unfold items_valid, eqlen;
      try setoid_rewrite ipack_nil; simpl; intuition; auto.
  Qed.

  Lemma array_rep_sync_nil_sep_star : forall xp a l,
    array_rep xp a (Synced l) =p=> array_rep xp a (Synced nil) * array_rep xp a (Synced l).
  Proof.
    intros.
    unfold array_rep, synced_array, rep_common, eqlen; intros.
    norm.
    eassign (@nil tagged_block).
    cancel.
    subst; repeat setoid_rewrite ipack_nil; simpl; auto;
    unfold items_valid in *; intuition.
    unfold nils; rewrite repeat_length; auto.
  Qed.

  Theorem sync_invariant_array_rep : forall xp a st,
    sync_invariant (array_rep xp a st).
  Proof.
    unfold array_rep, synced_array, unsync_array; destruct st; eauto.
  Qed.

  Theorem sync_invariant_avail_rep : forall xp a n,
    sync_invariant (avail_rep xp a n).
  Proof.
    unfold avail_rep; eauto.
  Qed.

  Hint Resolve sync_invariant_array_rep sync_invariant_avail_rep.

  Hint Rewrite list_chunk_nil ipack_nil.
  Hint Rewrite Nat.add_0_r Nat.add_0_l.
  Hint Rewrite synced_array_is.
  Hint Rewrite combine_length : lists.
  Hint Rewrite ipack_length divup_mul.

  Ltac rewrite_ignore H :=
    match type of H with
    | forall _, corr2 _ _ => idtac
    | sep_star _ _ _ => idtac
    end.

  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints core)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with core .. ];
    match type of H with
    | context [ length (list_chunk _ _ _) ] => rewrite block_chunk_length in H
    end).

  Ltac simplen' := repeat match goal with
    | [H : @eqlen _ ?T ?a ?b |- context [length ?a] ] => setoid_replace (length a) with (length b) by auto
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | rewrite_ignore H | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : @eqlen _ ?T ?l nil |- context [?l] ] => replace l with (@nil T) by eauto
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac simplen := unfold eqlen; eauto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with core lists); simpl; eauto; try omega.

  Lemma xform_synced_array : forall xp st l,
    crash_xform (synced_array xp st l) =p=> synced_array xp st l.
  Proof.
    unfold synced_array; intros.
    xform; cancel; subst.
    rewrite crash_xform_arrayN_subset_combine_nils.
    cancel.
    auto.
  Qed.

  Lemma xform_synced_rep : forall xp st l,
    crash_xform (array_rep xp st (Synced l)) =p=> array_rep xp st (Synced l).
  Proof.
    intros; simpl.
    apply xform_synced_array.
  Qed.

  Lemma xform_avail_rep : forall xp st nr,
    crash_xform (avail_rep xp st nr) =p=> avail_rep xp st nr.
  Proof.
    unfold avail_rep; intros; intros.
    xform.
    rewrite crash_xform_arrayN_subset; cancel.
    unfold possible_crash_list in *; subst; intuition.
    setoid_rewrite H.
    rewrite synced_list_length; auto.
    rewrite Forall_forall in *; intros.
    unfold possible_crash_list in *; subst; intuition.

    eapply in_selN_exists in H as Hx; cleanup.
    unfold synced_list in H4; simpl in H4.
    setoid_rewrite selN_combine in H4.
    destruct x0; cleanup.
    inversion H4.
    unfold vsmerge; simpl.
    rewrite repeat_selN.
    constructor; auto.
    assert (A0: x1 < length x).
    setoid_rewrite H1; rewrite <- synced_list_length; eauto.
    assert (A: In (selN x x1 valuset0) x). 
    eapply in_selN; auto.
    specialize H2 with (1:=A).
    rewrite Forall_forall in H2.
    specialize H3 with (1:= A0).
    eauto.
    rewrite <- synced_list_length; eauto.
    rewrite repeat_length; auto.
    Unshelve.
    exact nil.
  Qed.


  Lemma xform_avail_rep_array_rep : forall xp st nr,
    (forall l', Forall (@Rec.well_formed itemtype) l') ->
    nr * items_per_val <= (RALen xp - st) * items_per_val ->
    xparams_ok xp ->
    st <= RALen xp ->
    crash_xform (avail_rep xp st nr) =p=>
      exists l, array_rep xp st (Synced l) *
      [[ length l = (nr * items_per_val)%nat ]].
  Proof.
    unfold avail_rep; intros.
    xform.
    rewrite crash_xform_arrayN_subset; cancel;
    apply possible_crash_list_length in H4 as Hlength; subst.
    unfold possible_crash_list in *; subst; intuition.
    unfold synced_array.
    Opaque In.
    cancel.
    unfold rep_common; intuition.
    eassign (fold_left iunpack (map snd l') []).
    unfold items_valid; intuition.
    rewrite fold_left_iunpack_length.
    rewrite map_length; setoid_rewrite <- Hlength; auto.
    rewrite <- ipack_iunpack; auto.
    rewrite <- combine_map_fst_snd at 1.
    replace (map fst l') with (repeat Public (length (map snd l'))); auto.
    eapply list_selN_ext; intros.
    rewrite repeat_length; repeat rewrite map_length; auto.
    rewrite repeat_length, map_length in *.
    erewrite repeat_selN, selN_map; auto.    
    rewrite Forall_forall in *.

    assert (A0: pos < length x).
    setoid_rewrite Hlength; auto.
    assert (A: In (selN x pos valuset0) x). 
    eapply in_selN; auto.
    specialize H6 with (1:=A).
    rewrite Forall_forall in H6.
    specialize H5 with (1:= A0).
    symmetry; eauto.
    unfold eqlen.
    rewrite repeat_length; auto.
    rewrite fold_left_iunpack_length.
    rewrite map_length. setoid_rewrite Hlength; auto.
    Unshelve.
    exact Public.
  Qed.

  Lemma xform_unsync_array_avail : forall xp st l,
    crash_xform (unsync_array xp st l) =p=>
      avail_rep xp st (divup (length l) items_per_val).
  Proof.
    unfold unsync_array, avail_rep, rep_common; intros.
    xform.
    rewrite crash_xform_arrayN_subset.
    unfold possible_crash_list.
    cancel.
    rewrite combine_length_eq in *; simplen.
    rewrite <- ipack_length; auto.
    setoid_rewrite combine_length in H1; auto.
    unfold eqlen in *; rewrite min_r in H1; auto.
    rewrite synced_list_length; auto.
    rewrite repeat_length; auto.
    rewrite Forall_forall in *; intros; auto.
    eapply in_selN_exists in H as Hx; cleanup.
    unfold synced_list in H5; simpl in H5.
    setoid_rewrite selN_combine in H5.
    destruct x; cleanup.
    inversion H5.
    unfold vsmerge; simpl.
    rewrite repeat_selN.
    constructor; auto.
    
    assert (A0: x1 < length
         (combine (combine (repeat Public (length (ipack l))) (ipack l)) x0)).
    setoid_rewrite H1; rewrite <- synced_list_length; eauto.
    specialize H6 with (1:= A0).
    setoid_rewrite selN_combine in H6.
    unfold vsmerge in *; simpl in *; cleanup.
    destruct H6.
    rewrite <- H6.
    setoid_rewrite selN_combine.
    rewrite repeat_selN; simpl; auto.
    rewrite synced_list_length in *.
    rewrite <- H1 in H3.
    repeat setoid_rewrite combine_length in H3.
    apply Nat.min_glb_lt_iff in H3; cleanup.
    apply Nat.min_glb_lt_iff in H3; cleanup; auto.
    apply repeat_length.
    assert (A: In (selN x0 x1 nil) x0). 
    eapply in_selN; auto.
    repeat setoid_rewrite combine_length in A0.
    apply Nat.min_glb_lt_iff in A0; cleanup; auto.
    specialize H2 with (1:=A).
    rewrite Forall_forall in H2; eauto.
    unfold eqlen in *; auto.
    rewrite <- synced_list_length; eauto.
    rewrite repeat_length; auto.
    Unshelve.
    exact nil.
  Qed.

  Lemma array_rep_size_ok : forall m xp start st,
    array_rep xp start st m ->
    nr_blocks st <= RALen xp - start.
  Proof.
    unfold array_rep, synced_array, unsync_array, rep_common, items_valid.
    destruct st; intros; destruct_lift H; subst;
    apply divup_le; rewrite Nat.mul_comm; eauto.
  Qed.

  Lemma array_rep_size_ok_pimpl : forall xp st,
    array_rep xp 0 st =p=>
    array_rep xp 0 st * [[ nr_blocks st <= RALen xp ]].
  Proof.
    intros; unfold pimpl; intros.
    apply array_rep_size_ok in H as H1.
    pred_apply; cancel.
  Qed.

  Lemma array_rep_avail : forall xp start st,
    array_rep xp start st =p=>
    avail_rep xp start (nr_blocks st).
  Proof.
    unfold array_rep, avail_rep, synced_array, unsync_array, rep_common, eqlen, nr_blocks.
    intros; destruct st; cancel; subst; autorewrite with lists.
    setoid_rewrite combine_length; auto.
    subst; rewrite min_l; auto.
    setoid_rewrite combine_length; auto.
    subst; rewrite min_r; auto.
    rewrite ipack_length; auto.
    rewrite repeat_length; auto.
    rewrite H4; auto.
    unfold nils at 2; rewrite repeat_length; auto.
    rewrite Forall_forall; intros.
    eapply in_selN_exists in H as Hx; cleanup.
    setoid_rewrite selN_combine in H2; auto.
    unfold nils in H2.
    rewrite repeat_selN in H2.
    rewrite <- H2.
    unfold vsmerge ; simpl; constructor; auto.
    setoid_rewrite selN_combine; auto.
    rewrite repeat_selN; auto.
    repeat setoid_rewrite combine_length in H1.
    apply Nat.min_glb_lt_iff in H1; cleanup.
    apply Nat.min_glb_lt_iff in H1; cleanup; auto.
    apply repeat_length.
    setoid_rewrite combine_length in H1.
    apply Nat.min_glb_lt_iff in H1.
    destruct H1; auto.

    rewrite <- ipack_length.
    setoid_rewrite combine_length.
    rewrite Nat.min_l; simplen.
    rewrite <- H4.
    setoid_rewrite combine_length.
    rewrite min_r; simplen; auto.

    rewrite Forall_forall; intros.
    eapply in_selN_exists in H as Hx; cleanup.
    setoid_rewrite selN_combine in H3; auto.
    rewrite <- H3.
    unfold vsmerge ; simpl; constructor; auto.
    setoid_rewrite selN_combine; auto.
    rewrite repeat_selN; auto.
    repeat setoid_rewrite combine_length in H1.
    apply Nat.min_glb_lt_iff in H1; cleanup.
    apply Nat.min_glb_lt_iff in H1; cleanup; auto.
    apply repeat_length.
    rewrite Forall_forall in H2; eapply H2.
    apply in_selN.
    setoid_rewrite combine_length in H1.
    apply Nat.min_glb_lt_iff in H1; cleanup; auto.

    Grab Existential Variables.
    exact nil. exact $0. exact Public. exact $0. exact Public. exact nil.
  Qed.

  Lemma array_rep_avail_synced : forall xp start items,
    array_rep xp start (Synced items) =p=>
    avail_rep xp start (divup (length items) items_per_val).
  Proof.
    intros; apply array_rep_avail.
  Qed.

  Lemma avail_rep_split : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start nr =p=> avail_rep xp start n1 * avail_rep xp (start + n1) n2.
  Proof.
    unfold avail_rep; intros; norm.
    instantiate (2 := (firstn n1 vsl)).
    instantiate (1 := (skipn n1 vsl)).
    cancel.
    rewrite Nat.add_assoc.
    rewrite arrayN_split by auto.
    eassign n1.
    cancel.
    intuition.
    rewrite firstn_length.
    rewrite Nat.min_l; omega.
    apply forall_firstn; auto.
    rewrite skipn_length; omega.
    apply forall_skipn; auto.
  Qed.

  Lemma avail_rep_merge : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start n1 * avail_rep xp (start + n1) n2 =p=> avail_rep xp start nr.
  Proof.
    unfold avail_rep; intros; norm.
    instantiate (1 := vsl ++ vsl0).
    setoid_rewrite arrayN_app.
    rewrite Nat.add_assoc.
    cancel.
    intuition.
    rewrite app_length; omega.
    apply Forall_append; auto.
  Qed.

  Lemma helper_add_sub : forall a b c,
    b <= c -> c <= a -> a >= b + (a - c).
  Proof.
    intros; omega.
  Qed.

  Lemma helper_add_le : forall a b nb n,
    b <= nb -> n >= a + nb -> a + b <= n.
  Proof.
    intros; omega.
  Qed.

  Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.

  Lemma array_rep_synced_app : forall xp start na a b,
    length a = na * items_per_val ->
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b) =p=>
    array_rep xp start (Synced (a ++ b)).
  Proof.
    simpl; intros;
    unfold synced_array, rep_common, nils, eqlen; norm; subst; intuition.
    cancel.
    erewrite ipack_app by eauto.
    setoid_rewrite combine_length.
    repeat rewrite min_r.
    repeat rewrite app_length, Nat.add_assoc.
    repeat rewrite <- repeat_app.
    rewrite combine_app, app_length; auto.
    repeat rewrite <- repeat_app.
    rewrite combine_app, arrayN_app. repeat setoid_rewrite combine_length_eq; auto.
    repeat rewrite repeat_length;
    repeat rewrite ipack_length. 
    cancel.
    all: repeat rewrite repeat_length; auto.
    setoid_rewrite combine_length_eq; try rewrite repeat_length; auto.

    unfold items_valid, roundup in *; intuition.
    apply well_formed_app_iff; auto.
    rewrite app_length.
    eapply helper_add_le; eauto.
    rewrite Nat.sub_add_distr.
    setoid_rewrite Nat.mul_sub_distr_r at 2.
    apply helper_add_sub.
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_r; omega.
  Qed.

  Lemma array_rep_synced_app_rev :
    forall xp start na a b,
    length a = na * items_per_val ->                                
    array_rep xp start (Synced (a ++ b)) =p=>
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b).
  Proof.
    simpl; intros;
    unfold synced_array, rep_common, nils, eqlen; norm; subst; intuition;
    try rewrite repeat_length; auto.
    cancel.
    erewrite ipack_app by eauto.
    rewrite app_length, Nat.add_assoc.
    repeat rewrite <- repeat_app.
    repeat rewrite combine_app, app_length; auto.
    rewrite <- repeat_app.
    rewrite combine_app, arrayN_app. repeat setoid_rewrite combine_length_eq; auto.
    repeat rewrite repeat_length;
    repeat rewrite ipack_length.
    cancel.
    all: try apply repeat_length.
    repeat rewrite repeat_length; auto.
    rewrite repeat_length; auto.
    
    apply (@items_valid_app xp start a b H1).
    rewrite H, divup_mul by auto.
    eapply items_valid_app3; eauto.
  Qed.

  
       
    Theorem read_all_ok :
    forall xp count cs pr,
    {< F d items,
    PERM: pr
    PRE:bm, hm,
      PermCacheDef.rep cs d bm *
      [[ length items = (count * items_per_val)%nat /\
         Forall Rec.well_formed items /\ xparams_ok xp ]] *
      [[ (F * array_rep xp 0 (Synced items))%pred d ]]
    POST:bm', hm',
       RET: ^(cs, r)
          PermCacheDef.rep cs d bm' *
          [[ (F * array_rep xp 0 (Synced items))%pred d ]] *
          [[ r = items ]]
    CRASH:bm'', hm'',
      exists cs', PermCacheDef.rep cs' d bm''
    >} read_all xp count cs.
  Proof.
    unfold read_all.
    step.
    rewrite synced_array_is, Nat.add_0_r; cancel.
    rewrite ipack_length, H0, divup_mul; auto.
    repeat setoid_rewrite combine_length_eq; auto.
    all: try rewrite repeat_length; auto.
    rewrite ipack_length, H0, divup_mul; auto.
    rewrite nils_length; auto.
    rewrite ipack_length, H0, divup_mul; auto.

    step; subst.
    rewrite H14 in H4.
    apply in_map_iff in H4; cleanup.
    apply in_firstn_in in H7.
    apply in_map_iff in H7; cleanup.
    destruct x0; apply in_combine_l in H7.
    destruct t; apply in_combine_l in H7.
    apply repeat_spec in H7; subst; simpl; auto.
    step.
    step.
    rewrite H14.
    rewrite map_fst_combine.
    rewrite firstn_oob; auto.
    rewrite map_snd_combine.
    eapply iunpack_ipack; eauto.
    apply repeat_length.
    repeat setoid_rewrite combine_length_eq; auto.
    rewrite repeat_length, ipack_length, H0, divup_mul; auto.
    apply repeat_length.
    rewrite nils_length; setoid_rewrite combine_length_eq; auto.
    apply repeat_length.
    apply repeat_length.
    solve_hashmap_subset.
    Unshelve.
    unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Lemma vsupd_range_unsync_array : forall xp start items old_vs,
    items_valid xp start items ->
    eqlen old_vs (ipack items) ->
    Forall (fun vs => Forall (fun tb => fst tb = Public) (vsmerge vs)) old_vs ->
    arrayS (RAStart xp + start) (vsupd_range old_vs (combine (repeat Public (length (ipack items))) (ipack items)))
      =p=> unsync_array xp start items.
  Proof.
    intros.
    unfold vsupd_range, unsync_array, rep_common.
    safecancel.
    apply arrayN_unify.
    rewrite skipn_oob.
    rewrite app_nil_r.
    f_equal; eauto.
    
    unfold eqlen in *;
    setoid_rewrite combine_length_eq; rewrite repeat_length; auto; omega.
    auto.

    unfold eqlen in *;
    setoid_rewrite combine_length_eq; auto.
    rewrite <- H0; rewrite repeat_length, firstn_exact.
    rewrite map_length; auto.
    apply repeat_length.
    apply repeat_length.
    rewrite firstn_oob; auto.
    rewrite Forall_forall in *; intros.
    apply in_map_iff in H2; cleanup; eauto.
    unfold eqlen in *;
    setoid_rewrite combine_length_eq; rewrite repeat_length; auto; omega.
  Qed.

  Lemma vsupd_range_nopad_unsync_array : forall xp start (items : itemlist) old_vs,
    items_valid xp start items ->
    length old_vs = divup (length items) items_per_val ->
    Forall (fun vs => Forall (fun tb => fst tb = Public) (vsmerge vs)) old_vs ->
    arrayS (RAStart xp + start) (vsupd_range old_vs (combine  (repeat Public (length (nopad_ipack items))) (nopad_ipack items)))
      =p=> unsync_array xp start items.
  Proof.
    unfold vsupd_range, unsync_array, rep_common, eqlen.
    intros.
    rewrite nopad_ipack_length in *.
    rewrite firstn_oob.
    rewrite skipn_oob.
    safecancel.
    apply arrayN_unify.
    rewrite app_nil_r.
    f_equal.
    rewrite  ipack_nopad_ipack_eq, nopad_ipack_length; auto.
    simplen.
    setoid_rewrite combine_length_eq; auto.
    apply repeat_length.
    rewrite nopad_ipack_length; apply repeat_length.
    rewrite Forall_forall in *; intros.
    apply in_map_iff in H2; cleanup; eauto.
    auto.
    simplen.
    setoid_rewrite combine_length_eq; auto.
    rewrite repeat_length; omega.
    rewrite nopad_ipack_length; apply repeat_length.
    simplen.
    setoid_rewrite combine_length_eq; auto.
    rewrite repeat_length; omega.
    rewrite nopad_ipack_length; apply repeat_length.
  Qed.

  Lemma write_aligned_length_helper : forall n l,
    n <= length (map block2val (list_chunk l items_per_val item0)) ->
    n <= divup (length l) items_per_val.
  Proof.
    intros; autorewrite with lists in *.
    erewrite <- list_chunk_length; eauto.
  Qed.
  Local Hint Resolve write_aligned_length_helper.


  Theorem write_aligned_ok :
    forall xp start new cs pr,
    {< F d,
    PERM:pr   
    PRE:bm, hm,
      PermCacheDef.rep cs d bm *
      [[ items_valid xp start new ]] *
      [[ (F * avail_rep xp start (divup (length new) items_per_val))%pred d ]]
    POST:bm', hm', RET: cs
      exists d', PermCacheDef.rep cs d' bm' *
      [[ (F * array_rep xp start (Unsync new))%pred d' ]]
    XCRASH:bm'', hm'',  exists cs' d',
      PermCacheDef.rep cs' d' bm'' *
      [[ (F * avail_rep xp start (divup (length new) items_per_val)) % pred d' ]]
    >} write_aligned xp start new cs.
  Proof.
    unfold write_aligned, avail_rep.
    step.
    rewrite map_length, repeat_length; auto.
    apply repeat_spec in H; subst; auto.
    safestep.
    rewrite block_mem_subset_rep; eauto.
    eauto.
    all: apply extract_blocks_length in H13 as Hx.
    cleanup.
    cbn. simplen.
    setoid_rewrite combine_length_eq in Hx.
    rewrite repeat_length, nopad_list_chunk_length in Hx; auto.
    rewrite <- Hx; auto.
    cbn. simplen.
    rewrite H14; eauto.
    eauto.
    step.
    step.
    rewrite H14.
    erewrite <- map_length with (f:= block2val).
    replace  (map block2val (nopad_list_chunk new items_per_val)) with
        (nopad_ipack new) by auto.
    apply vsupd_range_nopad_unsync_array; auto.
    solve_hashmap_subset.
    rewrite <- H1; cancel; eauto.
    solve_hashmap_subset.
    xcrash.
    rewrite vsupd_range_length; auto.
    simplen.
    setoid_rewrite combine_length_eq in Hx; auto.
    rewrite repeat_length, nopad_list_chunk_length in Hx; auto.
    rewrite <- Hx; auto.
    rewrite repeat_length, map_length; auto.
    unfold vsupd_range.
    rewrite Forall_forall in *; intros.
    destruct x1.
    eapply in_app_iff in H5; destruct H5.
    unfold vsmerge; simpl; constructor.
    apply in_combine_l in H5.
    rewrite H14 in H5; destruct t; apply in_combine_l in H5.
    apply repeat_spec in H5; subst; simpl; auto.
    apply in_combine_r in H5; apply in_map_iff in H5; cleanup; eauto.
    eapply H10; eapply in_firstn_in; eauto.
    eapply H10; eapply in_skipn_in; eauto.
    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Lemma vssync_range_sync_array : forall xp start items count vsl,
    items_valid xp start items ->
    length items = (count * items_per_val)%nat ->
    length vsl = count ->
    arrayS (RAStart xp + start) (vssync_range (combine (combine (repeat Public (length (ipack items))) (ipack items)) vsl) count)
      =p=> synced_array xp start items.
  Proof.
    unfold synced_array, rep_common; cancel; simplen.
    unfold vssync_range.
    rewrite skipn_oob.
    rewrite app_nil_r.
    apply arrayN_unify.
    rewrite firstn_oob.
    rewrite map_fst_combine.
    unfold nils.
    all: repeat setoid_rewrite combine_length_eq; auto; simplen.
    rewrite nils_length; simplen.
  Qed.

  Lemma helper_ipack_length_eq: forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    count = length vsl.
  Proof.
    intros.
    replace (length vsl) with (length (ipack items)) by simplen.
    rewrite ipack_length; simplen.
  Qed.

  Lemma helper_ipack_length_eq': forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    length vsl = count.
  Proof.
    intros; apply eq_sym; eapply helper_ipack_length_eq; eauto.
  Qed.

  Local Hint Resolve helper_ipack_length_eq helper_ipack_length_eq'.
  Hint Rewrite ipack_length.

  Lemma vssync_range_pimpl : forall xp start items vsl m,
    length items = (length vsl) * items_per_val ->
    m <= (length vsl) ->
    arrayS (RAStart xp + start) (vssync_range (combine (combine (repeat Public (length (ipack items))) (ipack items)) vsl) m) =p=>
    arrayS (RAStart xp + start) (combine (combine (repeat Public (length (ipack items))) (ipack items)) (repeat nil m ++ skipn m vsl)).
  Proof.
    intros.
    unfold vssync_range, ipack.
    apply arrayN_unify.
    setoid_rewrite skipn_combine.
    rewrite <- combine_app.
    f_equal.
    rewrite <- firstn_map_comm.
    setoid_rewrite map_fst_combine.
    rewrite firstn_skipn; auto.
    all: repeat setoid_rewrite combine_length_eq; auto; simplen.
    apply min_l.
    repeat setoid_rewrite combine_length_eq; auto; simplen.
  Qed.


  Theorem sync_aligned_ok :
    forall xp start count cs pr,
    {< F d0 d items,
    PERM:pr
    PRE:bm, hm,
      PermCacheDef.synrep cs d0 d bm * 
      [[ (F * array_rep xp start (Unsync items))%pred d ]] *
      [[ length items = (count * items_per_val)%nat ]] *
      [[ items_valid xp start items /\ sync_invariant F ]]
    POST:bm', hm', RET: cs
      exists d', PermCacheDef.synrep cs d0 d' bm' *
      [[ (F * array_rep xp start (Synced items))%pred d' ]]
    CRASH:bm'', hm'',  exists cs', PermCacheDef.rep cs' d0 bm''
    >} sync_aligned xp start count cs.
  Proof.
    unfold sync_aligned.
    prestep. norml.
    unfold unsync_array, rep_common in *; destruct_lifts.

    safecancel.
    eassign F_; cancel; eauto.
    eauto.
    unfold eqlen in *; setoid_rewrite combine_length_eq; simplen.
    rewrite <- H12.
    setoid_rewrite combine_length_eq; simplen.
    auto.
    auto.

    step.
    step.
    apply vssync_range_sync_array; eauto.
    unfold eqlen in *; rewrite <- H12.
    setoid_rewrite combine_length_eq; simplen.
    solve_hashmap_subset.
    rewrite <- H1; cancel; eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (read_all _ _ _) _) => apply read_all_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write_aligned _ _ _ _) _) => apply write_aligned_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (sync_aligned _ _ _ _) _) => apply sync_aligned_ok : prog.
End AsyncRecArray.

