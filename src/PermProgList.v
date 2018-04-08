Require Import Pred Mem Word Arith.
Require Import Nomega NArith Omega List ListUtils.
Require Import Morphisms FunctionalExtensionality ProofIrrelevance.
Require Export PermProgLoop.

Import ListNotations.

Set Implicit Arguments.

Definition hash_list h values :=
  let^ (hash) <- ForEach item items_rest values
  Hashmap hm'
  Ghost [ l crash ]
  Loopvar [ hash ]
  Invariant
    exists items_prefix,
    [[ values = items_prefix ++ items_rest ]] *
    [[ hash_list_rep (rev items_prefix ++ l) hash hm' ]]
  OnCrash crash
  Begin
    hash <- Hash2 item hash;;
    Ret ^(hash)
  Rof ^(h);;
  Ret hash.


Definition seal_all (tl: list tag) (bl: list block):=
  let^ (l) <- ForN i < length bl
  Blockmem bm
  Ghost [ crash ]
  Loopvar [ hl ]
  Invariant
    [[ extract_blocks bm (rev hl) = firstn i (combine tl bl) ]] *
    [[ handles_valid bm (rev hl) ]]               
  OnCrash
    crash
  Begin
    h <- Seal (selN tl i Public) (selN bl i $0);;
    Ret ^(h::hl)
  Rof ^(nil);;
  Ret (rev l).

     
Definition unseal_all (hl: list handle) :=
  let^ (bl) <- ForN i < length hl
  Blockmem bm
  Ghost [ crash ]
  Loopvar [ tbl ]
  Invariant
    [[ rev (tbl) = map snd (extract_blocks bm (firstn i hl)) ]]
  OnCrash
    crash
  Begin
    tb <- Unseal (selN hl i 0);;
    Ret ^(tb::tbl)
  Rof ^((nil: list block));;
  Ret (rev bl).


Theorem seal_all_ok :
    forall tl bl pr,
    {!< F,
    PERM: pr                      
    PRE:bm, hm,
        F * [[ length tl = length bl ]] *
        [[ forall t, In t tl -> can_access pr t ]]
    POST:bm', hm', RET: r
        F * [[ extract_blocks bm' r = combine tl bl ]] *
        [[ handles_valid bm' r ]]                
    CRASH:bm'', hm_crash,
        false_pred (* Can't crash *)              
    >!} seal_all tl bl.
Proof.
  unfold seal_all; step.
  unfold handles_valid; auto.
  safestep.
  apply H3.
  apply in_selN with (n:= m).
  omega.

  step.
  step.
  rewrite extract_blocks_app.
  rewrite extract_blocks_upd_not_in.
  rewrite H5.
  simpl; rewrite upd_eq; auto.
  destruct (combine tl bl) eqn:D.
  apply length_zero_iff_nil in D.
  rewrite combine_length_eq in D; auto.
  subst; omega.
  rewrite <- D.
  rewrite <- selN_combine.
  rewrite <- firstn_S_selN.
  rewrite D; simpl; auto.
  setoid_rewrite combine_length_eq; omega.
  auto.
  unfold not; intros.
  unfold handles_valid, handle_valid in H12; eapply Forall_forall in H12; eauto;
  cleanup; congruence.
  apply Forall_app.      
  apply handles_valid_upd; auto.
  unfold handle_valid; eexists; apply upd_eq; eauto.
  solve_hashmap_subset.
  unfold false_pred; cancel.

  step.
  step.
  rewrite H, <- H4.
  erewrite <- combine_length_eq, firstn_exact; auto.
  solve_hashmap_subset.
  eassign (false_pred (AT:= addr)(AEQ:=addr_eq_dec)(V:=valuset))%pred;
  unfold false_pred; cancel.

  Unshelve.
  exact tt.
Qed.
     
     
Theorem hash_list_ok :
  forall h values pr,
  {!< F l,
  PERM:pr   
  PRE:bm, hm,
    F * [[ hash_list_rep l h hm ]]
  POST:bm', hm', RET:h'
    F * [[ hash_list_rep (rev values ++ l) h' hm' ]]
  CRASH:bm'', hm'',
    false_pred (* Can't crash *)
  >!} hash_list h values.
Proof.
  unfold hash_list.
  step.
  rewrite app_nil_l; reflexivity.
  rewrite app_nil_l; eassumption.
  step; try apply HL_nil; auto.
  step.
  safestep.

  (* Loop invariant. *)
  - rewrite <- cons_nil_app. eauto.
  - rewrite rev_unit. cbn [app].
    eapply hash_list_rep_subset; eauto.
    econstructor; eauto using hash_list_rep_upd.
    eauto using hashmap_get_fwd_safe_eq.
  - solve_hashmap_subset.
  
  (* Loop invariant implies post-condition. *)
  - step.
    step.
    rewrite app_nil_r.
    eapply hash_list_rep_subset; eauto.
    solve_hashmap_subset.
  - eassign (lift_empty (False) (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset))%pred.
    cancel.
    Unshelve.
    exact tt.
Qed. 

Theorem unseal_all_ok :
    forall hl pr,
    {!< F tbl,
    PERM: pr                      
    PRE:bm, hm,
        F * [[ tbl = extract_blocks bm hl ]] *
        [[ handles_valid bm hl ]] *
        [[ forall t, In t (map fst tbl) -> can_access pr t ]]
    POST:bm', hm', RET: r
        F * [[ r = map snd tbl ]]
    CRASH:bm'', hm_crash,
        false_pred (* Can't crash *)              
    >!} unseal_all hl.
  Proof.
    unfold unseal_all; step.
    safestep.
    apply H3.
    apply in_selN with (n:= m).
    rewrite map_length.
    apply extract_blocks_length in H4;
    setoid_rewrite H4; auto.
    eassign (selN (map snd (extract_blocks bm hl)) m ($0)).
    erewrite extract_blocks_selN.
    repeat erewrite selN_map.
    rewrite <- surjective_pairing; auto.
    unfold block_mem_subset in *.

    erewrite extract_blocks_subset_trans with (bm:= bm); eauto.
    apply extract_blocks_length in H4;
    setoid_rewrite H4; auto.
    apply extract_blocks_length in H4;
    setoid_rewrite H4; auto.
    eapply handles_valid_subset_trans; eauto.
    auto.

    step.
    step.
    rewrite H11.
    replace ([selN (map snd (extract_blocks bm hl)) m $0]) with
        (map snd [selN (extract_blocks bm hl) m tagged_block0]).
    rewrite <- map_app.
    erewrite extract_blocks_subset_trans with (bm:= bm); eauto.
    erewrite extract_blocks_selN_inside; auto.
    rewrite <- extract_blocks_app.
    rewrite <- firstn_S_selN; auto.
    eapply handles_valid_subset_trans; eauto.
    erewrite extract_blocks_subset_trans with (bm:= bm); eauto.

    simpl; erewrite selN_map; auto.
    erewrite <- extract_blocks_subset_trans with (bm:= bm); eauto.
    apply extract_blocks_length in H4;
    setoid_rewrite H4; auto.
    solve_hashmap_subset.
    unfold false_pred; cancel.

    step.
    step.
    rewrite H9, firstn_exact.
    erewrite <- extract_blocks_subset_trans; eauto.
    solve_hashmap_subset.
    eassign (false_pred (AT:= addr)(AEQ:=addr_eq_dec)(V:=valuset))%pred;
    unfold false_pred; cancel.
    Unshelve.
    all: eauto.
    exact tt.
    exact Public.
    exact tagged_block0.
  Qed.


Hint Extern 1 ({{_|_}} Bind (seal_all _ _) _) => apply seal_all_ok : prog.
Hint Extern 1 ({{_|_}} Bind (unseal_all _) _) => apply unseal_all_ok : prog.
Hint Extern 1 ({{_|_}} Bind (hash_list _ _) _) => apply hash_list_ok : prog.





