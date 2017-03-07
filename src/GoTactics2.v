Require Import ProofIrrelevance Eqdep_dec.
Require Import Omega VerdiTactics.
Require Import Mem Pred Hoare.
Require Import GoSepAuto.
Require Import GoSemantics GoHoare.
Require Export GoTactics1.


Local Open Scope string_scope.

Ltac find_cases var st := case_eq (VarMap.find var st); [
  let v := fresh "v" in
  let He := fresh "He" in
  intros v He; rewrite ?He in *
| let Hne := fresh "Hne" in
  intro Hne; rewrite Hne in *; exfalso; solve [ discriminate || intuition idtac ] ].


Ltac inv_exec :=
  match goal with
  | [ H : Go.step _ _ _ |- _ ] => invc H
  | [ H : Go.exec _ _ _ |- _ ] => invc H
  | [ H : Go.crash_step _ |- _ ] => invc H
  end; try discriminate.


Theorem eq_dec_eq :
  forall A (dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) a,
    dec a a = left eq_refl.
Proof.
  intros.
  destruct (dec a a); try congruence.
  f_equal.
  apply UIP_dec; assumption.
Qed.

Ltac forwardauto1 H :=
  repeat eforward H; conclude H eauto.

Ltac forwardauto H :=
  forwardauto1 H; repeat forwardauto1 H.

Ltac forward_solve_step :=
  match goal with
    | _ => progress intuition eauto
    | [ H : forall _, _ |- _ ] => forwardauto H
    | _ => deex
    | _ => discriminate
  end.

Ltac forward_solve :=
  repeat forward_solve_step.

Import Go.

Ltac unfold_expr :=
  match goal with
  | [H : _ |- _ ] =>
      progress (unfold is_false, is_true, eval_bool,
         value_well_typed,
         numop_impl', numop_impl,
         split_pair_impl, split_pair_impl',
         join_pair_impl, join_pair_impl',
         append_impl', uncons_impl',
         map_add_impl, map_add_impl',
         map_remove_impl, map_remove_impl',
         map_find_impl, map_find_impl',
         map_card_impl, map_card_impl',
         freeze_buffer_impl, freeze_buffer_impl',
         slice_buffer_impl, slice_buffer_impl',
         append_impl, uncons_impl,
         map_elements_impl, map_elements_impl',
         eval_test_m, eval_test_num, eval_test_bool,
         update_one, setconst_impl, duplicate_impl,
         deserialize_num_impl, deserialize_num_impl',
         sel, id, eval, eq_rect_r, eq_rect
         in H); simpl in H
  | _ => progress (unfold is_false, is_true, eval_bool,
         value_well_typed,
         numop_impl', numop_impl,
         split_pair_impl, split_pair_impl',
         join_pair_impl, join_pair_impl',
         append_impl', uncons_impl',
         map_add_impl, map_add_impl',
         map_remove_impl, map_remove_impl',
         map_find_impl, map_find_impl',
         map_card_impl, map_card_impl',
         freeze_buffer_impl, freeze_buffer_impl',
         slice_buffer_impl, slice_buffer_impl',
         append_impl, uncons_impl,
         map_elements_impl, map_elements_impl',
         eval_test_m, eval_test_num, eval_test_bool,
         update_one, setconst_impl, duplicate_impl,
         deserialize_num_impl, deserialize_num_impl',
         sel, id, eval, eq_rect_r, eq_rect
         ); simpl
  end.


Ltac deex_hyp H :=
  match type of H with
  | exists varname, _ =>
    let varname' := fresh varname in
    destruct H as (varname', H); intuition subst
  end.


Ltac find_inversion_wrap :=
  match goal with
    | [ H : wrap _ = Go.Val _ _ |- _ ] => unfold wrap in H; simpl in H; unfold id in H
    | [ H : Go.Val _ _ = wrap _ |- _ ] => unfold wrap in H; simpl in H; unfold id in H
    | _ => find_inversion_go
  end.

Ltac match_finds :=
  match goal with
    | [ H1: VarMap.find ?a ?s = ?v1, H2: VarMap.find ?a ?s = ?v2 |- _ ] => rewrite H1 in H2;
      (find_inversion_wrap || invc H2 || idtac)
  end.

Ltac destruct_pair :=
  match goal with
    | [ H : _ * _ |- _ ] => destruct H
    | [ H : Go.state |- _ ] => destruct H
  end.

Ltac inv_exec_progok :=
  repeat destruct_pair; repeat inv_exec; unfold Go.sel in *; simpl in *;
  intuition (subst; try discriminate;
             repeat find_inversion_safe; repeat match_finds; repeat find_inversion_safe;  simpl in *;
               try solve [ exfalso; intuition eauto 10 ]; eauto 10).

Ltac extract_var_val_from H P s :=
  match P with
  | context[(?a |-> ?v)%pred] =>
    match goal with
    | [ H: VarMap.find a s = Some v |- _ ] => fail 1
    | _ => idtac
    end;
    let He := fresh "He" in
    assert (VarMap.find a s = Some v) as He; [
      eapply pred_apply_pimpl_proper in H; [
      | reflexivity |
      lazymatch goal with
      | [ |- _ =p=> ?Q ] =>
        let F := fresh "F" in
        evar (F : pred);
        unify Q (a |-> v * F)%pred;
        cancel
      end ];
      eapply ptsto_valid in H; eassumption
    | try rewrite He in * ]
  end.

Ltac extract_var_val :=
  match goal with
  | [ H: ?s ≲ ?P |- _ ] => extract_var_val_from H P s
  | [ H: (?P)%pred (mem_of ?s) |- _ ] => extract_var_val_from H P s
  end.

Ltac extract_pred_apply_exists_in H :=
  repeat setoid_rewrite pimpl_exists_l_star_r in H;
  repeat setoid_rewrite pimpl_exists_r_star_r in H;
    unfold pred_apply, exis in H; deex_hyp H; repeat deex_hyp H.

Ltac extract_pred_apply_exists :=
  match goal with
  | [ H : _ ≲ _ |- _ ] => extract_pred_apply_exists_in H
  | [ H : ?P (mem_of ?s) |- _ ] => extract_pred_apply_exists_in H
  end.

Definition prod' := prod.
Definition exis' := exis.

Hint Extern 0 (okToCancel (ptsto ?a _) (ptsto ?b _)) => unify a b; reflexivity : okToUnify.
Hint Extern 0 (okToCancel (ptsto ?a _) (ptsto ?a _)) => reflexivity : okToCancel.

Local Open Scope pred_scope.

Lemma ptsto_upd_disjoint' : forall (F : pred) a v m,
  F m -> m a = None
  -> (a |-> v * F)%pred (upd m a v).
Proof.
  intros.
  eapply pred_apply_pimpl_proper; [ reflexivity | | eapply ptsto_upd_disjoint; eauto ].
  cancel.
Qed.

Lemma ptsto_any_upd :
  forall AT AEQ V a v F m,
    (a |->? * F)%pred m -> (@ptsto AT AEQ V a v * F)%pred (Mem.upd m a v).
Proof.
  intros.
  apply pimpl_exists_r_star_r in H.
  unfold exis in H; deex_hyp H.
  eauto using ptsto_upd.
Qed.

Lemma ptsto_typed_any_upd :
  forall AT AEQ T {Wr : GoWrapper T} a v F m,
    (a ~>? T * F)%pred m -> (a |-> Val wrap_type v * F)%pred (@Mem.upd AT _ AEQ m a (Val wrap_type v)).
Proof.
  intros.
  apply pimpl_exists_r_star_r in H.
  unfold exis in H; deex_hyp H.
  eauto using ptsto_upd.
Qed.

Lemma okToCancel_ptsto_any : forall var val,
  okToCancel (var |-> val : pred) (var |->?).
Proof.
  intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (?var |-> ?val) (?var |->?)) =>
  apply okToCancel_ptsto_any : okToCancel.

Lemma okToCancel_ptsto_typed_any_typed : forall T {Wr : GoWrapper T} var (val : T),
  okToCancel (var ~> val : pred) (var ~>? T).
Proof.
  intros.
  apply pimpl_exists_r. eauto.
Qed.

Hint Extern 0 (okToCancel (?var ~> ?val) (exists val', ?var |-> Val _ val')) =>
  apply okToCancel_ptsto_typed_any_typed : okToCancel.

Lemma okToCancel_ptsto_any_typed : forall T {Wr : GoWrapper T} var val,
  okToCancel (var |-> Val (@wrap_type T _) val : pred) (var ~>? T).
Proof.
  intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (?var |-> Val _ _) (exists val', ?var |-> Val _ val')) =>
  apply okToCancel_ptsto_any_typed : okToCancel.

Lemma okToCancel_any_any : forall X var V,
  okToCancel (exists x : X, var |-> V x : pred) (var |->?).
Proof.
  intros.
  apply pimpl_exists_l; intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (exists _, ?var |-> _) (?var |->?)) =>
  apply okToCancel_any_any : okToCancel.

(* TODO: too much of a hack? too slow? *)
Hint Extern 0 (okToCancel (?var |-> _) (exists _, ?var |-> _)) =>
  apply pimpl_exists_r; eexists; reflexivity : okToCancel.

Hint Extern 0 (okToCancel (exists val', ?var |-> Val _ val')%pred (exists val', ?var |-> Val _ val')%pred) =>
  reflexivity : okToCancel.

Ltac cancel_go :=
  solve [GoSepAuto.cancel_go_refl] ||
  (idtac "cancel_refl failed"; solve [GoSepAuto.cancel_go_fast] ||
   unfold var, default_value; GoSepAuto.cancel; try apply pimpl_refl).

Lemma ptsto_delete' : forall a (F :pred) (m : mem),
  (a |->? * F)%pred m -> F (delete m a).
Proof.
  intros.
  apply pimpl_exists_r_star_r in H.
  unfold exis in H.
  deex.
  eapply ptsto_delete; eauto.
Qed.

Ltac pred_solve_step := match goal with
  | [ |- ( ?P )%pred (upd _ ?a ?x) ] =>
    match P with
    | context [(a |-> _)%pred] =>
      eapply pimpl_apply with (p := (a |-> _ * _)%pred);
      [ cancel_go | (eapply ptsto_upd_disjoint'; [ | solve [eauto] ]) ||
                    eapply ptsto_upd ||
                    eapply ptsto_any_upd ||
                    eapply ptsto_typed_any_upd ]
    | context [(@ptsto ?AT ?AEQ ?V a ?y)%pred] =>
      let H := fresh in
      assert (@okToCancel AT AEQ V (ptsto a x) (ptsto a y)) as H by (eauto with okToCancel);
      rewrite <- H
    end
  | [ |- ( ?P )%pred (delete _ ?a) ] =>
    eapply ptsto_delete' with (F := P)
  | [ H : _%pred ?t |- _%pred ?t ] => pred_apply; solve [cancel_go]
  | _ => solve [cancel_go]
  end.

Create HintDb pred_solve_rewrites.
Hint Rewrite add_upd remove_delete : pred_solve_rewrites.
(* Doesn't seem to work.
Hint Rewrite default_zero : pred_solve_rewrites.
*)

Ltac pred_solve := progress (
  unfold pred_apply in *;
  repeat pred_solve_step;
  repeat (autorewrite with pred_solve_rewrites || rewrite ?default_zero);
  repeat pred_solve_step).

Ltac pred_cancel :=
  unfold pred_apply in *;
  match goal with
  | [H : _ |- _] => eapply pimpl_apply; [> | exact H]; solve [cancel_go]
  end.


Ltac pred_conflict_solve :=
  match goal with
  | [H : ?x = ?y,
     H': context [ptsto ?x] |- _ ] =>
     match goal with
     | [H'' : context [ptsto ?y] |- _ ] =>
      unify H' H'';
      match type of H' with
      | ?p ?m_ =>
        rewrite H in H';
        exfalso;
        eapply ptsto_conflict_F with (a := y) (m := m_);
        pred_apply; cancel_go
      end
    end
  end.

Ltac eval_expr_step :=
    repeat (destruct_pair + unfold_expr); simpl in *;
    try pred_conflict_solve;
    try subst;
    repeat destruct_type unit;
    clear_trivial_eq;
    match goal with
    | [H : context [match ?e in (_ = _) return _ with _ => _ end] |- _ ]
      => rewrite (proof_irrelevance _ e (eq_refl)) in H
    | [H : context [eq_sym ?t] |- _ ]
      => setoid_rewrite (proof_irrelevance _ t eq_refl) in H
    | [H : context [VarMap.find ?k (VarMap.add ?k' _ _)] |- _] =>
      destruct (Nat.eq_dec k k'); [
        rewrite VarMapFacts.add_eq_o in H by auto |
        rewrite VarMapFacts.add_neq_o in H by auto ]
    | [e : ?x = _, H: context[match ?x with _ => _ end] |- _]
      => rewrite e in H
    | [e : ?x = _ |- context[match ?x with _ => _ end] ]
      => rewrite e
    | [H : context[if ?x then _ else _] |- _]
      => let H' := fresh in destruct x eqn:H'; try omega
    | [|- context[if ?x then _ else _] ]
      => let H' := fresh in destruct x eqn:H'; try omega
    | [H : context [match ?x with _ => _ end],
       H': _ = ?x |- _]
      => rewrite <- H' in H
    | [H : context [match ?x with _ => _ end],
       H': ?x = _ |- _]
      => rewrite H' in H
    | [H : context [match ?x with _ => _ end] |- _]
      => let H' := fresh in destruct x eqn:H'
    | [ |- context [match ?e in (_ = _) return _ with _ => _ end] ]
      => rewrite (proof_irrelevance _ e (eq_refl))
    | [ |- context [eq_sym ?t] ]
      => setoid_rewrite (proof_irrelevance _ t eq_refl)
    | [ |- context [match ?x with _ => _ end] ]
      => let H' := fresh in destruct x eqn:H'
    | [x : value |- _ ] => destruct x
    | [H : ?a = _, H' : context [?a] |- _ ] =>
      rewrite H in H'
    | _
      => idtac
    end; try solve [congruence | omega];
    repeat find_inversion_wrap.

Ltac eval_expr :=
    try extract_pred_apply_exists;
    repeat extract_var_val;
    repeat eval_expr_step.
