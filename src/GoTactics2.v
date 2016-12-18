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
         numop_impl', numop_impl,
         split_pair_impl, split_pair_impl',
         join_pair_impl, join_pair_impl',
         map_add_impl, map_add_impl',
         map_remove_impl, map_remove_impl',
         map_find_impl, map_find_impl',
         map_card_impl, map_card_impl',
         map_elements_impl, map_elements_impl',
         eval_test_m, eval_test_num, eval_test_bool,
         update_one, setconst_impl, duplicate_impl,
         sel, id, eval, eq_rect_r, eq_rect
         in H); simpl in H
  | _ => progress (unfold is_false, is_true, eval_bool,
         numop_impl', numop_impl,
         split_pair_impl, split_pair_impl',
         join_pair_impl, join_pair_impl',
         map_add_impl, map_add_impl',
         map_remove_impl, map_remove_impl',
         map_find_impl, map_find_impl',
         map_card_impl, map_card_impl',
         map_elements_impl, map_elements_impl',
         eval_test_m, eval_test_num, eval_test_bool,
         update_one, setconst_impl, duplicate_impl,
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
  lazymatch goal with
  | [ H: ?s ≲ ?P |- _ ] => extract_var_val_from H P s
  | [ H: (?P)%pred (mem_of ?s) |- _ ] => extract_var_val_from H P s
  end.

Ltac extract_pred_apply_exists :=
  match goal with
  | [ H : _ ≲ _ |- _ ] =>
    repeat setoid_rewrite pimpl_exists_l_star_r in H;
    repeat setoid_rewrite pimpl_exists_r_star_r in H;
      unfold pred_apply, exis in H; deex_hyp H; repeat deex_hyp H
  end.

Ltac eval_expr_step :=
    repeat extract_var_val;
    repeat (destruct_pair + unfold_expr); simpl in *;
    try extract_pred_apply_exists;
    try subst;
    match goal with
    | [H : context [match ?e in (_ = _) return _ with _ => _ end] |- _ ]
      => rewrite (proof_irrelevance _ e (eq_refl)) in H
    | [H : context [eq_sym ?t] |- _ ]
      => setoid_rewrite (proof_irrelevance _ t eq_refl) in H
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
    | _
      => idtac
    end; try solve [congruence | omega];
    repeat find_inversion_wrap.

Ltac eval_expr := repeat eval_expr_step.


Definition prod' := prod.
Definition exis' := exis.

Hint Extern 0 (okToCancel (ptsto ?a _) (ptsto ?b _)) => unify a b; reflexivity : okToUnify.

Local Open Scope pred_scope.

Lemma ptsto_upd_disjoint' : forall (F : pred) a v m,
  F m -> m a = None
  -> (a |-> v * F)%pred (upd m a v).
Proof.
  intros.
  eapply pred_apply_pimpl_proper; [ reflexivity | | eapply ptsto_upd_disjoint; eauto ].
  cancel.
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

Ltac cancel_go := GoSepAuto.cancel.

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
    | context [(a |-> ?x)%pred] =>
      eapply pimpl_apply with (p := (a |-> x * _)%pred);
      [ cancel_go | (eapply ptsto_upd_disjoint'; solve [eauto]) || eapply ptsto_upd ]
    | context [(@ptsto ?AT ?AEQ ?V a ?y)%pred] =>
      let H := fresh in
      assert (@okToCancel AT AEQ V (ptsto a y) (ptsto a x)) as H;
      [ eauto with okToCancel | rewrite H ]
    end
  | [ |- ( ?P )%pred (delete _ ?a) ] =>
    eapply ptsto_delete' with (F := P)
  | [ H : _%pred ?t |- _%pred ?t ] => pred_apply; solve [cancel_go]
  | _ => solve [cancel_go]
  end.

Create HintDb pred_solve_rewrites.
Hint Rewrite add_upd remove_delete : pred_solve_rewrites.
(* Coq bug! This hangs:
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