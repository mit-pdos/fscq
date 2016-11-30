Require Import Hlist.
Require Export ForwardChaining.

Ltac destruct_ands :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         end.

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; destruct_ands; subst
  end.

Ltac remove_duplicate :=
  match goal with
  | [ H: ?p, H': ?p |- _ ] =>
    match type of p with
    | Prop => clear H'
    end
  end.

Ltac remove_refl :=
  match goal with
  | [ H: ?a = ?a |- _ ] => clear dependent H
  end.

Ltac remove_sym_neq :=
  match goal with
  | [ H: ?a <> ?a', H': ?a' <> ?a |- _ ] => clear dependent H'
  end.

Ltac remove_unit :=
  match goal with
  | [ a: unit |- _ ] => clear a
  end.

Ltac sigT_eq :=
  match goal with
  | [ H: @eq (sigT _) _ _ |- _ ] =>
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
    subst
  end.

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      is_not_learnt H;
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.

(* test simpl_match failure when match does not go away *)
Goal forall (vd m: nat -> option nat) a,
    vd a = m a ->
    vd a = match (m a) with
         | Some v => Some v
         | None => None
           end.
Proof.
  intros.
  (simpl_match; fail "should not work here")
  || idtac.
Abort.

Goal forall (vd m: nat -> option nat) a v v',
    vd a =  Some v ->
    m a = Some v' ->
    vd a = match (m a) with
           | Some _ => Some v
           | None => None
           end.
Proof.
  intros.
  simpl_match; now auto.
Abort.

(* hypothesis replacement should remove the match or fail *)
Goal forall (vd m: nat -> option nat) a,
    vd a = m a ->
    m a = match (m a) with
          | Some v => Some v
          | None => None
          end ->
    True.
Proof.
  intros.
  (simpl_match; fail "should not work here")
  || idtac.
Abort.

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => case_eq e; intros
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                is_not_learnt H;
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
               end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.

Ltac same_opt_val :=
  match goal with
  | [ H: ?e = Some ?v, H': ?e = Some ?v' |- _ ] =>
    rewrite H in H'; inversion H'; subst
  | [ H: ?e = Some ?v, H': ?e = None |- _ ] =>
    rewrite H in H'; now inversion H'
  end.

Ltac mem_contents_eq :=
  match goal with
  | [ H: get ?m ?var = _, H': get ?m ?var = _ |- _ ] =>
    rewrite H in H'; try inversion H'; subst
  end.

Ltac cleanup :=
  repeat (remove_duplicate
          || remove_refl
          || remove_unit
          || remove_sym_neq
          || same_opt_val
          || simpl_match
          || mem_contents_eq);
  simpl;
  try congruence.

Module Dbg.

Ltac find_all x :=
repeat match goal with
       | [ H: context[x] |- _ ] =>
         let t := type of H in
          lazymatch t with
          | Learnt => idtac
          | _ => idtac H ":" t
          end; fail
       end.

Ltac repeat_upto k t :=
  try lazymatch k with
  | O => idtac
  | S ?k' => progress t; repeat_upto k' t
  end.

Tactic Notation "repeat_upto" constr(k) tactic(t) :=
  repeat_upto k t.

Goal 1 = 1.
  (* repeat_upto does not infinite loop and emits 4 goals
      (eq_trans is called once, then once on each generated equality) *)
  repeat_upto 2 eapply eq_trans; [
    apply eq_refl | apply eq_refl | apply eq_refl | apply eq_refl ].
Abort.

Tactic Notation "time_solver" tactic(t) :=
  try time "finisher" progress t.

Inductive hidden (P:Prop) : Prop :=
| Hidden (H:P).

Remark hidden_eq_p : forall P,
  hidden P <-> P.
Proof.
  firstorder.
Qed.

Ltac unhide_goal := apply Hidden.

Ltac unhide_hyp H := rewrite hidden_eq_p in H.

Tactic Notation "unhide" := unhide_goal.
Tactic Notation "unhide" "in" hyp(H) := unhide_hyp H.

Goal forall (P Q:Prop),
  hidden (P -> Q) ->
  P ->
  Q /\ hidden P.
Proof.
  intros.
  split.
  - unhide in H.
    apply H. apply H0.
  - unhide.
    apply H0.

  Fail idtac "should be solved".
Abort.

End Dbg.

Ltac inv_prod :=
  match goal with
  | [ H: (_, _) = (_, _) |- _ ] =>
    inversion H; clear H; subst
  end.

(* lightweight intuition *)
Ltac expand_propositional t :=
  repeat match goal with
         | |- forall _, _ => intro
         | [ H: ?P -> _ |- _ ] =>
           lazymatch type of P with
           | Prop => let ant := fresh in
                 assert P as ant by (solve [ trivial ] || t);
                 specialize (H ant);
                 clear ant
           end
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         end.

Tactic Notation "expand" "propositional" := expand_propositional auto.
Tactic Notation "expand" "propositional" tactic(t) := expand_propositional t.

Ltac specialize_all t :=
  repeat match goal with
  | [ H: forall (_:t), _, x:t |- _ ] =>
    specialize (H x)
  end.

Ltac learn_all t :=
  repeat match goal with
  | [ H: forall (_:t), _, x:t |- _ ] =>
    learn that (H x)
  end.

Ltac head_symbol e :=
  lazymatch e with
  | ?h _ _ _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ => h
  | ?h _ _ _ _ => h
  | ?h _ _ _ => h
  | ?h _ _ => h
  | ?h _ => h
  | ?h => h
  end.

Ltac descend :=
  repeat match goal with
         | |- exists _, _ => eexists
         end.