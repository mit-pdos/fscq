Require Import Hlist.
Require Export ForwardChaining.

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

Ltac simpl_match :=
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    replace d with d';
      try lazymatch goal with
        | [ |- context[match d' with _ => _ end] ] => fail
        end
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    replace d in H;
      try lazymatch type of H with
        | context[match d' with _ => _ end] => fail
        end
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
  cbn;
  try congruence.

Module Dbg.

Ltac find_all x :=
repeat match goal with
       | [ H: context[x] |- _ ] =>
         let t := type of H in idtac H ":" t; fail
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

End Dbg.
