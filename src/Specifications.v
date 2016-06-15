Require Import AsyncDisk.
Require Import MemClass Pred PredCrash.
Require Import Prog ProgMonad Hoare.
Require Import SepAuto.
Require Import Hashmap.

Set Implicit Arguments.

Notation prog_valuset := (valu * list valu)%type.

Record SeqHoareSpec R :=
  SeqSpec { seq_spec_pre: @pred addr _ prog_valuset;
            seq_spec_post: R -> @pred addr _ prog_valuset;
            seq_spec_crash: @pred addr _ prog_valuset }.

Definition seq_hoare_double R A (spec: A -> SeqHoareSpec R)
           (p: Prog.prog R) :=
  forall T' (rx : R -> Prog.prog T'),
    Hoare.corr2
      (fun hm_ done_ crash_ =>
         exists a F_,
           F_ * seq_spec_pre (spec a) *
           [[ sync_invariant F_ ]] *
           [[ forall r, Hoare.corr2
                       (fun hm'_ done'_ crash'_ =>
                          F_ * seq_spec_post (spec a) r  *
                          [[ exists l, hashmap_subset l hm_ hm'_ ]] *
                          [[ done'_ = done_ ]] *
                          [[ crash'_ = crash_ ]]
                       ) (rx r) ]] *
           [[ forall hm_crash,
                (F_ * seq_spec_crash (spec a) *
                 [[ exists l, hashmap_subset l hm_ hm_crash ]])%pred =p=>
              crash_ hm_crash ]])%pred
      (Bind p rx).

(* technically the fully expanded spec is a quadruple: the three
predicates in spec, plus the program (in comparison to ordinary Hoare
triples consisting of a precondition, postcondition and program) *)
Definition seq_hoare_quadruple R A (spec: A -> SeqHoareSpec R)
           (p: Prog.prog R) :=
  forall a F hm d out,
    (F * seq_spec_pre (spec a) *
     [[ sync_invariant F ]])%pred d ->
    exec d hm p out ->
    (exists d' hm' r,
        out = Finished d' hm' r /\
        (F * seq_spec_post (spec a) r *
         [[ exists l, hashmap_subset l hm hm' ]])%pred d') \/
    (exists d' hm',
        out = Crashed R d' hm' /\
        (F * seq_spec_crash (spec a) *
         [[ exists l, hashmap_subset l hm hm' ]])%pred d').

Section ExampleSeqSpecs.

  (* isomorphic to prod, but distinct for the benefit of Ltac *)
  Inductive spec_prod A B :=
    spec_pair : A -> B -> spec_prod A B.

  Ltac destruct_spec_prod :=
    repeat match goal with
    | [ p: spec_prod _ _ |- _ ] => destruct p
    end.

  Ltac spec_equiv :=
    repeat lazymatch goal with
           | [ |- forall _, _ ] => intros
           | [ |- seq_hoare_double _ _ ] =>
             unfold seq_hoare_double
           | [ |- corr2 _ _ ] =>
             eapply pimpl_ok2; [ solve [ eauto ] | eauto ]
           | [ |- _ =p=> exists (_: spec_prod _ _), _ ] =>
             eapply pimpl_exists_l;
             intros;
             repeat destruct_spec_prod;
             cancel
           | [ |- _ =p=> _ ] =>
             cancel
           end.

  (* these are the sorts of theorems needed to go from the notation to
  the more structured SeqHoareSpec. *)
  Theorem seq_read_spec : forall a,
      {< v,
       PRE        a |-> v
       POST RET:r a |-> v * [[ r = (fst v) ]]
       CRASH      a |-> v
      >} Prog.Read a <->
      seq_hoare_double
        (fun v =>
           SeqSpec (a |-> v)%pred
                   (fun r => a |-> v *
                                 [[ r = (fst v) ]])%pred
                   (a |-> v)%pred
        ) (Prog.Read a).
  Proof.
    split; intros.
    - spec_equiv.
    - spec_equiv.
  Qed.

  Definition swap a a' :=
    v <- Prog.Read a;
      v' <- Prog.Read a';
      Prog.Write a v';;
      Prog.Write a' v;;
      Ret tt.

  Notation "'SEQSPEC' e1 .. e2 , {{ pre }} {{ post }} {{ crash }}" :=
    (fun e1 => .. (fun e2 =>
                  SeqSpec pre%pred post%pred crash%pred) .. )
      (at level 0,
       e1 binder,
       e2 binder).

  Definition uncurry {A B C} (f: A -> B -> C) :
    spec_prod A B -> C :=
    fun ab => let 'spec_pair a b := ab in f a b.

  Definition test_spec a a' :=
    uncurry SEQSPEC v v',
    {{ a |-> v * a' |-> v' }}
      {{ fun r:unit => a |-> v' * a' |-> v }}
      {{ a |->? * a' |->? }}.

  Hint Resolve spec_pair.

  Theorem seq_swap_spec : forall a a',
      {< (v v': prog_valuset),
       PRE       a |-> v * a' |-> v'
       POST RET:_ a |-> v' * a' |-> v
       CRASH a |->? * a' |->?
      >} swap a a' <->
      seq_hoare_double
        (uncurry SEQSPEC v v',
         {{ a |-> v * a' |-> v' }}
           {{ fun r:unit => a |-> v' * a' |-> v }}
           {{ a |->? * a' |->? }}
        ) (swap a a').
  Proof.
    unfold uncurry.
    split; intros.

    - (* this is exactly what spec_equiv does, but cancel exposes a bug
    that prevents the tactic from working *)
      unfold seq_hoare_double; intros.
      eapply pimpl_ok2; eauto; intros.
      eapply pimpl_exists_l.
      intros.
      destruct_spec_prod.
      cancel.

    - eapply pimpl_ok2; eauto; intros.
      (* this looks bad, but its just deex'ing the number of
      existentially quantified variables in the precondition, then
      instantiating the pair on the right hand side with the newly
      created sequence of variables *)
      do 2 (eapply pimpl_exists_l; intros; eauto).
      apply pimpl_exists_r.
      exists (spec_pair x x0).
      cancel.
  Qed.

End ExampleSeqSpecs.

Hint Resolve <- bind_right_id.

Ltac lift_sep_star :=
 repeat match goal with
         | [ H: (_ * [[ _ ]])%pred _ |- _ ] =>
           apply sep_star_lift_apply in H;
             destruct H
         end .

Theorem spec_double_to_quadruple : forall T A (spec: A -> SeqHoareSpec T) (p: prog T),
    seq_hoare_double spec p ->
    seq_hoare_quadruple spec p.
Proof.
  unfold seq_hoare_double, seq_hoare_quadruple; intros.
  unfold corr2 at 1 in H.
  specialize (H _ Ret).
  specialize (H (fun hm' r =>
                   F * seq_spec_post (spec a) r *
                   [[ exists l, hashmap_subset l hm hm' ]])%pred).
  specialize (H (fun hm' =>
                   F * seq_spec_crash (spec a) *
                   [[ exists l, hashmap_subset l hm hm' ]])%pred).
  specialize (H d hm out).
  match type of H with
  | ?H -> _ => assert H
  end.
  exists a, F.
  pred_apply; cancel.
  unfold corr2; intros.
  inv_exec.
  left.
  do 3 eexists; intuition eauto.
  lift_sep_star; subst.
  pred_apply; cancel.

  intuition.
Qed.

Ltac deex_pred :=
  deex ||
  match goal with
  | [ H: exis (fun (varname:_) => _) _ |- _ ] =>
    let newvar := fresh varname in
    unfold exis in H at 1;
    destruct H as (newvar, ?);
    intuition idtac
  end.

Ltac inv_outcome :=
  match goal with
  | [ H: _ = _ :> (outcome _) |- _ ] =>
    inversion H; subst; clear H
  end.

Theorem spec_quadruple_to_double : forall T A (spec: A -> SeqHoareSpec T) (p: prog T),
    seq_hoare_quadruple spec p ->
    seq_hoare_double spec p.
Proof.
  unfold seq_hoare_double, seq_hoare_quadruple; intros.
  unfold corr2 at 1; intros.
  inv_exec;
    repeat deex_pred;
    lift_sep_star;
    match goal with
    | [ Hexec: exec _ _ _ _ |- _ ] =>
      apply (H a F_) in Hexec
    end;
    intuition;
    repeat deex;
    try inv_outcome;
    try solve [ pred_apply; cancel ].

  match goal with
  | [ H: forall _, {{_}} rx _, Hexec: exec _ _ (rx _) _ |- _] =>
    eapply H in Hexec; eauto
  end.
  pred_apply; cancel.

  right; repeat eexists; eauto.
  match goal with
  | [ H: forall _, _ =p=> crash _ |- _ ] =>
    apply H; pred_apply; cancel
  end.
Qed.
