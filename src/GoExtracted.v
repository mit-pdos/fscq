Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred SepAuto.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoTactics2.
Import ListNotations.
Import Go.

Open Scope pred_scope.

Require Import Cache.

Instance WrapByTransforming_cachestate : WrapByTransforming cachestate.
  refine {|
    transform := fun cs => (CSMap cs, CSMaxCount cs, CSEvict cs);
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.

Instance cachestate_default_value : DefaultValue cachestate := {| zeroval :=
  {| CSMap := Go.Map.empty _; CSMaxCount := 0; CSEvict := tt |} |}.
  unfold wrap, wrap', GoWrapper_transform, default_value. simpl.
  repeat f_equal.
  apply MapUtils.addrmap_equal_eq.
  apply MapUtils.AddrMap.map_empty.
  auto with map.
Defined.

Instance addrmap_default_value : forall T {H: GoWrapper T}, DefaultValue (Map.t T).
  intros.
  apply Build_DefaultValue with (zeroval := Map.empty _).
  unfold default_value, default_value', wrap, wrap'.
  simpl. repeat f_equal.
  apply MapUtils.addrmap_equal_eq.
  apply MapUtils.AddrMap.map_empty.
  eauto with map.
Defined.

Example compile_writeback : forall env, sigT (fun p => forall a cs,
  EXTRACT BUFCACHE.writeback a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  unfold BUFCACHE.writeback.
  intros.
  compile_step.
  eapply hoare_strengthen_pre.
  rewrite transform_pimpl. simpl. reflexivity. (* TODO *)
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  3: cancel_go.
  Focus 3. unfold exis'. cancel.
  match goal with
  | [ |- ?P =p=> ?Q ] => set Q
  end.
  pattern x in p. subst p. reflexivity.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  (* TODO do the right thing here in compile_map_op *)
  eapply CompileRet with (v := (CSMap cs)) (var0 := (snd (fst (fst (fst (fst (fst (fst (fst (fst (fst vars))))))))))).
  compile_step.
  compile_step.
  compile_step.
  compile_step. (* TODO rule for Ret false *)
  {
    eapply hoare_weaken.
    eapply CompileRet', CompileSkip.
    cancel_go. cancel_go.
  }
  compile_step.
  compile_step.
  eapply hoare_weaken.
  eapply CompileRet' with (var0 := 1).
  eapply hoare_weaken_post.
  intros.
  match goal with
  | [ |- ?P =p=> ?Q ] => set (P)
  end.
  rewrite transform_pimpl. simpl.
  subst p.
  match goal with
  | [ |- ?e _ =p=> ?Q ] => unify e (fun x : unit => Q)
  end. reflexivity.
  2: cancel_go.
  2: cancel_go.
  eapply CompileRet.
  unfold prod'. (* TODO: prod' should never escape to this point! *)
  compile_step.
  compile_step.
  compile_step.
  eapply hoare_weaken.
  eapply CompileRet' with (var0 := 1).
  eapply hoare_weaken_post.
  intros.
  match goal with
  | [ |- ?P =p=> ?Q ] => set (P)
  end.
  rewrite transform_pimpl. simpl.
  subst p.
  match goal with
  | [ |- ?e _ =p=> ?Q ] => unify e (fun x : unit => Q)
  end. reflexivity.
  2: cancel_go.
  2: cancel_go.
  eapply CompileRet.
  unfold prod'.
  compile_step.
  compile_step.
  (***********)
  (* This [compile_step] takes >2 minutes *)
  (***********)
  Time compile_step.
  unfold exis'. cancel.
  Axiom admit : False.
  (* TODO: [CSMap cs] is gone! *) exfalso; apply admit.
  eapply hoare_weaken.
  eapply CompileRet' with (var0 := 1).
  eapply hoare_weaken_post.
  intros.
  match goal with
  | [ |- ?P =p=> ?Q ] => set (P)
  end.
  rewrite transform_pimpl. simpl.
  subst p.
  match goal with
  | [ |- ?e _ =p=> ?Q ] => unify e (fun x : unit => Q)
  end. reflexivity.
  2: cancel_go.
  2: cancel_go.
  eapply CompileRet.
  unfold prod'.
  compile_step.
  compile_step.
  (* [compile_step] here works but takes >15 minutes... *)
  match goal with
  | |- EXTRACT Ret (?a_, ?b_)
       {{ ?pre }}
          _
       {{ ?post }} // _ =>
        match find_val a_ pre with
        | Some ?ka =>
            match find_val b_ pre with
            | Some ?kb =>
                match var_mapping_to_ret with
                | ?kp =>
                    eapply hoare_weaken;
                     [ apply CompileJoin with
                         (avar := ka) (bvar := kb) (pvar := kp)
                     | .. ]
                end
            end
        end
  end.
  simpl in *. fold prod' in *. cancel.
  simpl in *. unfold exis' in *. cancel.
  (* TODO: [CSMap cs] is gone! *) exfalso; apply admit.

  Unshelve.
  all: repeat constructor.
  exact $0.
(* This eats memory and dies: *)
Defined.
Eval lazy in (projT1_sig compile_writeback).