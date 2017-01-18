Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
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

Local Open Scope string_scope.

Example compile_writeback : forall env, sigT (fun p => forall a cs,
  EXTRACT BUFCACHE.writeback a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 ~>? MapUtils.AddrMap.Map.key * 1 ~> ret }} // env
  /\ source_stmt p).
Proof.
  unfold BUFCACHE.writeback.
  intros.
  Print Ltac compile_step.
  eexists; intros.
Defined.

Eval lazy in (projT1 (compile_writeback (StringMap.empty _))).

Example compile_evict : forall env, sigT (fun p => forall a cs,
  func2_val_ref "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.evict a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env
  /\ source_stmt p).
Proof.
  unfold BUFCACHE.evict.
  intros.
  compile.
Defined.

Eval lazy in (projT1 (compile_evict (StringMap.empty _))).
(*
Example compile_maybe_evict : forall env, sigT (fun p => forall cs,
  func2_val_ref "evict" BUFCACHE.evict env ->
  EXTRACT BUFCACHE.maybe_evict cs
  {{ 0 ~> cs }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  unfold BUFCACHE.maybe_evict.
  intros.
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
  eapply hoare_weaken.
  eapply CompileMapCardinal with (var0 := pair_vec_nthl 0 0 vars) (mvar := pair_vec_nthl 0 1 vars).
  cancel_go.
  cancel_go.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  simpl decls_pre. (* TODO: most of the [simpl]s in GoExtraction.v right now are in the wrong spot -- could add a declarationn in another goal *)
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
  compile_step.
  Ltac pattern_prog pat :=
    match goal with
    | [ |- ProgMonad.prog_equiv _ ?pr ] =>
      let Pr := fresh "Pr" in
      set pr as Pr;
      pattern pat in Pr;
      subst Pr
    end.
  eapply extract_equiv_prog. 
  pattern_prog (MapUtils.AddrMap.Map.elements (CSMap cs)).
  eapply ProgMonad.bind_left_id.
  simpl decls_pre.
  compile_step.
  compile_step.
  eapply hoare_weaken.
  eapply CompileMapElements with (mvar := pair_vec_nthl 0 1 vars) (var0 := pair_vec_nthl 0 14 vars).
  cancel_go.
  cancel_go.
  simpl decls_pre.
  do_declare bool ltac:(fun cvar => idtac cvar).
  simpl decls_pre.
  do_declare (nat * (word AsyncDisk.Valulen.valulen * bool))%type ltac:(fun xvar => idtac xvar).
  simpl decls_pre.
  do_declare (list (nat * (word AsyncDisk.Valulen.valulen * bool))%type) ltac:(fun xsvar => idtac xsvar).
  eapply hoare_weaken.
  apply CompileUncons with (lvar := pair_vec_nthl 0 14 vars)
                             (cvar := pair_vec_nthl 0 15 vars)
                             (xvar := pair_vec_nthl 0 16 vars)
                             (xsvar := pair_vec_nthl 0 17 vars).
  3: cancel_go.
  3: cancel_go.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  intros.
  compile.
Defined.


Transparent BUFCACHE.read.


(* TODO *)
Definition eviction_update' a s := Ret (eviction_update s a).

Example compile_read : forall env, sigT (fun p => forall a cs,
  func1_ref "maybe_evict" BUFCACHE.maybe_evict env ->
  func2_val_ref "eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.read a cs
  {{ 0 ~> a * 1 ~> cs * 2 ~>? (cachestate * (valu * unit)) }}
    p
  {{ fun ret => 0 |->? * 1 ~>? cachestate * 2 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.read.
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
  cancel_go.
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
  (* TODO: copy here automatically. This is *the* standard mostly unavoidable copy *)
  do_declare valu ltac:(fun ka' =>
                          eapply CompileBefore; [ 
                            eapply CompileRet with (v := a1) (var0 := ka');
                            eapply hoare_weaken; [
                              eapply CompileDup with (var0 := pair_vec_nthl 0 14 vars) (var' := ka') | cancel_go .. ] | ]).
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  change (Ret (eviction_update ?s ?a)) with (eviction_update' a s).
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  cancel_go.

  Unshelve.
  all: econstructor.
Defined.

Transparent BUFCACHE.write.
Example compile_write : forall env, sigT (fun p => forall a v cs,
  func1_ref "maybe_evict" BUFCACHE.maybe_evict env ->
  func2_val_ref "eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.write a v cs
  {{ 0 ~> a * 1 ~> v * 2 ~> cs }}
    p
  {{ fun ret => 0 ~>? addr * 1 ~>? valu * 2 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.write.
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
  change (Ret (eviction_update ?s ?a)) with (eviction_update' a s).
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  Unshelve.
  all: econstructor.
Defined.

Transparent BUFCACHE.begin_sync.
Example compile_begin_sync : forall env, sigT (fun p => forall cs,
  EXTRACT BUFCACHE.begin_sync cs
  {{ 0 ~> cs }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.begin_sync.
  (* TODO: make this not split & rejoin :P *)
  compile.
Defined.

Eval lazy in projT1 (compile_begin_sync _).
*)

Transparent BUFCACHE.sync.

Definition wbsig := Build_ProgFunctionSig (@Build_WrappedType cachemap) [with_wrapper addr; with_wrapper addr].

Example compile_sync : forall env, sigT (fun p => forall a cs,
  prog_func_call_lemma  "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.sync a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 ~>? addr * 1 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.sync.
  compile.
Defined.
Eval lazy in projT1 (compile_sync _).


Transparent BUFCACHE.end_sync.
Example compile_end_sync : forall env, sigT (fun p => forall cs,
  EXTRACT BUFCACHE.end_sync cs
  {{ 0 ~> cs }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.end_sync.
  compile.
Defined.


Transparent BUFCACHE.init.
Example compile_init : forall env, sigT (fun p => forall n,
  EXTRACT BUFCACHE.init n
  {{ 0 ~> n * 1 ~>? cachestate }}
    p
  {{ fun ret => 0 ~>? nat * 1 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.init.
  compile.
  cancel_go.
Defined.

Local Open Scope string_scope.
Local Open Scope list_scope.

Ltac argtuple pre var :=
  match pre with
  | context [var |-> @wrap ?T ?V ?val] =>
    let X := argtuple pre (S var) in
    let P := constr:(@wrap_type _ V) in
    match X with
    | (?count, ?X)  => constr:(pair (S count) (pair P X))
    end
  | _ => constr:(pair 0 tt)
  end.

Ltac add_to_env name P env :=
  match type of P with
  | EXTRACT _ {{ ?PRE }} ?body_ {{ fun ret : ?R => ?POST }} // _ =>
    lazymatch constr:(fun ret : mark_ret R => (_:find_ret POST)) with
    | (fun ret => ?rvar) =>
      match PRE with
      | context [?x ~> ?y] =>
        match (argtuple PRE 0) with
        | (?nargs, ?args) =>
          let x_ := fresh in
          set (body := body_);
          set (op := {|
            NumParamVars := nargs;
            ParamVars := args;
            Body := body;
            body_source := ltac:(eauto);
          |});
          set (env' := StringMap.add name op env);
          simpl in *; subst body; subst env;
          rename env' into env; subst op
        end
      end
    end
  end.

Ltac add_compiled_program name compiled env :=
  let P := fresh in
  let e_ := fresh in
  let H := fresh in
  destruct (compiled env) as [e_  P];
  repeat match type of P with
  | forall x : ?X, ?y =>
      let x_ := fresh "v" in
      cut X; [intro x_; specialize (P x_) | solve [abstract (repeat econstructor)] ]
  | func2_val_ref ?a ?b ?c -> ?y =>
      let x_ := fresh "v" in
    cut (func2_val_ref a b c); [intro x_; specialize (P x_) | clear P]
  | Logic.and _ _ => destruct P
  end ;
  add_to_env name P env ;
  (* Remove unnecessary variables *)
  repeat match goal with
  | [env := ?X, v : _ |- _] =>
    clear v
  end;
  (* preserve proof for solving func2_ref_val *)
  pose proof compiled.

Definition prog_of := projT1.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "writeback" compile_writeback env.
  exact env.
Defined.


(* Ltac add_compiled_program name compiled env ::=
  let P := fresh in
  let e_ := fresh in
  let H := fresh in
  destruct (compiled env) as [e_  P];
  repeat match type of P with
  | forall x : ?X, ?y =>
      let x_ := fresh "v" in
      cut X; [intro x_; specialize (P x_) | solve [abstract (repeat econstructor)] ]
  | func2_val_ref ?a ?b ?c -> ?y =>
      let x_ := fresh "v" in
    cut (func2_val_ref a b c); [intro x_; specialize (P x_) | clear P]
  | Logic.and _ _ => destruct P
  end.
  add_compiled_program "evict" compile_evict env.
  Focus 2.
  
  
  Ltac func2_val_ref := match goal with
  | [H : context [ProgOk] |- func2_val_ref _ ?p ?env] =>
    match type of H with
    | context [sigT] =>
      destruct (H env); clear H
    | context [?q] => (is_evar q; fail 1) ||
      unify p q;
      eapply extract_func2_val_ref_call;
      [ eapply H ||
        (let H1 := fresh in
        edestruct H as [H1 ]; eapply H1) |
      ]
    end
  end.
  Print func2_val_ref.
  Print func2_ref_val.
  func2_val_ref.
  func2_val_ref.
  Check extract_func2_val_ref_call.
  subst_definitions.
  Ltac map_find_step :=
    match goal with
    |- context [StringMap.find ?k (StringMap.add ?k' _ _)] =>
      destruct (StringMap.E.eq_dec k k');
      [rewrite StringMapFacts.add_eq_o by auto |
       rewrite StringMapFacts.add_neq_o by auto];
       try congruence
    end.
  map_find_step.
  simpl.
  congruence.
  
  
      
  eval_expr.
  
  
  intros. edestruct a. eauto.
  edestruct X.
  eapply extract_func2_val_ref_call.
  intros.
  edestruct a.
  eauto.
  
  apply p.
  clear p.
  subst env.
  
Search func2_val_ref.
  unfold func2_val_ref.
  (* TODO add more programs here *)
  *)
