Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers.
Import ListNotations.

Import Go.

Require Import Cache.

Local Open Scope string_scope.

Example compile_writeback : sigT (fun p => source_stmt p /\
  forall env a cs,
  EXTRACT BUFCACHE.writeback a cs
  {{ 0 ~>? cachestate * 1 ~> a * 2 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.writeback.
  compile.
Defined.

Eval lazy in (projT1 compile_writeback).

Example compile_evict : sigT (fun p => source_stmt p /\ forall env a cs,
  prog_func_call_lemma {| FArgs := [with_wrapper addr; with_wrapper cachestate]; FRet := with_wrapper cachestate |} "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.evict a cs
  {{ 0 ~>? cachestate * 1 ~> a * 2 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? W * 2 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.evict.
  compile.
Defined.

Eval lazy in (projT1 compile_evict).

Example compile_maybe_evict : sigT (fun p => source_stmt p /\ forall env cs,
  prog_func_call_lemma {| FArgs := [with_wrapper addr; with_wrapper cachestate]; FRet := with_wrapper cachestate |} "evict" BUFCACHE.evict env ->
  EXTRACT BUFCACHE.maybe_evict cs
  {{ 0 ~>? cachestate * 1 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.maybe_evict.
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
  eapply CompileMapCardinal with (var0 := nth_var 0 vars) (mvar := nth_var 1 vars).
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
  eapply CompileMapElements with (mvar := nth_var 1 vars) (var0 := nth_var 15 vars).
  cancel_go.
  cancel_go.
  simpl decls_pre.
  do_declare bool ltac:(fun cvar => idtac cvar).
  simpl decls_pre.
  do_declare (nat * (word AsyncDisk.Valulen.valulen * bool))%type ltac:(fun xvar => idtac xvar).
  simpl decls_pre.
  do_declare (list (nat * (word AsyncDisk.Valulen.valulen * bool))%type) ltac:(fun xsvar => idtac xsvar).
  eapply hoare_weaken.
  apply CompileUncons with (lvar := nth_var 15 vars)
                             (cvar := nth_var 16 vars)
                             (xvar := nth_var 17 vars)
                             (xsvar := nth_var 18 vars).
  3: cancel_go.
  3: cancel_go.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  intros.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  repeat compile_step.
  compile_step.
  compile_step.
  repeat compile_step.
  compile_step.
  Unshelve. all: compile.
Defined.

Definition eviction_update' a s := Ret (eviction_update s a).

Instance WrapByTransforming_evictionstate : WrapByTransforming eviction_state.
  refine {|
    transform := fun s => tt;
  |}.
  simpl; intros. destruct t1, t2; f_equal; auto.
Defined.

Example compile_eviction_update' : sigT (fun p => source_stmt p /\ forall env a s,
  EXTRACT eviction_update' a s
  {{ 0 ~>? eviction_state * 1 ~> a * 2 ~> s }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? eviction_state }} // env).
Proof.
  unfold eviction_update', eviction_update.
  compile.
Defined.

Eval lazy in (projT1 compile_eviction_update').

Transparent BUFCACHE.read.

Example compile_read : sigT (fun p => source_stmt p /\ forall env a cs,
  prog_func_call_lemma {| FArgs := [with_wrapper cachestate]; FRet := with_wrapper cachestate |}
    "maybe_evict" BUFCACHE.maybe_evict env ->
  prog_func_call_lemma {| FArgs := [with_wrapper W; with_wrapper eviction_state]; FRet := with_wrapper eviction_state |}
    "eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.read a cs
  {{ 0 ~>? (cachestate * (valu * unit)) * 1 ~> a * 2 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.read.
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
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  match goal with
  |- context [(?k ~> a1)%pred] =>
    (* TODO: copy here automatically. This is *the* standard mostly unavoidable copy *)
    do_declare valu ltac:(fun ka' =>
                            eapply CompileBefore; [
                              eapply CompileRet with (v := a1) (var0 := ka');
                              eapply hoare_weaken; [
                                eapply CompileDup with (var0 := k) (var' := ka') | cancel_go .. ] | ])
  end.
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
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  Unshelve.
  all: compile.
Defined.


Transparent BUFCACHE.write.
Example compile_write : sigT (fun p => source_stmt p /\ forall env a v cs,
  prog_func_call_lemma {| FArgs := [with_wrapper cachestate]; FRet := with_wrapper cachestate |}
    "maybe_evict" BUFCACHE.maybe_evict env ->
  prog_func_call_lemma {| FArgs := [with_wrapper W; with_wrapper eviction_state]; FRet := with_wrapper eviction_state |}
    "eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.write a v cs
  {{ 0 ~>? cachestate * 1 ~> a * 2 ~> v * 3 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? valu * 3 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.write.
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
  compile_step.
  compile_step.

  Unshelve.
  all: compile.
Defined.

Transparent BUFCACHE.begin_sync.
Example compile_begin_sync : sigT (fun p => source_stmt p /\ forall env cs,
  EXTRACT BUFCACHE.begin_sync cs
  {{ 0 ~>? cachestate * 1 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? cachestate }} // env).
Proof.
  intros. unfold BUFCACHE.begin_sync.
  (* TODO: make this not split & rejoin :P *)
  compile.
Defined.

Eval lazy in projT1 (compile_begin_sync).

Transparent BUFCACHE.sync.

Example compile_sync : sigT (fun p => source_stmt p /\ forall env a cs,
  prog_func_call_lemma {| FRet := with_wrapper cachestate; FArgs := [with_wrapper addr; with_wrapper cachestate] |} "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.sync a cs
  {{ 0 ~>? cachestate * 1 ~> a * 2 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.sync.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  Unshelve.
  all : compile.
Defined.
Eval lazy in projT1 (compile_sync).


Transparent BUFCACHE.end_sync.
Example compile_end_sync : sigT (fun p => source_stmt p /\ forall env cs,
  EXTRACT BUFCACHE.end_sync cs
  {{ 0 ~>? cachestate * 1 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.end_sync.
  compile.
Defined.


Transparent BUFCACHE.init.
Example compile_init : sigT (fun p => source_stmt p /\ forall env n,
  EXTRACT BUFCACHE.init n
  {{ 0 ~>? cachestate * 1 ~> n }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? nat }} // env).
Proof.
  unfold BUFCACHE.init.
  compile.
Defined.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope pred_scope.

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
  | context [EXTRACT _ {{ ?PRE }} ?body_ {{ ?POST }} // _] =>
    match POST with
    | (fun ret : ?R => ?POST) =>
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
    end
  end.

Ltac add_compiled_program name compiled env :=
  let P := fresh in
  let e_ := fresh in
  let H := fresh in
  let S := fresh "src" in
  destruct compiled as [e_ P];
  match type of P with
  | Logic.and (source_stmt _) _ =>
    apply proj1 in P as S;
    apply proj2 in P
  | Logic.and _ (source_stmt _) =>
    apply proj2 in P as S;
    apply proj1 in P
  end;
  repeat match type of P with
  | forall x : ?X, ?y =>
      let x_ := fresh "v" in
      cut X; [intro x_; specialize (P x_) | solve [abstract (repeat econstructor)] ]
  end;
  try (add_to_env name P env;
  (* Remove unnecessary variables *)
  clear P;
  repeat match goal with
  | [env := ?X, v : _ |- _] =>
    lazymatch type of v with
    | context [ProgOk] => fail
    | _ => clear v
    end
  end).

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "writeback" compile_writeback env.
  add_compiled_program "evict" compile_evict env.
  add_compiled_program "maybe_evict" compile_maybe_evict env.
  add_compiled_program "eviction_update" compile_eviction_update' env.
  add_compiled_program "read" compile_read env.
  add_compiled_program "write" compile_write env.
  add_compiled_program "sync" compile_sync env.
  add_compiled_program "compile_end_sync" compile_end_sync env.
  add_compiled_program "begin_sync" compile_begin_sync env.
  add_compiled_program "end_sync" compile_end_sync env.
  add_compiled_program "init" compile_init env.
  (* TODO add more programs here *)

  exact env.
Defined.
