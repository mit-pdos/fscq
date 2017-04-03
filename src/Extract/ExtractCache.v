Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
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
  prog_func_call_lemma {| FArgs := [with_wrapper addr; with_wrapper cachestate]; FRet := with_wrapper cachestate |} "cache_writeback" BUFCACHE.writeback env ->
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
  prog_func_call_lemma {| FArgs := [with_wrapper addr; with_wrapper cachestate]; FRet := with_wrapper cachestate |} "cache_evict" BUFCACHE.evict env ->
  EXTRACT BUFCACHE.maybe_evict cs
  {{ 0 ~>? cachestate * 1 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.maybe_evict.
  compile.
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
    "cache_maybe_evict" BUFCACHE.maybe_evict env ->
  prog_func_call_lemma {| FArgs := [with_wrapper W; with_wrapper eviction_state]; FRet := with_wrapper eviction_state |}
    "cache_eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.read a cs
  {{ 0 ~>? (cachestate * (immut_word valulen * unit)) * 1 ~> a * 2 ~> cs }}
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
  Ltac a := match goal with
         | [ |- EXTRACT (v <- Read _; _) {{ _ }} _ {{ _ }} // _ ] =>
           compile_step; [
             match goal with
               |- EXTRACT _ {{ ?vara ~>? ?T * _ }} _ {{ _ }} // _ =>
               eapply CompileBefore; [
                 eapply CompileRet with (var0 := vara) (v := ($0 : word 0)) | ]
             end | ]
         | [ |- EXTRACT (Ret (eviction_update ?a ?b)) {{ _ }} _ {{ _ }} // _ ] =>
           change (Ret (eviction_update a b)) with (eviction_update' b a)
         | _ => compile_step
         end.
  do_declare (immut_word valulen) ltac:(fun bvar => idtac bvar).
  eapply hoare_weaken; [
    eapply CompileBind with (T := immut_word valulen) (var0 := nth_var 13 vars) | cancel_go.. ].
  do_declare valu ltac:(fun mvar => idtac mvar).
  let vara := constr:(nth_var 14 vars) in
  let F := fresh "F" in
  evar (F : pred);
  eapply CompileAfter with (B := (fun r : valu => vara ~> r * F)%pred); subst F.
  eapply CompileBefore; [
    eapply CompileRet with (var0 := nth_var 14 vars) (v := ($0 : word 0)) | ].
  compile_step.
  compile_step.
  intro block.
  eapply hoare_weaken; [
    eapply CompileRet with (v := block : immut_word valulen) (var0 := nth_var 13 vars) | cancel_go.. ].
  eapply hoare_weaken; [
    eapply CompileFreeze with (dvar := nth_var 13 vars) (svar := nth_var 14 vars); divisibility | cancel_go.. ].
  intros.
  a.
  a.
  change (valu * bool)%type with (immut_word valulen * bool)%type.
  a.
  change MapUtils.AddrMap.Map.add with Map.add.
  a.
  a.
  a.
  a.
  change valu with (immut_word valulen)%type.
  lazymatch goal with
  | |- EXTRACT Bind (Ret ?x_) ?p
       {{ _ }}
          _
       {{ ?post }} // _ =>
        match type of x_ with
        | ?T_ =>
          idtac x_ T_;
            let Wr_ := constr:(_ : GoWrapper T_) in
            do_declare T_
             ltac:((fun v_ =>
                      eapply hoare_strengthen_pre; [  | eapply CompileBindRet with (vara := v_) (a := x_) ];
                       [ cancel_go | .. ]))
        end
  end.
  match goal with
  | |- EXTRACT Ret (?a_, ?b_)
       {{ ?pre }}
          _
       {{ ?post }} // _ =>
        match find_val a_ pre with
        | Some ?ka =>
            match var_mapping_to_ret with
            | ?kp =>
                let A_ := type of a_ in
                let B_ := type of b_ in
                match find_val b_ pre with
                | Some ?kb =>
                    eapply hoare_weaken;
                        [ apply CompileJoin with (A := A_) (B := B_) (avar := ka) (bvar := kb) (pvar := kp) | cancel_go.. ]
                end
            end
        end
  end.
  solve [repeat a].
  solve [repeat a].
  solve [repeat a].
  change (nth_var 13 vars |-> Val ImmutableBuffer (existT (fun n : W => word n) valulen a1))%pred
         with (nth_var 13 vars ~> a1 : pred)%pred.
  change valu with (immut_word valulen).
  repeat a.

  Unshelve.
  all: compile.
Defined.

Transparent BUFCACHE.read_array.

Example compile_read_array : sigT (fun p => source_stmt p /\  forall env a i cs,
  prog_func_call_lemma {| FArgs := [with_wrapper _ ; with_wrapper _]; FRet := with_wrapper _ |}
    "cache_read" BUFCACHE.read env ->
  EXTRACT BUFCACHE.read_array a i cs
  {{ 0 ~>? (cachestate * (immut_word valulen * unit)) * 1 ~> a * 2 ~> i * 3 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? W * 3 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.read_array.
  compile.
Defined.

Transparent BUFCACHE.write.
Example compile_write : sigT (fun p => source_stmt p /\ forall env a v cs,
  prog_func_call_lemma {| FArgs := [with_wrapper cachestate]; FRet := with_wrapper cachestate |}
    "cache_maybe_evict" BUFCACHE.maybe_evict env ->
  prog_func_call_lemma {| FArgs := [with_wrapper W; with_wrapper eviction_state]; FRet := with_wrapper eviction_state |}
    "cache_eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.write a v cs
  {{ 0 ~>? cachestate * 1 ~> a * 2 ~> v * 3 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? immut_word valulen * 3 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.write.
  repeat (progress change (Ret (eviction_update ?s ?a)) with (eviction_update' a s)
       || compile_step).

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
  unfold BUFCACHE.begin_sync.
  compile.
Defined.

Eval lazy in projT1 (compile_begin_sync).

Transparent BUFCACHE.sync.

Example compile_sync : sigT (fun p => source_stmt p /\ forall env a cs,
  prog_func_call_lemma {| FRet := with_wrapper cachestate; FArgs := [with_wrapper addr; with_wrapper cachestate] |} "cache_writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.sync a cs
  {{ 0 ~>? cachestate * 1 ~> a * 2 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.sync.
  compile.
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

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "cache_writeback" compile_writeback env.
  add_compiled_program "cache_evict" compile_evict env.
  add_compiled_program "cache_maybe_evict" compile_maybe_evict env.
  add_compiled_program "cache_eviction_update" compile_eviction_update' env.
  add_compiled_program "cache_read" compile_read env.
  add_compiled_program "cache_read_array" compile_read_array env.
  add_compiled_program "cache_write" compile_write env.
  add_compiled_program "cache_sync" compile_sync env.
  add_compiled_program "cache_begin_sync" compile_begin_sync env.
  add_compiled_program "cache_end_sync" compile_end_sync env.
  add_compiled_program "cache_init" compile_init env.
  (* TODO add more programs here *)

  exact env.
Defined.
