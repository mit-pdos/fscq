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
    "maybe_evict" BUFCACHE.maybe_evict env ->
  prog_func_call_lemma {| FArgs := [with_wrapper W; with_wrapper eviction_state]; FRet := with_wrapper eviction_state |}
    "eviction_update" eviction_update' env ->
  EXTRACT BUFCACHE.read a cs
  {{ 0 ~>? (cachestate * (valu * unit)) * 1 ~> a * 2 ~> cs }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? addr * 2 ~>? cachestate }} // env).
Proof.
  unfold BUFCACHE.read.
  repeat match goal with
  (* TODO: copy here automatically. This is *the* standard mostly unavoidable copy *)
  | [ |- EXTRACT (v <- Read _; _) {{ _ }} _ {{ _ }} // _ ] =>
    compile_step; [
      solve [repeat compile_step] |
      match goal with
      |- EXTRACT _ {{ ?vara ~> ?a * _ }} _ {{ _ }} // _ =>
        do_duplicate a
      end
    ]
  | [ |- EXTRACT (Ret (eviction_update ?a ?b)) {{ _ }} _ {{ _ }} // _ ] =>
    change (Ret (eviction_update a b)) with (eviction_update' b a)
  | _ => compile_step
  end.
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
  prog_func_call_lemma {| FRet := with_wrapper cachestate; FArgs := [with_wrapper addr; with_wrapper cachestate] |} "writeback" BUFCACHE.writeback env ->
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
