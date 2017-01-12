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

(*
Example compile_writeback : forall env, sigT (fun p => forall a cs,
  EXTRACT BUFCACHE.writeback a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  unfold BUFCACHE.writeback.
  intros.
  compile.
Defined.


Eval lazy in (projT1 (compile_writeback (StringMap.empty _))).

(* Outputs the following: *)
Check
 Declare (Pair Bool (Pair DiskBlock Bool))
         (fun var : W =>
          Declare (AddrMap (Pair DiskBlock Bool))
            (fun var0 : W =>
             Declare (Pair (AddrMap (Pair DiskBlock Bool)) Num)
               (fun var1 : W =>
                Declare EmptyStruct
                  (fun var2 : W =>
                   Declare Num
                     (fun var3 : W =>
                      Declare Bool
                        (fun var4 : W =>
                         Declare (Pair DiskBlock Bool)
                           (fun var5 : W =>
                            Declare Bool
                              (fun var6 : W =>
                               Declare DiskBlock
                                 (fun var7 : W =>
                                  Declare (AddrMap (Pair DiskBlock Bool))
                                    (fun var8 : W =>
                                     Declare (Pair DiskBlock Bool)
                                       (fun var9 : W =>
                                        Declare Bool
                                          (fun var10 : W =>
                                           Declare (Pair (AddrMap (Pair DiskBlock Bool)) Num)
                                             (fun var11 : W =>
                                              Declare (Pair (AddrMap (Pair DiskBlock Bool)) Num)
                                                (fun var12 : W =>
                                                 Declare (Pair (AddrMap (Pair DiskBlock Bool)) Num)
                                                   (fun var13 : W =>
                                                    (Modify SplitPair (1, var1, var2);
                                                     Modify SplitPair (var1, var0, var3);
                                                     Modify MapFind (var0, 0, var);
                                                     Modify SplitPair (var, var4, var5);
                                                     If Var var4
                                                     Then Modify SplitPair (var5, var7, var6);
                                                          If Var var6
                                                          Then DiskWrite (Var 0) (Var var7);
                                                               var8 <~dup var0;
                                                               __;
                                                               Modify JoinPair (var9, var7, var10);
                                                               __;
                                                               Modify MapAdd (var8, 0, var9);
                                                               Modify JoinPair (var11, var8, var3);
                                                               Modify JoinPair (1, var11, var2)
                                                          Else Modify JoinPair (var12, var0, var3);
                                                               Modify JoinPair (1, var12, var2) EndIf
                                                     Else Modify JoinPair (var13, var0, var3);
                                                          Modify JoinPair (1, var13, var2) EndIf)%go))))))))))))))).

(* Equivalent Go:
func writeback(a *big.Num, cs *CacheState) {
  var v pair_bool_pair_diskblock_bool
  var v0 map_pair_diskblock_bool
  var v1 pair_map_pair_diskblock_bool_bignum
  var v2 struct{}
  var v3 *big.Num
  var v4 bool
  var v5 pair_diskblock_bool
  var v6 bool
  var v7 *[BLOCK_SIZE]byte
  var v8 map_pair_diskblock_bool
  var v9 pair_disblock_bool
  var v10 bool
  var v11 pair_map_pair_diskblock_bool_bignum
  var v12 pair_map_pair_diskblock_bool_bignum
  var v13 pair_map_pair_diskblock_bool_bignum

  v1, v2 = cs.fst, cs.snd
  v0, v3 = v1.fst, v1.snd
  v = MapFind(v0, a)
  v4, v5 = v.fst, v.snd
  if v4 {
    v7, v6 = v5.fst, v5.snd
    if v6 {
      DiskWrite(a, v7)
      v8 = CopyMap(v0)
      v9.fst, v9.snd = v7, v10
      MapAdd(v8, a, v9)
      v11.fst, v11.snd = v8, v3
      cs.fst, cs.snd = v11, v2
    } else {
      v12.fst, v12.snd = v0, v3
      cs.fst, cs.snd = v12, v2
    }
  } else
    v13.fst, v13.snd = v0, v3
    cs.fst, cs.snd = v13, v2
  }
}
*)


Example compile_evict : forall env, sigT (fun p => forall a cs,
  func2_val_ref "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.evict a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  unfold BUFCACHE.evict.
  intros.
  compile.
Defined.

Eval lazy in (projT1 (compile_evict (StringMap.empty _))).

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
  simpl. (* TODO: most of the [simpl]s in GoExtraction.v right now are in the wrong spot -- could add a declarationn in another goal *)
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
  simpl.
  compile_step.
  compile_step.
  eapply hoare_weaken.
  eapply CompileMapElements with (mvar := pair_vec_nthl 0 1 vars) (var0 := pair_vec_nthl 0 14 vars).
  cancel_go.
  cancel_go.
  simpl.
  do_declare bool ltac:(fun cvar => idtac cvar).
  simpl.
  do_declare (nat * (word AsyncDisk.Valulen.valulen * bool))%type ltac:(fun xvar => idtac xvar).
  simpl.
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

Transparent BUFCACHE.sync.
Example compile_sync : forall env, sigT (fun p => forall a cs,
  func2_val_ref "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.sync a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 ~>? addr * 1 ~> ret }} // env).
Proof.
  intros. unfold BUFCACHE.sync.
  compile.
Defined.
Eval lazy in projT1 (compile_sync _).

*)

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
Print BUFCACHE.writeback.

Ltac argtuple pre var :=
  match pre with
  | context [var |-> @wrap ?T ?V ?val] =>
    let X := argtuple pre (S var) in
    let P := constr:(pair PassedByRef (@wrap_type _ V)) in
    match X with
    | (0, tt) => constr:(pair 1 P)
    | (?count, ?X)  => constr:(pair (S count) (pair X P))
    end
  | _ => constr:(pair 0 tt)
  end.

Ltac add_to_env name P env :=
  match type of P with
  | EXTRACT _ {{ ?PRE }} _ {{ fun ret : ?R => ?POST }} // _ =>
    lazymatch constr:(fun ret : mark_ret R => (_:find_ret POST)) with
    | (fun ret => ?rvar) =>
      match PRE with
      | context [?x ~> ?y] =>
        match (argtuple PRE 0) with
        | (?nargs, ?args) =>
          let x_ := fresh in
          set (body := (projT1 (compile_writeback env)));
          set (op := {|
            NumParamVars := nargs;
            ParamVars := args;
            Body := body;
            body_source := ltac:((subst body; simpl; repeat econstructor));
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
  forall x : ?X, ?y =>
    let x_ := fresh "v" in
    cut X; [intro x_; specialize (P x_) | solve [abstract (repeat econstructor)] ]
  end;
  add_to_env name P env;
  (* Remove unnecessary variables *)
  repeat match goal with
  | [env := ?X, v : _ |- _] =>
    clear v
  end.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "BUFCACHE.writeback" compile_writeback env.
  (* TODO add more programs here *)

  exact env.
Defined.