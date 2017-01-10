Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred.
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

Local Open Scope string_scope.
Local Open Scope list_scope.
Print BUFCACHE.writeback.
Check compile_writeback.

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