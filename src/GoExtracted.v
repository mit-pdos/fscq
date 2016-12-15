Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred SepAuto.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoTactics2.
Import ListNotations.
Import Go.

Open Scope pred_scope.

Require Import Cache.

Require Import GoSepAuto.

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


Lemma okToCancel_ptsto_any : forall var val,
  okToCancel (var |-> val : pred) (var |->?).
Proof.
  intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (?var |-> ?val) (?var |->?)) =>
  apply okToCancel_ptsto_any : okToCancel.

Lemma okToCancel_ptsto_typed_any_typed : forall T {Wr : GoWrapper T} var (val : T),
  okToCancel (var ~> val : pred) (var ~>? T).
Proof.
  intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (?var ~> ?val) (exists val', ?var |-> Val _ val')) =>
  apply okToCancel_ptsto_typed_any_typed : okToCancel.

Lemma okToCancel_ptsto_any_typed : forall T {Wr : GoWrapper T} var val,
  okToCancel (var |-> Val (@wrap_type T _) val : pred) (var ~>? T).
Proof.
  intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (?var |-> Val _ _) (exists val', ?var |-> Val _ val')) =>
  apply okToCancel_ptsto_any_typed : okToCancel.

Lemma okToCancel_any_any : forall X var V,
  okToCancel (exists x : X, var |-> V x : pred) (var |->?).
Proof.
  intros.
  apply pimpl_exists_l; intros.
  apply pimpl_exists_r. eauto.
Qed.
Hint Extern 0 (okToCancel (exists _, ?var |-> _) (?var |->?)) =>
  apply okToCancel_any_any : okToCancel.

(* TODO: too much of a hack? too slow? *)
Hint Extern 0 (okToCancel (?var |-> _) (exists _, ?var |-> _)) =>
  apply pimpl_exists_r; eexists; reflexivity : okToCancel.

Hint Extern 0 (okToCancel (decls_pre ?decls ?vars) (decls_post ?decls ?vars)) =>
  apply decls_pre_impl_post.

Example compile_writeback : forall env, sigT (fun p => forall a cs,
  EXTRACT BUFCACHE.writeback a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  unfold BUFCACHE.writeback.
  intros.
Ltac cancel_go ::= cancel.
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
  Focus 3. cancel. 
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
    eapply CompileRet' with (var0 := (snd (fst (fst (fst (fst (fst (fst (fst (fst (fst (fst (fst vars))))))))))))).
    eapply CompileSkip.
    cancel_go. cancel_go.
  }
  compile_step.
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
  compile_step.
  compile_step.
  (***********)
  (* This [compile_step] once took 2 minutes. Now it takes 3 seconds! *)
  (***********)
  Time compile_step.
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
  compile_step.
  compile_step.
  compile_step.

  Unshelve.
  all: repeat constructor.
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
func writeback(a *big.Num, cs *CacheMap) {
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