Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import RecArrayUtils.

Module ExtractRecArrayUtils (RA : RASig).
  Module Defs := RADefs RA.
  Import RA Defs.

  Instance GoWrapper_block {Wr : GoWrapper item} : GoWrapper block.
    typeclasses eauto.
  Defined.

  (* this is effectively an inlined subroutine; the actual prog only matters during extraction *)
  Lemma CompileRetSomePair : forall T V {WT : GoWrapper T} {WV : GoWrapper V} tvar vvar rvar,
    sigT (fun xp =>
    forall A (t : T) (v : V) env,
    EXTRACT Ret (Some (t, v))
      {{ tvar ~> t * vvar ~> v * rvar ~>? (option (T * V)) * A }}
        xp
      {{ fun ret => rvar ~> ret * tvar ~>? T * vvar ~>? V * A }} // env).
  Proof.
    intros.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    do_declare bool ltac:(fun x => set (avar := x)).
    eapply CompileBefore.
    eapply CompileRet with (v := true) (var0 := avar).
    subst_definitions.
    compile_step.
    eapply hoare_weaken.
    eapply CompileRetOptionSome with (pvar := rvar) (avar := avar) (bvar := nth_var 0 vars).
    all : subst_definitions; cancel_go.
    Unshelve. compile.
  Defined.

  Lemma CompileRetNone : forall T {W : GoWrapper T} rvar,
    sigT (fun xp =>
    forall A env,
    EXTRACT Ret (@None T)
      {{ rvar ~>? (option T) * A }}
        xp
      {{ fun ret => rvar ~> ret * A }} // env).
  Proof.
    intros.
    eexists; intros.
    eapply CompileDeclare with (T := bool).
    intros avar.
    eapply hoare_weaken.
    eapply CompileRetOptionNone with (pvar := rvar) (avar := avar).
    cancel_go.
    cancel_go.
  Defined.

  Opaque CompileRetSomePair CompileRetNone.

  Ltac make_wrapper t := lazymatch t with
    | @wrap_type _ ?H => H
    | Slice ?t =>
      let W := make_wrapper t in
      constr:(@GoWrapper_list _ W)
    | Pair ?a ?b =>
      let Wa := make_wrapper a in
      let Wb := make_wrapper b in
      constr:(GoWrapper_pair Wa Wb)
    | ?T =>
      let T' := eval cbn in (type_denote T) in
      constr:(ltac:(typeclasses eauto) : GoWrapper T')
    end.

  Ltac extract_step_declare name := match goal with
    | [ Wr : GoWrapper _ |- EXTRACT _ {{ _ }} Declare _ _ {{ _ }} // _ ] =>
      eapply CompileDeclare with (Wr := Wr); intros name
    | [ |- EXTRACT _ {{ _ }} Declare ?T_ _ {{ _ }} // _ ] =>
      let Wr_ := make_wrapper T_ in
      eapply CompileDeclare with (Wr := Wr_); intros name
    end.

  Ltac extract_step_modify := match goal with
    | [|- EXTRACT (Ret tt) {{ _ }} Modify (SetConst ?x) ^(?v0) {{ _ }} // _ ] =>
      eapply CompileRet with (v := x) (var0 := v0);
      let T := type of x in
      let Wr_ := constr:(ltac:(typeclasses eauto) : GoWrapper T) in
      eapply hoare_weaken; [eapply CompileConst with (Wr := Wr_) | cancel_go..]
    | [|- EXTRACT (Ret tt) {{ ?pre }} Modify MoveOp ^(?dst, ?src) {{ _ }} // _ ] =>
      match pre with
      | context [(src ~> ?x)%pred] =>
        eapply CompileRet with (var0 := dst) (v := x);
        eapply hoare_weaken; [ eapply CompileMove | cancel_go..]
      end
    | [|- EXTRACT (Ret tt) {{ ?pre }} Modify Uncons ^(?lvar_, ?cvar_, ?xvar_, ?lvar'_) {{ _ }} // _ ] =>
      match pre with
      | context [(lvar_ ~> @nil ?T_)%pred] =>
        eapply hoare_weaken; [
          eapply CompileUnconsNil with (T := T_) |
          cancel_go..
        ]
      | context [(lvar_ ~> (?a :: ?l))%pred] =>
        eapply hoare_weaken; [
          let T_ := type of a in
          eapply CompileUnconsCons with (T := T_) (x := a) (xs := l) |
          cancel_go..
        ]
      end
    end.

  Ltac extract_step_flow := match goal with
    | [|- EXTRACT (Ret tt) {{ ?pre }} While (Var ?v) _ {{ _ }} // _ ] =>
      match pre with
      | context [(v ~> true)%pred] =>
        eapply hoare_weaken; [ eapply CompileWhileTrueOnce | cancel_go..]
      | context [(v ~> false)%pred] =>
        eapply hoare_weaken; [ eapply CompileWhileFalseNoOp | cancel_go..]
      end
    | [|- EXTRACT (Ret tt) {{ ?pre }} If (Var ?v) Then _ Else _ EndIf {{ _ }} // _ ] =>
      match pre with
      | context [(v ~> true)%pred] =>
        eapply hoare_weaken; [ eapply CompileIfTrue | cancel_go..]
      | context [(v ~> false)%pred] =>
        eapply hoare_weaken; [ eapply CompileIfFalse | cancel_go..]
      end
    | [|- EXTRACT (Ret tt) {{ _ }} Skip {{ _ }} // _ ] =>
      eapply CompileSkip
    end.

  Ltac extract_step :=
    extract_step_modify    ||
    extract_step_flow      ||
    match goal with
    | [|- EXTRACT _ {{ _ }} Seq _ _ {{ _ }} // _ ] =>
      eapply CompileBefore
    end.

  Lemma compile_ifind_block: forall (Wr : GoWrapper item)
    cond pcond vari varb varr env,
    (forall varx varr x i A,
    EXTRACT (Ret (cond x i))
    {{ varx ~> x * vari ~> i * varr ~>? bool * A }}
      pcond varx varr
    {{ fun ret => varx ~> x * vari ~> i * varr ~> ret * A }} // env) ->
           forall A start b, EXTRACT (Ret (ifind_block cond b start))
    {{ vari ~> start * varb ~> b * varr ~>? option (W * item) * A }}
      Declare Num (fun vone =>
      Declare Bool (fun varHdIsValid =>
      Declare Bool (fun varCont =>
      Declare wrap_type (fun varx =>
      Declare (Slice wrap_type) (fun varb' => (
      Go.Modify (@Go.SetConst Bool true) ^(varCont);
      Go.Modify (@Go.SetConst Num 1) ^(vone);
      projT1 (CompileRetNone (W * item) varr); (* set return value to None *)
      While (Var varCont) (
        Modify Uncons ^( varb, varCont, varx, varb');
        If Var varCont
        Then pcond varx varHdIsValid;
          If Var varHdIsValid
          Then Go.Modify (@Go.SetConst Bool false) ^(varCont);
            projT1 (CompileRetSomePair W item vari varx varr)
          Else Modify (ModifyNumOp Plus) ^(vari, vari, vone)
          EndIf
        Else Skip
        EndIf;
        varb <~move varb')%go))))))
    {{ fun ret => vari ~>? W * varb ~>? block * varr ~> ret * A }} // env.
  Proof.
    intros.
    extract_step_declare vone.
    extract_step_declare varHdIsValid.
    extract_step_declare varCont.
    extract_step_declare varx.
    extract_step_declare varb'.
    eapply hoare_strengthen_pre with (A1 := (varb' ~>? (list item) * varx ~>? item * _)%pred); [ cancel_go |].
    repeat extract_step.
    eapply CompileRet with (v := @None (W * item)) (var0 := varr).
    eapply hoare_weaken; [ eapply (projT2 (CompileRetNone _ _)) | cancel_go..].
    eapply hoare_weaken; [ eapply CompileRet' with (var0 := varr) | cancel_go..].
    revert b start.
    induction b; cbn; intros.
    repeat (extract_step || cancel_go).

    destruct cond eqn:Hcond.
    repeat extract_step.
    eapply CompileRet with (var0 := varHdIsValid) (v := cond a start).
    eapply hoare_weaken; [ eauto | cancel_go..].
    rewrite Hcond.
    repeat extract_step.
    eapply CompileRet with (var0 := varr) (v := Some (start, a)).
    eapply hoare_weaken.
    apply (projT2 (CompileRetSomePair W item vari varx varr)).
    all : try cancel_go.
    repeat extract_step.
    repeat extract_step.

    repeat extract_step.
    eapply CompileRet with (v := cond a start) (var0 := varHdIsValid).
    eapply hoare_weaken; [ eauto | cancel_go..].
    rewrite Hcond.
    repeat extract_step.
    eapply CompileRet with (v := start + 1) (var0 := vari).
    eapply hoare_weaken; [ eapply CompileAddInPlace1 with (avar := vari) (bvar := vone) | cancel_go..].
    cancel_go.
    repeat extract_step.
    rewrite PeanoNat.Nat.add_1_r.
    eapply hoare_weaken; [ eauto | cancel_go..].
  Qed.

End ExtractRecArrayUtils.