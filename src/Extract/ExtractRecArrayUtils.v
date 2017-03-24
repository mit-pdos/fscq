Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import GoOfWord.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import RecArrayUtils.

Module Type ExtractRASig (RA : RASig).
  Import RA.

  Parameter XPWrapper : GoWrapper xparams.

  Parameter CompileRAStart : sigT (fun xstart => forall xpvar retvar,
    source_stmt (xstart xpvar retvar) /\ forall xp F env,
    EXTRACT (Ret (RAStart xp))
    {{ xpvar ~> xp * retvar ~>? W * F }}
      xstart xpvar retvar
    {{ fun ret => retvar ~> ret * xpvar ~> xp * F }} // env).

  Parameter CompileRALen : sigT (fun xstart => forall xpvar retvar,
    source_stmt (xstart xpvar retvar) /\ forall xp F env,
    EXTRACT (Ret (RALen xp))
    {{ xpvar ~> xp * retvar ~>? W * F }}
      xstart xpvar retvar
    {{ fun ret => retvar ~> ret * xpvar ~> xp * F }} // env).

  Parameter byte_aligned_item : byte_aligned itemtype.
End ExtractRASig.

Module ExtractRecArrayUtils (RA : RASig) (XRA: ExtractRASig RA).

  Module Defs := RADefs RA.
  Import RA Defs XRA.

  Opaque CompileRetSome.

  Lemma compile_ifind_block: forall
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
      Declare (@wrap_type _ (GoWrapper_rec itemtype)) (fun varx =>
      Declare (@wrap_type _ (GoWrapper_rec blocktype)) (fun varb' => (
      Go.Modify (@Go.SetConst Bool true) ^(varCont);
      Go.Modify (@Go.SetConst Num 1) ^(vone);
      projT1 (@CompileRetNone (W * item) _ varr); (* set return value to None *)
      While (Var varCont) (
        Modify Uncons ^( varb, varCont, varx, varb');
        If Var varCont
        Then pcond varx varHdIsValid;
          If Var varHdIsValid
          Then Go.Modify (@Go.SetConst Bool false) ^(varCont);
          Declare (Pair Num (@wrap_type _ (GoWrapper_rec itemtype))) (fun varp => (
            Go.Modify Go.JoinPair ^(varp, vari, varx);
            projT1 (@CompileRetSome (W * item)  _ varp varr)
          ))
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
    eapply hoare_weaken; [ eapply (proj2 (projT2 (CompileRetNone _)) _ _) | cancel_go..].
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
    extract_step_declare varp.
    eapply hoare_weaken.
    eapply CompileRet with (var0 := varr) (v := Some (start, a)).
    eapply extract_equiv_prog with (pr1 := x <- Ret (start, a); Ret (Some x)).
    rewrite ProgMonad.bind_left_id. reflexivity.
    eapply hoare_weaken; [ eapply CompileBindRet with (vara := varp) | cancel_go..].
    eapply hoare_weaken; [ eapply CompileJoin | cancel_go..].
    eapply hoare_weaken.
    eapply (proj2 (projT2 (CompileRetSome _ _))).
    2 : cancel_go.
    2 : cancel_go.
    2 : cancel_go.
    2 : cancel_go.
    cancel_go.
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