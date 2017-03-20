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

  Lemma CompileWhileFalseNoOp : forall A var0 xbody env,
    EXTRACT (Ret tt)
    {{ var0 ~> false * A }}
      Go.While (Var var0) xbody
    {{ fun ret => var0 ~> false * A }} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    repeat exec_solve_step.
    repeat exec_solve_step.
    repeat exec_solve_step.
    contradiction H1.
    repeat eexists.
    apply StepWhileFalse.
    eval_expr.
  Qed.

  Lemma CompileUnconsNil : forall T (W : GoWrapper T) A lvar cvar xvar xsvar env,
    EXTRACT (Ret tt)
    {{ lvar ~> @nil T * cvar ~>? bool * xvar ~>? T * xsvar ~>? list T * A }}
      Modify Uncons ^(lvar, cvar, xvar, xsvar)
    {{ fun _ => lvar |-> Val (Slice wrap_type) Moved * cvar ~> false * xvar ~>? T * xsvar ~> @nil T * A}} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    repeat exec_solve_step.
    repeat exec_solve_step.
    repeat exec_solve_step.
    contradiction H1.
    repeat eexists.
    eapply StepModify;
    [eval_expr; eauto..].
  Qed.

  Lemma CompileUnconsCons : forall T (W : GoWrapper T) A lvar cvar xvar xsvar (x : T) xs env,
    EXTRACT (Ret tt)
    {{ lvar ~> (x :: xs) * cvar ~>? bool * xvar ~>? T * xsvar ~>? list T * A }}
      Modify Uncons ^(lvar, cvar, xvar, xsvar)
    {{ fun _ => lvar |-> Val (Slice wrap_type) Moved * cvar ~> true * xvar ~> x * xsvar ~> xs * A}} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    repeat exec_solve_step.
    repeat exec_solve_step.
    repeat exec_solve_step.
    contradiction H1.
    repeat eexists.
    eapply StepModify;
    [eval_expr; eauto..].
  Qed.

  Lemma CompileWhileTrueOnce : forall A B var0 xp env,
    EXTRACT (Ret tt)
    {{ var0 ~> true * A }}
      xp;
      Go.While (Var var0) xp
    {{ fun _ => B }} // env ->
    EXTRACT (Ret tt)
    {{ var0 ~> true * A }}
      Go.While (Var var0) xp
    {{ fun _ => B }} // env.
  Proof.
    intros. unfold ProgOk.
    inv_exec_progok.
    inv_exec.
    repeat exec_solve_step.
    repeat exec_solve_step.
    repeat exec_solve_step.
    contradiction H2.
    repeat eexists.
    apply StepWhileTrue.
    eval_expr.
  Qed.

  Lemma CompileIfFalse : forall T A B (p : prog T) px qx var0 env,
    EXTRACT p {{ var0 ~> false * A }} px {{ B }} // env ->
    EXTRACT p
    {{ var0 ~> false * A }}
      If (Var var0) Then qx Else px EndIf
    {{ B }} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; eauto.
    cbn; eauto.
    forward_solve.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; eauto.
    cbn; eauto.
    forward_solve.
    inv_exec.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; eauto.
    cbn; eauto.
    forward_solve.
    contradiction H2.
    repeat eexists.
    eapply StepIfFalse.
    eval_expr.
  Qed.

  Lemma CompileIfTrue : forall T A B (p : prog T) px qx var0 env,
    EXTRACT p {{ var0 ~> true * A }} px {{ B }} // env ->
    EXTRACT p
    {{ var0 ~> true * A }}
      If (Var var0) Then px Else qx EndIf
    {{ B }} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; eauto.
    cbn; eauto.
    forward_solve.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; eauto.
    cbn; eauto.
    forward_solve.
    inv_exec.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; eauto.
    cbn; eauto.
    forward_solve.
    contradiction H2.
    repeat eexists.
    eapply StepIfTrue.
    eval_expr.
  Qed.

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
                     projT1
                       (CompileRetSomePair W item vari varx varr)
                Else Modify (ModifyNumOp Plus) ^(vari, vari, vone) EndIf Else 
           __ EndIf;
           varb <~move varb')%go))))))
    {{ fun ret => vari ~>? W * varb ~>? block * varr ~> ret * A }} // env.
  Proof.
    intros.
    eapply CompileDeclare with (Wr := GoWrapper_Num); intros vone.
    eapply CompileDeclare with (Wr := GoWrapper_Bool); intros varHdIsValid.
    eapply CompileDeclare with (Wr := GoWrapper_Bool); intros varCont.
    eapply CompileDeclare with (Wr := Wr); intros varx.
    eapply CompileDeclare with (Wr := @GoWrapper_list _ Wr); intros varb'.
    eapply hoare_strengthen_pre with (A1 := (varb' ~>? (list item) * varx ~>? item * _)%pred); [ cancel_go |].
    eapply CompileBefore.
    eapply CompileRet with (v := true) (var0 := varCont).
    eapply hoare_weaken; [eapply CompileConst with (Wr := GoWrapper_Bool) | cancel_go..].
    eapply CompileBefore.
    eapply CompileRet with (v := 1) (var0 := vone).
    eapply hoare_weaken; [eapply CompileConst with (Wr := GoWrapper_Num) | cancel_go..].

    eapply CompileBefore.
    eapply CompileRet with (v := @None (W * item)) (var0 := varr).
    eapply hoare_weaken; [ eapply (projT2 (CompileRetNone _ _)) | cancel_go..].
    eapply hoare_weaken; [ eapply CompileRet' with (var0 := varr) | cancel_go..].
    revert b start.
    induction b; cbn; intros.
    eapply hoare_weaken; [ eapply CompileWhileTrueOnce | cancel_go..].
    repeat eapply CompileBefore.
    eapply hoare_strengthen_pre; [| eapply CompileUnconsNil with (T := item)]; cancel_go.
    eapply hoare_strengthen_pre; [| eapply CompileIfFalse; compile_step]; cancel_go.
    eapply CompileRet with (v := @nil item) (var0 := varb).
    eapply hoare_weaken; [ eapply CompileMove | cancel_go..].
    eapply hoare_weaken; [ eapply CompileWhileFalseNoOp | cancel_go..].

    destruct cond eqn:Hcond.
    eapply hoare_weaken; [ eapply CompileWhileTrueOnce | cancel_go..].
    repeat eapply CompileBefore.
    eapply hoare_weaken; [ apply CompileUnconsCons with (x := a) (xs := b) | cancel_go..].
    eapply hoare_weaken; [ eapply CompileIfTrue | cancel_go..].
    eapply CompileBefore.
    eapply CompileRet with (var0 := varHdIsValid) (v := cond a start).
    eapply hoare_weaken; [ eapply H | cancel_go..].
    eapply hoare_weaken; [ eapply CompileIfTrue | rewrite ?Hcond; cancel_go..].
    eapply CompileBefore.
    eapply CompileRet with (v := false) (var0 := varCont).
    eapply hoare_weaken; [ apply CompileConst with (Wr := GoWrapper_Bool) (v := varCont) | cancel_go..].
    eapply CompileRet with (var0 := varr) (v := Some (start, a)).
    eapply hoare_weaken.
    apply (projT2 (CompileRetSomePair W item vari varx varr)).
    all : try cancel_go.
    eapply CompileRet with (v := b) (var0 := varb).
    compile_step.
    eapply hoare_weaken; [ eapply CompileWhileFalseNoOp | cancel_go..].

    eapply hoare_weaken; [ eapply CompileWhileTrueOnce | cancel_go..].
    repeat eapply CompileBefore.
    eapply hoare_weaken; [ eapply CompileUnconsCons | cancel_go..].
    eapply hoare_weaken; [ eapply CompileIfTrue | cancel_go..].
    eapply CompileBefore.
    eapply CompileRet with (v := cond a start) (var0 := varHdIsValid).
    eapply hoare_weaken; [ eauto | cancel_go..].
    rewrite Hcond.
    eapply hoare_weaken; [ eapply CompileIfFalse | cancel_go..].
    eapply CompileRet with (v := start + 1) (var0 := vari).
    eapply hoare_weaken; [ eapply CompileAddInPlace1 with (avar := vari) (bvar := vone) | cancel_go..].
    cancel_go.
    eapply CompileRet with (v := b) (var0 := varb).
    eapply hoare_weaken; [apply CompileMove | cancel_go..].
    rewrite PeanoNat.Nat.add_1_r.
    eapply hoare_weaken; [ eauto | cancel_go..].
  Qed.

End ExtractRecArrayUtils.