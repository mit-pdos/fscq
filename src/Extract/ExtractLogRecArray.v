Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Require Import ExtractRecArrayUtils.
Require Import GoOfWord.
Import ListNotations.
Import LogRecArray.

Import Go.

Module ExtractLogRecArray (RA : RecArrayUtils.RASig) (XRA : ExtractRASig RA).

  Module RAExtract := ExtractRecArrayUtils RA XRA.
  Module LRA := LogRecArray RA.
  Import XRA LRA RA Defs RAExtract.

  Lemma compile_val2block svar dvar : sigT (fun p => source_stmt p /\ forall val env F,
    EXTRACT (Ret (val2block val))
    {{ dvar ~>? block * svar ~> val * F }}
      p
    {{ fun ret => dvar ~> ret * svar ~>? valu * F }} // env).
  Proof.
    unfold val2block, val2word.
    compile_step.
    eapply CompileDeclare with (Wr := GoWrapper_immut_word _).
    intros val_immut.
    eapply CompileBefore.
    eapply CompileRet with (H := GoWrapper_immut_word _) (v := val) (var0 := val_immut).
    eapply hoare_weaken.
    eapply CompileFreeze with (svar := svar) (dvar := val_immut).
    apply valulen_divide_8.
    cancel_go.
    cancel_go.
    eapply hoare_weaken.
    eapply compile_of_word with (vsrc := val_immut) (vdst := dvar).
    apply byte_aligned_item.
    cancel_go.
    cbv [wrap].
    eq_rect_simpl.
    generalize blocksz_ok.
    generalize dependent valulen.
    cbn; intros ? ? e.
    rewrite <- e.
    eq_rect_simpl.
    cancel_go.
    cancel_go.
    Unshelve. all : compile.
    apply source_stmt_go_of_word.
    exact 0.
  Defined.

  Lemma compile_read : sigT (fun p => source_stmt p /\ forall xp a ms env,
    prog_func_call_lemma {| FArgs := [with_wrapper _; with_wrapper _; with_wrapper _ ];
      FRet := with_wrapper _ |} "grouplog_read" GroupLog.GLog.read env ->
    EXTRACT Log.LOG.read xp a ms
    {{ 0 ~>? (Log.LOG.mstate * Cache.cachestate * (valu * unit))%type * 1 ~> xp * 2 ~> a * 3 ~> ms }}
    p
    {{ fun ret => 0 ~> ret * 1 ~>? FSLayout.log_xparams * 2 ~>? W * 3 ~>? (Log.LOG.mstate * Cache.cachestate)%type }} // env).
  Proof.
    unfold Log.LOG.read.
    compile_step.
    compile_step.
    compile_step.
    repeat compile_step.
    compile_step.
    compile_step.
    rewrite surjective_pairing with (p := ms) at 1.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.

    unfold Log.LOG.MSLL.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    unfold pair_args_helper, Log.LOG.mk_memstate.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_decompose.
    compile_bind.
    repeat compile_step.
    repeat compile_step.
    repeat compile_step.
    repeat compile_step.
    repeat compile_step.
    Unshelve. all: compile.
  Defined.

  Lemma compile_ifind : forall cond env,
    sigT (fun xcond =>
      forall xvar ivar condvar, source_stmt (xcond xvar ivar condvar) /\ forall x i F,
      EXTRACT Ret (cond x i)
      {{ xvar ~> x * ivar ~> i * condvar ~>? bool * F }}
        xcond xvar ivar condvar
      {{ fun ret => condvar ~> ret * xvar ~> x * ivar ~> i * F }} // env
    ) ->
    sigT (fun xxp => forall lxp xp ms,
      prog_func_call_lemma {| FArgs := [with_wrapper _; with_wrapper _; with_wrapper _; with_wrapper _ ];
      FRet := with_wrapper _ |} "log_read_array" Log.LOG.read_array env ->
    EXTRACT ifind lxp xp cond ms
    {{ 0 ~>? (Log.LOG.mstate * Cache.cachestate * (option (W * item) * unit))%type *
       1 ~> lxp * 2 ~> xp * 3 ~> ms }}
       xxp
    {{ fun ret => 0 ~> ret * 1 ~>? FSLayout.log_xparams * 2 ~>? xparams * 3 ~>? (Log.LOG.mstate * Cache.cachestate)%type }} // env).
  Proof.
    intros.
    unfold ifind.
    compile_step.
    compile_step.
    match goal with |- context [BasicProg.ForN_ ?p _ _ ?N ?O] => generalize N; generalize O end.
    intros.
    compile_step.
    compile_step.
    eapply hoare_weaken; [ eapply ((projT2 CompileRALen) 2) | cancel_go..].
    unfold pair_args_helper.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    eapply hoare_weaken; [ eapply CompileBindRet with (vara := nth_var 0 vars) | cancel_go..].
    compile_step.
    compile_step.
    compile_step.
    do_declare bool ltac:(fun contvar_ =>
      eapply CompileBefore;
      [ eapply CompileRet with (v := true) (var0 := contvar_); compile_step |..];
      eapply hoare_weaken; [ eapply CompileForWithBreak with
        (loopvar := nth_var 0 vars) (ivar := nth_var 2 vars)
        (nvar := nth_var 1 vars) (contv := contvar_) | cancel_go..]).
    intros; repeat (f_equal; destruct_pair); destruct u; auto.
    intros.
    eapply CompileBefore.
    do_declare bool ltac:(fun rvar => idtac rvar;
      eapply CompileRet with (v := BasicProg.is_some (fst (snd t))) (var0 := rvar)).
    eapply CompileBefore.
    do_declare (option (W * item)) ltac:(fun ovar =>
      eapply CompileRet with (v := fst (snd t)) (var0 := ovar)).
    repeat compile_step.
    eapply hoare_weaken; [
    eapply CompileIsSome with (ovar := nth_var 6 vars) (varr := nth_var 5 vars) | cancel_go..].
    eapply CompileBefore.
    eapply CompileRet with (v := t) (var0 := nth_var 0 vars).
    rewrite (@surjective_pairing _ _ t) at 1.
    compile_step.
    rewrite (@surjective_pairing _ _ (snd t)) at 1.
    replace (snd (snd t)) with tt by (repeat destruct_pair; destruct u; auto).
    compile_step.
    compile_step.
    repeat compile_step.
    intros.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    let rvar := var_mapping_to_ret in
    eapply hoare_weaken; [ eapply ((projT2 CompileRAStart) 2 rvar) | cancel_go..].
    compile_step.
    compile_step.
    compile_step.
    repeat match goal with
    | [|- EXTRACT (Ret (val2block ?x_)) {{ ?pre }} _ {{ ?post }} // _ ] =>
      let rvar := var_mapping_to_ret in
      let svar := var_mapping_to pre x_ in
      eapply hoare_weaken; [ eapply (projT2 (compile_val2block svar rvar)) | cancel_go..]
    | [|- EXTRACT (Ret (ifind_block _ ?b ?i)) {{ ?pre }} _ {{ ?post }} // _ ] =>
      let rvar := var_mapping_to_ret in
      let ivar := var_mapping_to pre i in
      let bvar := var_mapping_to pre b in
      eapply hoare_weaken; [ eapply compile_ifind_block with (vari := ivar) (varb := bvar) (varr := rvar)
       | cancel_go..]
    | [|- EXTRACT ?P {{ ?pre }} _ {{ ?post }} // _ ] => idtac P; compile_step
    end.
    intros varx varr x' i'. intros.
    match goal with |- EXTRACT _ {{ ?pre }} _ {{ ?post }} // _ =>
      let ivar := var_mapping_to pre i' in
      eapply hoare_weaken; [ eapply (proj2 (projT2 X varx ivar varr)) | cancel_go..]
    end.
    repeat match goal with
    [ |- EXTRACT (Ret (Some ?b)) {{ ?pre }} _ {{ ?post }} // _ ] =>
      let rvar := var_mapping_to_ret in
      let bvar := var_mapping_to pre b in
      eapply hoare_weaken; [
      eapply (proj2 (projT2 (CompileRetSome bvar rvar))) | cancel_go..]
    | [|- EXTRACT ?P {{ ?pre }} _ {{ ?post }} // _ ] => idtac P; compile_step
    end.
    unfold pair_args_helper.
    compile_step.
    (* cancel_go_fast does the wrong thing here - probably instantiates an evar wrong or something *)
    Ltac cancel_go ::= (idtac "cancel_refl failed";
      (solve [ cancel_go_fast ]) || unfold var, default_value; cancel;
      try apply pimpl_refl).
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    repeat match goal with
    | [|- EXTRACT (Ret (?a, ?b)) {{ ?pre }} _ {{ ?post }} // _ ] =>
      let rvar := var_mapping_to_ret in
      let avar_ := var_mapping_to pre a in
      let bvar_ := var_mapping_to pre b in
      eapply hoare_weaken; [ eapply CompileJoin with (pvar := rvar) (avar := avar_) (bvar := bvar_) | ..]
    | [|- EXTRACT ?P {{ ?pre }} _ {{ ?post }} // _ ] => idtac P; compile_step
    end.
    cancel_go_fast.
    match goal with |- context [?x] => is_evar x; generalize dependent x end.
    abstract cancel.
    Unshelve. all : compile.
  Defined.

End ExtractLogRecArray.
