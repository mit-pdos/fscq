Require Import PeanoNat String List FMapAVL Structures.OrderedTypeEx.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import StringMap.
Require Import Eqdep.
Require Import VerdiTactics.
Require Import Word.
Require Import Mem AsyncDisk PredCrash Prog.

Import ListNotations.

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

(* TODO: use Pred.v's *)
Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; intuition subst
  end.

Ltac apply_in_hyp lem :=
  match goal with
  | [ H : _ |- _ ] => eapply lem in H
  end.

Ltac subst_definitions :=
  repeat match goal with
  | [ H := _ |- _ ] => subst H
  end.

Ltac eforward H :=
  match type of H with
  | forall a : ?A, _ =>
    match type of A with
    | Prop => fail 1
    | _ => idtac
    end;
    let v := fresh a in
    evar (v : A); specialize (H v); subst v
  end.

Fixpoint all_some A (l : list (option A)) : option (list A) :=
  match l with
    | [] => Some []
    | x :: xs =>
      match x, all_some xs with
        | Some x0, Some xs0 => Some (x0 :: xs0)
        | _, _ => None
      end
  end.

Notation "R ^*" := (clos_refl_trans_1n _ R) (at level 0).

(*
Semantics for Go
================

* No pointer aliasing. Use pointers for types which can be mutated. (Or for everything?)
* Let the post-extraction phase actually allocate variable names; here the semantics
  promise to give you unique identifiers (currently of type nat) when you Declare.
*)

Notation W := nat. (* Assume bignums? *)

Module VarMap := FMapAVL.Make(Nat_as_OT).

Module Go.

  Definition label := string.
  Definition var := nat.

  Inductive binop := Plus | Minus | Times.
  Inductive test := Eq | Ne | Lt | Le.

  Inductive expr :=
  | Var : var -> expr
  | Const : W -> expr (* TODO: constants of any type. Shoud see how GoWrapper works out for mutable types first *)
  | Binop : binop -> expr -> expr -> expr
  | TestE : test -> expr -> expr -> expr.

  Inductive type :=
  | Num
  | Bool
  | EmptyStruct
  | DiskBlock.

  Definition type_denote (t : type) : Type :=
    match t with
      | Num => W
      | Bool => bool
      | EmptyStruct => unit
      | DiskBlock => valu
    end.

  Definition can_alias t :=
    match t with
      | Num => true
      | Bool => true
      | EmptyStruct => true
      | DiskBlock => false
    end.

  Inductive value :=
  | Val t (v : type_denote t).

  Lemma value_inj :
    forall t v1 v2,
      Val t v1 = Val t v2 -> v1 = v2.
  Proof.
    intros.
    inversion H.
    apply inj_pair2 in H1.
    auto.
  Qed.
  Hint Resolve value_inj : equalities.

  Definition type_of (v : value) :=
    match v with Val t _ => t end.

  Definition default_value (t : type) :=
    match t with
      | Num => Val Num 0
      | Bool => Val Bool false
      | EmptyStruct => Val EmptyStruct tt
      | DiskBlock => Val DiskBlock $0
    end.

  Definition scope := VarMap.t type.
  Definition locals := VarMap.t value.

  Inductive stmt :=
  | Skip : stmt
  | Seq : stmt -> stmt -> stmt
  | If : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt
  | Call (retvars: list var) (* The caller's variables to get the return values *)
         (f: label) (* The function to call *)
         (argvars: list var) (* The caller's variables to pass in *)
  | Declare : type -> (var -> stmt) -> stmt
  | Assign : var -> expr -> stmt
  | DiskRead : var -> expr -> stmt
  | DiskWrite : expr -> expr -> stmt
  (* InCall and Undeclare only appear at runtime *)
  | Undeclare : var -> stmt
  | InCall (s0: locals) (* The stack frame inside the function *)
           (paramvars: list var) (* The function's names for the parameters *)
           (retparamvars: list var) (* The function's names for the returned values *)
           (argvars: list var) (* The caller's variables which it passed in *)
           (retvars: list var) (* The caller's variables which will get the return values *)
           (p: stmt) (* The remaining body *).

  (* Program does not contain an InCall or Undeclare. Could probably be expressed directly if we had generics. *)
  Inductive source_stmt : stmt -> Prop :=
  | SSkip : source_stmt Skip
  | SSeq :
      forall a b,
        source_stmt a ->
        source_stmt b ->
        source_stmt (Seq a b)
  | SIf :
      forall cond t f,
        source_stmt t ->
        source_stmt f ->
        source_stmt (If cond t f)
  | SWhile :
      forall cond body,
        source_stmt body ->
        source_stmt (While cond body)
  | SCall : forall retvars f argvars, source_stmt (Call retvars f argvars)
  | SAssign : forall x e, source_stmt (Assign x e)
  (* TODO: SDeclare should actually insist the body is a source_stmt too *)
  | SDeclare : forall t cont, source_stmt (Declare t cont)
  | SDiskRead : forall x a, source_stmt (DiskRead x a)
  | SDiskWrite : forall a v, source_stmt (DiskWrite a v).

  Fixpoint is_source_stmt (p : stmt) : bool :=
    match p with
      | Seq a b => is_source_stmt a && is_source_stmt b
      | If cond t f => is_source_stmt t && is_source_stmt f
      | While cond body => is_source_stmt body
      | InCall _ _ _ _ _ _ => false
      | Undeclare _ => false
      | _ => true
    end.

  Hint Constructors source_stmt.

  Hint Resolve andb_prop.
  Hint Resolve andb_true_intro.

  Theorem is_source_stmt_sound :
    forall p, is_source_stmt p = true -> source_stmt p.
  Proof.
    induction p; simpl; intuition; try discriminate; find_apply_lem_hyp andb_prop; intuition.
  Qed.

  Theorem is_source_stmt_complete :
    forall p, source_stmt p -> is_source_stmt p = true .
  Proof.
    induction p; simpl; intuition;
    match goal with
      | [ H: source_stmt _ |- _ ] => invc H
    end; auto.
  Qed.

  Definition state := (rawdisk * locals)%type.

  Definition eval_binop (op : binop) a b :=
    match op with
      | Plus => Some (Val Num (a + b))
      | Minus => Some (Val Num (a - b))
      | Times => Some (Val Num (a * b))
    end.

  Definition eval_test_num (op : test) a b :=
    match op with
      | Eq => if Nat.eq_dec a b then Some (Val Bool true) else Some (Val Bool false)
      | Ne => if Nat.eq_dec a b then Some (Val Bool false) else Some (Val Bool true)
      | Lt => if Compare_dec.lt_dec a b then Some (Val Bool true) else Some (Val Bool false)
      | Le => if Compare_dec.le_dec a b then Some (Val Bool true) else Some (Val Bool false)
    end.

  Definition eval_test_bool (op : test) a b :=
    match op with
      | Eq => if Bool.bool_dec a b then Some (Val Bool true) else Some (Val Bool false)
      | Ne => if Bool.bool_dec a b then Some (Val Bool false) else Some (Val Bool true)
      | _ => None
    end.

  Definition eval_binop_m (op : binop) (oa ob : option value) : option value :=
    match oa, ob with
      | Some (Val Num a), Some (Val Num b) => eval_binop op a b
      | _, _ => None
    end.

  Definition eval_test_m (op : test) (oa ob : option value) : option value :=
    match oa, ob with
      | Some (Val Num a), Some (Val Num b) => eval_test_num op a b
      | Some (Val Bool a), Some (Val Bool b) => eval_test_bool op a b
      | _, _ => None
    end.

  Fixpoint eval (st : locals) (e : expr) : option value :=
    match e with
      | Var x => VarMap.find x st
      | Const w => Some (Val Num w)
      | Binop op a b => eval_binop_m op (eval st a) (eval st b)
      | TestE op a b => eval_test_m op (eval st a) (eval st b)
    end.

  Hint Unfold eval.

  Definition eval_bool st e : option bool :=
    match eval st e with
      | Some (Val Bool b) => Some b
      | _ => None
    end.

  Definition is_true st e := eval_bool st e = Some true.
  Definition is_false st e := eval_bool st e = Some false.

  Definition mapsto_can_alias x st :=
    match find x st with
    | Some v => can_alias v
    | None => true
    end.

  Fixpoint add_remove_many keys (input : list value) (output : list (option value)) st :=
    match keys, input, output with
      | k :: keys', i :: input', o :: output' =>
        let st' :=
            match can_alias (type_of i), o with
              | false, Some v => VarMap.add k v st
              | false, None => VarMap.remove k st
              | _, _ => st
            end in
        add_remove_many keys' input' output' st'
      | _, _, _ => st
    end.

  Fixpoint add_many keys (output : list value) st :=
    match keys, output with
      | k :: keys', v :: output' =>
        let st' := VarMap.add k v st in
        add_many keys' output' st'
      | _, _ => st
    end.

  Fixpoint mapM A B (f : A -> option B) ls :=
    match ls with
      | x :: xs =>
        match f x, mapM f xs with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
        end
      | nil => Some nil
    end.

  Local Open Scope bool_scope.

  Fixpoint NoDup_bool A (eqb : A -> A -> bool) (ls : list A) {struct ls} :=
    match ls with
      | nil => true
      | x :: xs => forallb (fun e => negb (eqb e x)) xs && NoDup_bool eqb xs
    end.

  Require Import Bool.

  Lemma NoDup_bool_sound : forall A eqb, (forall a b : A, eqb a b = true <-> a = b) -> forall ls, NoDup_bool eqb ls = true -> NoDup ls.
    induction ls; simpl; intros.
    econstructor.
    apply_in_hyp andb_true_iff.
    intuition.
    econstructor.
    intro.
    apply_in_hyp forallb_forall; eauto.
    apply_in_hyp negb_true_iff.
    replace (eqb a a) with true in *.
    intuition.
    symmetry; eapply H; eauto.
    eauto.
  Qed.

  Definition sumbool_to_bool A B (b : {A} + {B}) := if b then true else false.

  Lemma sumbool_to_bool_dec :
    forall A b,
      @sumbool_to_bool A (~A) b = true <-> A.
  Proof.
    intros.
    unfold sumbool_to_bool.
    destruct b; intuition discriminate.
  Qed.

  Definition string_bool a b := sumbool_to_bool (string_dec a b).

  Definition is_string_eq := string_bool.

  Lemma is_string_eq_iff a b : is_string_eq a b = true <-> a = b.
    unfold is_string_eq, string_bool.
    destruct (string_dec a b); intuition; try discriminate.
  Qed.

  Lemma iff_not_iff P Q : (P <-> Q) -> (~ P <-> ~ Q).
  Proof.
    split; intros; intuition.
  Qed.

  Lemma is_string_eq_iff_conv a b : is_string_eq a b = false <-> a <> b.
  Proof.
    etransitivity.
    { symmetry; eapply not_true_iff_false. }
    eapply iff_not_iff.
    eapply is_string_eq_iff.
  Qed.

  Lemma NoDup_bool_string_eq_sound : forall ls, NoDup_bool string_bool ls = true -> NoDup ls.
    intros.
    eapply NoDup_bool_sound.
    2 : eauto.
    split; intros.
    unfold string_bool, sumbool_to_bool in *; destruct (string_dec a b); try discriminate; eauto.
    unfold string_bool, sumbool_to_bool in *; destruct (string_dec a b); try discriminate; eauto.
  Qed.

  Definition nat_bool a b := sumbool_to_bool (Nat.eq_dec a b).

  Definition is_no_dup := NoDup_bool nat_bool.

  Definition is_in (a : string) ls := if in_dec string_dec a ls then true else false.

  Definition is_none_or_not_in (v : option string) vs :=
    match v with
      | None => true
      | Some rv => negb (is_in rv vs)
    end.

  Record OperationalSpec := {
    ParamVars : list var;
    RetParamVars : list var;
    Body : stmt;
    (* ret_not_in_args : dont_intersect RetParamVars ParamVars = true; *)
    args_no_dup : is_no_dup ParamVars = true;
    body_source : is_source_stmt Body = true;
    (* TODO syntax_ok with is_actual_args_no_dup *)
  }.

  Definition Env := StringMap.t OperationalSpec.

  Record frame := {
    Locs : locals;
    Cont : stmt;
    Spec : OperationalSpec;
    Args : list var;
    RetV : var;
  }.

  Section EnvSection.

    Variable env : Env.

    Definition sel T m := fun k => VarMap.find k m : option T.

    Fixpoint make_map {elt} keys values :=
      match keys, values with
        | k :: keys', v :: values' => VarMap.add k v (make_map keys' values')
        | _, _ => @VarMap.empty elt
      end.

    Eval hnf in rawdisk.

    Definition maybe_add V k (v : V) m :=
      match k with
        | None => m
        | Some kk => VarMap.add kk v m
      end.


    Inductive runsto : stmt -> state -> state -> Prop :=
    | RunsToSkip : forall st,
                     runsto Skip st st
    | RunsToSeq : forall a b st st' st'',
                    runsto a st st' ->
                    runsto b st' st'' ->
                    runsto (Seq a b) st st''
    | RunsToIfTrue : forall cond t f st st',
                       is_true (snd st) cond ->
                       runsto t st st' ->
                       runsto (If cond t f) st st'
    | RunsToIfFalse : forall cond t f st st',
                        is_false (snd st) cond ->
                        runsto f st st' ->
                        runsto (If cond t f) st st'
    | RunsToWhileTrue : forall cond body st st' st'',
                          let loop := While cond body in
                          is_true (snd st) cond ->
                          runsto body st st' ->
                          runsto loop st' st'' ->
                          runsto loop st st''
    | RunsToWhileFalse : forall cond body st,
                           let loop := While cond body in
                           is_false (snd st) cond ->
                           runsto loop st st
    | RunsToDeclare : forall body body' d s si si' s' d' var t,
                       VarMap.find var s = None ->
                       si = VarMap.add var (default_value t) s ->
                       body' = body var ->
                       source_stmt body' ->
                       runsto body' (d, si) (d', si') ->
                       s' = VarMap.remove var si' ->
                       runsto (Declare t body) (d, s) (d', s')
    | RunsToAssign : forall x e d s s' v0 v,
                       eval s e = Some v ->
                       can_alias (type_of v) = true -> (* rhs must be aliasable *)
                       VarMap.find x s = Some v0 -> (* variable must be declared *)
                       type_of v = type_of v0 -> (* and have the correct type *)
                       s' = VarMap.add x v s ->
                       runsto (Assign x e) (d, s) (d, s')
    | RunsToDiskRead : forall x ae a d s s' v vs,
                         eval s ae = Some (Val Num a) ->
                         d a = Some (v, vs) ->
                         s' = VarMap.add x (Val DiskBlock v) s ->
                         runsto (DiskRead x ae) (d, s) (d, s')
    | RunsToDiskWrite : forall ae a ve v (d : rawdisk) d' s v0 v0s,
                          eval s ae = Some (Val Num a) ->
                          eval s ve = Some (Val DiskBlock v) ->
                          d a = Some (v0, v0s) ->
                          d' = upd d a (v, v0 :: v0s) ->
                          runsto (DiskWrite ae ve) (d, s) (d', s)
    | RunsToCall : forall retvars f argvars s spec d d' input callee_s' ret,
                     StringMap.find f env = Some spec ->
                     source_stmt (Body spec) ->
                     length argvars = length (ParamVars spec) ->
                     mapM (sel s) argvars = Some input ->
                     let callee_s := make_map (ParamVars spec) input in
                     runsto (Body spec) (d, callee_s) (d', callee_s') ->
                     all_some (List.map (fun rv => sel callee_s' rv) (RetParamVars spec)) = Some ret ->
                     let output := List.map (sel callee_s') (ParamVars spec) in
                     let s' := add_remove_many argvars input output s in
                     let s' := add_many retvars ret s' in
                     runsto (Call retvars f argvars) (d, s) (d', s').

    Inductive step : state * stmt -> state * stmt -> Prop :=
    | StepSeq1 : forall a a' b st st',
                   step (st, a) (st', a') ->
                   step (st, Seq a b) (st', Seq a' b)
    | StepSeq2 : forall a st,
                   step (st, Seq Skip a) (st, a)
    | StepIfTrue : forall cond t f st,
                     is_true (snd st) cond ->
                     step (st, If cond t f) (st, t)
    | StepIfFalse : forall cond t f st,
                      is_false (snd st) cond ->
                      step (st, If cond t f) (st, f)
    | StepWhileTrue : forall cond body st,
                        let loop := While cond body in
                        is_true (snd st) cond ->
                        step (st, loop) (st, Seq body loop)
    | StepWhileFalse : forall cond body st,
                         let loop := While cond body in
                         is_false (snd st) cond ->
                         step (st, loop) (st, Skip)
    | StepDeclare : forall t body body' d s s' var,
                      VarMap.find var s = None ->
                      s' = VarMap.add var (default_value t) s ->
                      body' = body var ->
                      source_stmt body' ->
                      step (d, s, Declare t body) (d, s', Seq body' (Undeclare var))
    | StepUndeclare : forall var d s s',
                        s' = VarMap.remove var s ->
                        step (d, s, Undeclare var) (d, s', Skip)
    | StepAssign : forall x e d s s' v v0,
                     (* rhs can't be a mutable object, to prevent aliasing *)
                     eval s e = Some v ->
                     can_alias (type_of v) = true -> (* rhs must be aliasable *)
                     VarMap.find x s = Some v0 -> (* variable must be declared *)
                     type_of v = type_of v0 -> (* and have the correct type *)
                     s' = VarMap.add x v s ->
                     step (d, s, Assign x e) (d, s', Skip)
    | StepDiskRead : forall x ae a d s s' v vs,
                       eval s ae = Some (Val Num a) ->
                       d a = Some (v, vs) ->
                       s' = VarMap.add x (Val DiskBlock v) s ->
                       step (d, s, DiskRead x ae) (d, s', Skip)
    | StepDiskWrite : forall ae a ve v d d' s v0 v0s,
                        eval s ae = Some (Val Num a) ->
                        eval s ve = Some (Val DiskBlock v) ->
                        d a = Some (v0, v0s) ->
                        d' = upd d a (v, v0 :: v0s) ->
                        step (d, s, DiskWrite ae ve) (d', s, Skip)
    | StepStartCall :
        forall s retvars f argvars spec d input,
          StringMap.find f env = Some spec ->
          source_stmt (Body spec) ->
          length argvars = length (ParamVars spec) ->
          mapM (sel s) argvars = Some input ->
          let callee_s := make_map (ParamVars spec) input in
          step (d, s, Call retvars f argvars) (d, callee_s, InCall s spec.(ParamVars) spec.(RetParamVars) argvars retvars spec.(Body))
    | StepInCall :
        forall st p st' p' s0 paramvars retparamvars argvars retvars,
          step (st, p) (st', p') ->
          step (st, InCall s0 paramvars retparamvars argvars retvars p)
               (st', InCall s0 paramvars retparamvars argvars retvars p')
    | StepEndCall :
        forall callee_s' s d input retvals paramvars retparamvars argvars retvars,
          mapM (sel s) argvars = Some input ->
          length argvars = length paramvars ->
          all_some (List.map (fun rv => sel callee_s' rv) retparamvars) = Some retvals ->
          let output := List.map (sel callee_s') paramvars in
          let s' := add_remove_many argvars input output s in
          let s' := add_many retvars retvals s' in
          step (d, callee_s', InCall s paramvars retparamvars argvars retvars Skip) (d, s', Skip).

    Inductive outcome :=
    | Failed
    | Finished (st : rawdisk * locals)
    | Crashed (d : rawdisk).

    Inductive crash_step : stmt -> Prop :=
    | CrashSeq1 : forall a b,
                    crash_step a ->
                    crash_step (Seq a b)
    | CrashInCall : forall s argvars retvar args ret p,
                      crash_step p ->
                      crash_step (InCall s argvars retvar args ret p)
    | CrashRead : forall x a,
                    crash_step (DiskRead x a)
    | CrashWrite : forall a v,
                     crash_step (DiskWrite a v).

    Definition is_final (sst : state * stmt) : Prop :=
      snd sst = Skip.

    Hint Unfold is_final.

    Inductive exec : state * stmt -> outcome -> Prop :=
    | XStep : forall sst sst' out,
                 step sst sst' ->
                 exec sst' out ->
                 exec sst out
    | XFail : forall sst,
                 (~exists st' p', step sst (st', p')) ->
                 ~is_final sst ->
                 exec sst Failed
    | XCrash : forall d s p,
                  crash_step p ->
                  exec (d, s, p) (Crashed d)
    | XDone : forall st,
                 exec (st, Skip) (Finished st).

    Hint Constructors exec runsto step.

    Hint Constructors clos_refl_trans_1n.

    Definition rt1n_front := Relation_Operators.rt1n_trans.

    Lemma rt1n_trans' : forall A R x y z,
                          clos_refl_trans_1n A R x y ->
                          clos_refl_trans_1n A R y z ->
                          clos_refl_trans_1n A R x z.
    Proof.
      eauto using clos_rt_rt1n, clos_rt1n_rt, rt_trans.
    Qed.

    Hint Extern 1 (clos_refl_trans_1n _ _ ?x ?y) =>
    match goal with
      | _ => is_evar x; fail 1
      | _ => is_evar y; fail 1
      | _ => eapply rt1n_trans'
    end.


    Ltac do_inv :=
      match goal with
        | [ H : step _ _ |- _ ] => invc H; eauto
        | [ H : clos_refl_trans_1n _ _ _ _ |- _ ] => invc H; eauto
      end.

    Lemma steps_incall :
      forall s0 argvars retvars args ret st p st' p',
        step^* (st, p) (st', p') ->
        step^* (st, InCall s0 argvars retvars args ret p) (st', InCall s0 argvars retvars args ret p').
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. eauto.
    Qed.
    Hint Resolve steps_incall.

    Lemma steps_sequence :
      forall p0 st p st' p',
        step^* (st, p) (st', p') ->
        step^* (st, Seq p p0) (st', Seq p' p0).
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. eauto.
    Qed.
    Hint Resolve steps_sequence.

    (* For some reason (probably involving tuples), the [Hint Constructors] isn't enough. *)
    Hint Extern 1 (step (_, Assign _ _) _) =>
    eapply StepAssign.
    Hint Extern 1 (step (_, Declare _ _) _) =>
    eapply StepDeclare.
    Hint Extern 1 (step (_, Undeclare _) _) =>
    eapply StepUndeclare.
    Hint Extern 1 (step (_, DiskRead _ _) _) =>
    eapply StepDiskRead.
    Hint Extern 1 (step (_, DiskWrite _ _) _) =>
    eapply StepDiskWrite.
    Hint Extern 1 (step (_, Call _ _ _) _) =>
    eapply StepStartCall.
    Hint Extern 1 (step (_, InCall _ _ _ _ _ _) _) =>
    eapply StepEndCall.

    Theorem runsto_Steps :
      forall p st st',
        runsto p st st' ->
        step^* (st, p) (st', Skip).
    Proof.
      intros.
      induction H; subst_definitions; subst; eauto 10.
    Qed.

    Inductive runsto_InCall : stmt -> state -> state -> Prop :=
    (* We'd have to duplicate all the [runsto] constructors which are recursive anyway *)
    | RunsToICSkip : forall st,
                       runsto_InCall Skip st st
    | RunsToICSeq : forall a b st st' st'',
                      runsto_InCall a st st' ->
                      runsto_InCall b st' st'' ->
                      runsto_InCall (Seq a b) st st''
    | RunsToICIfTrue : forall cond t f st st',
                         is_true (snd st) cond ->
                         runsto_InCall t st st' ->
                         runsto_InCall (If cond t f) st st'
    | RunsToICIfFalse : forall cond t f st st',
                          is_false (snd st) cond ->
                          runsto_InCall f st st' ->
                          runsto_InCall (If cond t f) st st'
    | RunsToICWhileTrue : forall cond body st st' st'',
                            let loop := While cond body in
                            is_true (snd st) cond ->
                            runsto_InCall body st st' ->
                            runsto_InCall loop st' st'' ->
                            runsto_InCall loop st st''
    | RunsToICWhileFalse : forall cond body st,
                             let loop := While cond body in
                             is_false (snd st) cond ->
                             runsto_InCall loop st st
    | RunsToICDeclare : forall body body' d s si si' s' d' var t,
                          VarMap.find var s = None ->
                          si = VarMap.add var (default_value t) s ->
                          body' = body var ->
                          source_stmt body' ->
                          runsto_InCall body' (d, si) (d', si') ->
                          s' = VarMap.remove var si' ->
                          runsto_InCall (Declare t body) (d, s) (d', s')
    | RunsToUndeclare : forall var d s s',
                          s' = VarMap.remove var s ->
                          runsto_InCall (Undeclare var) (d, s) (d, s')
    | RunsToICAssign : forall x e d s s' v0 v,
                         eval s e = Some v ->
                         can_alias (type_of v) = true -> (* rhs must be aliasable *)
                         VarMap.find x s = Some v0 -> (* variable must be declared *)
                         type_of v = type_of v0 -> (* and have the correct type *)
                         s' = VarMap.add x v s ->
                         runsto_InCall (Assign x e) (d, s) (d, s')
    | RunsToICDiskRead : forall x ae a d s s' v vs,
                           eval s ae = Some (Val Num a) ->
                           d a = Some (v, vs) ->
                           s' = VarMap.add x (Val DiskBlock v) s ->
                           runsto_InCall (DiskRead x ae) (d, s) (d, s')
    | RunsToICDiskWrite : forall ae a ve v d d' s v0 v0s,
                            eval s ae = Some (Val Num a) ->
                            eval s ve = Some (Val DiskBlock v) ->
                            d a = Some (v0, v0s) ->
                            d' = upd d a (v, v0 :: v0s) ->
                            runsto_InCall (DiskWrite ae ve) (d, s) (d', s)
    | RunsToICCallOp : forall retvars f argvars s spec d d' input callee_s' retvals,
                         StringMap.find f env = Some spec ->
                         source_stmt (Body spec) ->
                         length argvars = length (ParamVars spec) ->
                         mapM (sel s) argvars = Some input ->
                         let callee_s := make_map (ParamVars spec) input in
                         runsto_InCall (Body spec) (d, callee_s) (d', callee_s') ->
                         all_some (List.map (fun rv => sel callee_s' rv) (RetParamVars spec)) = Some retvals ->
                         let output := List.map (sel callee_s') (ParamVars spec) in
                         let s' := add_remove_many argvars input output s in
                         let s' := add_many retvars retvals s' in
                         runsto_InCall (Call retvars f argvars) (d, s) (d', s')
    | RunsToInCall : forall s0 paramvars retparamvars argvars retvars input retvals p d d' callee_s callee_s',
                       mapM (sel s0) argvars = Some input ->
                       length argvars = length paramvars ->
                       all_some (List.map (fun rv => sel callee_s' rv) retparamvars) = Some retvals ->
                       let output := List.map (sel callee_s') paramvars in
                       let s' := add_remove_many argvars input output s0 in
                       let s' := add_many retvars retvals s' in
                       runsto_InCall p (d, callee_s) (d', callee_s') ->
                       runsto_InCall (InCall s0 paramvars retparamvars argvars retvars p) (d, callee_s) (d', s').

    Hint Constructors source_stmt.

    Lemma source_stmt_RunsToInCall_runsto :
      forall p,
        source_stmt p ->
        forall st st',
          runsto_InCall p st st' ->
          runsto p st st'.
    Proof.
      induction 2; intros; subst_definitions; invc H; eauto.
    Qed.

    Hint Resolve source_stmt_RunsToInCall_runsto.

    Hint Constructors runsto_InCall.

    Lemma runsto_RunsToInCall :
      forall p st st',
        runsto p st st' ->
        runsto_InCall p st st'.
    Proof.
      induction 1; intros; subst_definitions; eauto.
    Qed.

    Hint Resolve runsto_RunsToInCall.

    Ltac inv_runsto :=
      match goal with
        | [ H: runsto ?c _ _ |- _ ] =>
          (is_var c; fail 1) ||
                             invc H
        | [ H: runsto_InCall _ _ _ |- _ ] =>
          invc H
      end.

    Lemma step_runsto :
      forall st p st' p' st'',
        step (st, p) (st', p') ->
        runsto_InCall p' st' st'' ->
        runsto_InCall p st st''.
    Proof.
      intros.
      prep_induction H0; induction H0; intros; subst_definitions; subst; do_inv.
      - subst_definitions. eauto.
      - destruct st', st''. invc H0_0. eauto.
      - eapply RunsToICCallOp; eauto. assert (Some input = Some input0) by congruence. find_inversion. auto.
      - destruct st. eapply RunsToInCall; eauto.
    Qed.

    Hint Resolve step_runsto.

    Theorem Steps_runsto' :
      forall p st st',
        step^* (st, p) (st', Skip) ->
        runsto_InCall p st st'.
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. eauto.
    Qed.

    Theorem Steps_runsto :
      forall p st st',
        source_stmt p ->
        step^* (st, p) (st', Skip) ->
        runsto p st st'.
    Proof.
      intros.
      eauto using Steps_runsto'.
    Qed.

    Theorem ExecFinished_Steps : forall p st st',
                                   exec (st, p) (Finished st') ->
                                   step^* (st, p) (st', Skip).
    Proof.
      intros.
      prep_induction H; induction H; intros; subst; try discriminate.
      + destruct sst'. eauto.
      + repeat find_inversion. eauto.
    Qed.

    Theorem Steps_ExecFinished : forall p st st',
                                   step^* (st, p) (st', Skip) ->
                                   exec (st, p) (Finished st').
    Proof.
      intros.
      prep_induction H; induction H; intros; subst; try discriminate.
      + find_inversion. eauto.
      + destruct y. eauto.
    Qed.

    Theorem ExecCrashed_Steps : forall p st d',
                                  exec (st, p) (Crashed d') ->
                                  exists s' p', step^* (st, p) (d', s', p') /\ crash_step p'.
    Proof.
      intros.
      prep_induction H; induction H; intros; subst; try discriminate.
      + destruct sst'. specialize (IHexec _ _ _ eq_refl eq_refl). repeat deex. eauto 8.
      + find_inversion. find_inversion. eauto 8.
    Qed.

    Theorem Steps_ExecCrashed : forall st p d' s' p',
                                  step^* (st, p) (d', s', p') ->
                                  crash_step p' ->
                                  exec (st, p) (Crashed d').
    Proof.
      intros.
      destruct st.
      prep_induction H; induction H; intros; subst.
      + repeat find_inversion. eauto.
      + destruct y. destruct s. eauto.
    Qed.

    Theorem ExecFailed_Steps :
      forall st p,
        exec (st, p) Failed ->
        exists st' p', step^* (st, p) (st', p') /\ ~is_final (st', p') /\ ~exists st'' p'', step (st', p') (st'', p'').
    Proof.
      intros.
      unfold is_final; simpl.
      prep_induction H; induction H; intros; subst; try discriminate; eauto.
      - destruct sst'. repeat eforward IHexec. repeat conclude IHexec eauto. repeat deex.
        eauto 10.
    Qed.

    Theorem Steps_ExecFailed :
      forall st p st' p',
        ~is_final (st', p') ->
        (~exists st'' p'', step (st', p') (st'', p'')) ->
        step^* (st, p) (st', p') ->
        exec (st, p) Failed.
    Proof.
      induction 3; eauto.
    Qed.

    Lemma Steps_Seq :
      forall p1 p2 p' st st'',
        step^* (st, Seq p1 p2) (st'', p') ->
        (exists p1', step^* (st, p1) (st'', p1') /\ p' = Seq p1' p2) \/
        (exists st', step^* (st, p1) (st', Skip) /\ step^* (st', p2) (st'', p')).
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. invc H.
        + destruct (IHclos_refl_trans_1n _ _ _ _ _ eq_refl eq_refl); eauto; deex; eauto.
        + eauto.
    Qed.

  End EnvSection.
  
End Go.

Notation "A < B" := (Go.TestE Go.Lt A B) : go_scope.
Notation "A <= B" := (Go.TestE Go.Le A B) : go_scope.
Notation "A <> B" := (Go.TestE Go.Ne A B) : go_scope.
Notation "A = B" := (Go.TestE Go.Eq A B) : go_scope.
Delimit Scope go_scope with go.

Notation "! x" := (x = 0)%go (at level 70, no associativity).
Notation "A * B" := (Go.Binop Go.Times A B) : go_scope.
Notation "A + B" := (Go.Binop Go.Plus A B) : go_scope.
Notation "A - B" := (Go.Binop Go.Minus A B) : go_scope.

Notation "A ; B" := (Go.Seq A B) (at level 201, B at level 201, left associativity, format "'[v' A ';' '/' B ']'") : go_scope.
Notation "x <~ y" := (Go.Assign x y) (at level 90) : go_scope.
Notation "'__'" := (Go.Skip) : go_scope.
Notation "'While' A B" := (Go.While A B) (at level 200, A at level 0, B at level 1000, format "'[v    ' 'While'  A '/' B ']'") : go_scope.
Notation "'If' a 'Then' b 'Else' c 'EndIf'" := (Go.If a b c) (at level 200, a at level 1000, b at level 1000, c at level 1000) : go_scope.

