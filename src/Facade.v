Require Import PeanoNat String List FMapAVL.
Require Import Relation_Operators Operators_Properties.
Require Import VerdiTactics.
Require Import StringMap.
Require Import Mem AsyncDisk PredCrash Prog ProgMonad SepAuto.
Require Import Gensym.
Require Import Word.
Require Import ProofIrrelevance.

Import ListNotations.

(* TODO: Split into more files *)

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

Hint Constructors step fail_step crash_step exec.

Definition label := string.
Definition var := string.

Notation W := nat. (* Assume bignums? *)

Inductive binop := Plus | Minus | Times.
Inductive test := Eq | Ne | Lt | Le.

Inductive Expr :=
| Var : var -> Expr
| Const : W -> Expr
| Binop : binop -> Expr -> Expr -> Expr
| TestE : test -> Expr -> Expr -> Expr.

Notation "A < B" := (TestE Lt A B) : facade_scope.
Notation "A <= B" := (TestE Le A B) : facade_scope.
Notation "A <> B" := (TestE Ne A B) : facade_scope.
Notation "A = B" := (TestE Eq A B) : facade_scope.
Delimit Scope facade_scope with facade.

Notation "! x" := (x = 0)%facade (at level 70, no associativity).
Notation "A * B" := (Binop Times A B) : facade_scope.
Notation "A + B" := (Binop Plus A B) : facade_scope.
Notation "A - B" := (Binop Minus A B) : facade_scope.

Section Extracted.

  Inductive Value :=
  | Num : W -> Value
  | EmptyStruct : Value
  | Block : valu -> Value.

  Definition can_alias v :=
    match v with
      | Num _ => true
      | EmptyStruct => true
      | Block _ => false
    end.

  Definition Locals := StringMap.t Value.

  Inductive Stmt :=
  | Skip : Stmt
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr -> Stmt -> Stmt -> Stmt
  | While : Expr -> Stmt -> Stmt
  | Call : var -> label -> list var -> Stmt
  | Assign : var -> Expr -> Stmt
  | DiskRead : var -> Expr -> Stmt
  | DiskWrite : Expr -> Expr -> Stmt
  (* Only appears at runtime *)
  | InCall (s0: Locals) (argvars: list var) (retvar: var) (args: list var) (ret: var) (p: Stmt).

  (* Everything program does not contain an InCall. Could probably be expressed directly if we had generics. *)
  Inductive SourceStmt : Stmt -> Prop :=
  | SSkip : SourceStmt Skip
  | SSeq :
      forall a b,
        SourceStmt a ->
        SourceStmt b ->
        SourceStmt (Seq a b)
  | SIf :
      forall cond t f,
        SourceStmt t ->
        SourceStmt f ->
        SourceStmt (If cond t f)
  | SWhile :
      forall cond body,
        SourceStmt body ->
        SourceStmt (While cond body)
  | SCall : forall x f args, SourceStmt (Call x f args)
  | SAssign : forall x e, SourceStmt (Assign x e)
  | SDiskRead : forall x a, SourceStmt (DiskRead x a)
  | SDiskWrite : forall a v, SourceStmt (DiskWrite a v).

  Definition State := (rawdisk * Locals)%type.
  Import StringMap.

  Definition eval_binop (op : binop + test) a b :=
    match op with
      | inl Plus => a + b
      | inl Minus => a - b
      | inl Times => a * b
      | inr Eq => if Nat.eq_dec a b then 1 else 0
      | inr Ne => if Nat.eq_dec a b then 0 else 1
      | inr Lt => if Compare_dec.lt_dec a b then 1 else 0
      | inr Le => if Compare_dec.le_dec a b then 1 else 0
    end.

  Definition eval_binop_m (op : binop + test) (oa ob : option Value) : option Value :=
    match oa, ob with
      | Some (Num a), Some (Num b) => Some (Num (eval_binop op a b))
      | _, _ => None
    end.

  Fixpoint eval (st : Locals) (e : Expr) : option Value :=
    match e with
      | Var x => find x st
      | Const w => Some (Num w)
      | Binop op a b => eval_binop_m (inl op) (eval st a) (eval st b)
      | TestE op a b => eval_binop_m (inr op) (eval st a) (eval st b)
    end.

  Definition eval_bool st e : option bool :=
    match eval st e with
      | Some (Num w) => Some (if Nat.eq_dec w 0 then false else true)
      | _ => None
    end.

  Definition is_true st e := eval_bool st e = Some true.
  Definition is_false st e := eval_bool st e = Some false.

  Definition mapsto_can_alias x st :=
    match find x st with
    | Some v => can_alias v
    | None => true
    end.


  Fixpoint add_remove_many keys (input : list Value) (output : list (option Value)) st :=
    match keys, input, output with
      | k :: keys', i :: input', o :: output' =>
        let st' :=
            match can_alias i, o with
              | false, Some v => add k v st
              | false, None => StringMap.remove k st
              | _, _ => st
            end in
        add_remove_many keys' input' output' st'
      | _, _, _ => st
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

  Definition is_no_dup := NoDup_bool string_bool.

  Definition is_in (a : string) ls := if in_dec string_dec a ls then true else false.

  Record OperationalSpec := {
    ArgVars : list string;
    RetVar : string;
    Body : Stmt;
    ret_not_in_args : negb (is_in RetVar ArgVars) = true;
    args_no_dup : is_no_dup ArgVars = true;
    (* TODO syntax_ok with is_actual_args_no_dup *)
  }.

  Definition Env := StringMap.t OperationalSpec.

  Record frame := {
    Locs : Locals;
    Cont : Stmt;
    Spec : OperationalSpec;
    Args : list var;
    RetV : var;
  }.

End Extracted.

Notation "R ^*" := (clos_refl_trans_1n _ R) (at level 0).

Section EnvSection.

  Import StringMap.

  Variable env : Env.

  Definition sel T m := fun k => find k m : option T.


  Fixpoint make_map {elt} keys values :=
    match keys, values with
      | k :: keys', v :: values' => add k v (make_map keys' values')
      | _, _ => @empty elt
    end.

  Eval hnf in rawdisk.

  Inductive RunsTo : Stmt -> State -> State -> Prop :=
  | RunsToSkip : forall st,
      RunsTo Skip st st
  | RunsToSeq : forall a b st st' st'',
      RunsTo a st st' ->
      RunsTo b st' st'' ->
      RunsTo (Seq a b) st st''
  | RunsToIfTrue : forall cond t f st st',
      is_true (snd st) cond ->
      RunsTo t st st' ->
      RunsTo (If cond t f) st st'
  | RunsToIfFalse : forall cond t f st st',
      is_false (snd st) cond ->
      RunsTo f st st' ->
      RunsTo (If cond t f) st st'
  | RunsToWhileTrue : forall cond body st st' st'',
      let loop := While cond body in
      is_true (snd st) cond ->
      RunsTo body st st' ->
      RunsTo loop st' st'' ->
      RunsTo loop st st''
  | RunsToWhileFalse : forall cond body st,
      let loop := While cond body in
      is_false (snd st) cond ->
      RunsTo loop st st
  | RunsToAssign : forall x e d s s' v,
      (* rhs can't be a mutable object, to prevent aliasing *)
      eval s e = Some v ->
      can_alias v = true ->
      s' = add x v s ->
      RunsTo (Assign x e) (d, s) (d, s')
  | RunsToDiskRead : forall x ae a d s s' v vs,
      eval s ae = Some (Num a) ->
      d a = Some (v, vs) ->
      s' = add x (Block v) s ->
      RunsTo (DiskRead x ae) (d, s) (d, s')
  | RunsToDiskWrite : forall ae a ve v d d' s v0 v0s,
      eval s ae = Some (Num a) ->
      eval s ve = Some (Block v) ->
      d a = Some (v0, v0s) ->
      d' = upd d a (v, v0 :: v0s) ->
      RunsTo (DiskWrite ae ve) (d, s) (d', s)
  | RunsToCallOp : forall x f args s spec d d' input callee_s' ret,
      StringMap.find f env = Some spec ->
      SourceStmt (Body spec) ->
      length args = length (ArgVars spec) ->
      mapM (sel s) args = Some input ->
      let callee_s := make_map (ArgVars spec) input in
      RunsTo (Body spec) (d, callee_s) (d', callee_s') ->
      sel callee_s' (RetVar spec) = Some ret ->
      let output := List.map (sel callee_s') (ArgVars spec) in
      let s' := add_remove_many args input output s in
      let s' := add x ret s' in
      RunsTo (Call x f args) (d, s) (d', s').

  Inductive Step : State * Stmt -> State * Stmt -> Prop :=
  | StepSeq1 : forall a a' b st st',
      Step (st, a) (st', a') ->
      Step (st, Seq a b) (st', Seq a' b)
  | StepSeq2 : forall a st,
      Step (st, Seq Skip a) (st, a)
  | StepIfTrue : forall cond t f st,
      is_true (snd st) cond ->
      Step (st, If cond t f) (st, t)
  | StepIfFalse : forall cond t f st,
      is_false (snd st) cond ->
      Step (st, If cond t f) (st, f)
  | StepWhileTrue : forall cond body st,
      let loop := While cond body in
      is_true (snd st) cond ->
      Step (st, loop) (st, Seq body loop)
  | StepWhileFalse : forall cond body st,
      let loop := While cond body in
      is_false (snd st) cond ->
      Step (st, loop) (st, Skip)
  | StepAssign : forall x e d s s' v,
      (* rhs can't be a mutable object, to prevent aliasing *)
      eval s e = Some v ->
      can_alias v = true ->
      s' = add x v s ->
      Step (d, s, Assign x e) (d, s', Skip)
  | StepDiskRead : forall x ae a d s s' v vs,
      eval s ae = Some (Num a) ->
      d a = Some (v, vs) ->
      s' = add x (Block v) s ->
      Step (d, s, DiskRead x ae) (d, s', Skip)
  | StepDiskWrite : forall ae a ve v d d' s v0 v0s,
      eval s ae = Some (Num a) ->
      eval s ve = Some (Block v) ->
      d a = Some (v0, v0s) ->
      d' = upd d a (v, v0 :: v0s) ->
      Step (d, s, DiskWrite ae ve) (d', s, Skip)
  | StepStartCall :
      forall x f args s spec d input,
        StringMap.find f env = Some spec ->
        SourceStmt (Body spec) ->
        length args = length (ArgVars spec) ->
        mapM (sel s) args = Some input ->
        let callee_s := make_map (ArgVars spec) input in
        Step (d, s, Call x f args) (d, callee_s, InCall s spec.(ArgVars) spec.(RetVar) args x spec.(Body))
  | StepInCall :
      forall st p st' p' s0 argvars retvar args ret,
        Step (st, p) (st', p') ->
        Step (st, InCall s0 argvars retvar args ret p) (st', InCall s0 argvars retvar args ret p')
  | StepEndCall :
      forall callee_s' s d input retval argvars retvar args ret,
        mapM (sel s) args = Some input ->
        length args = length argvars ->
        sel callee_s' retvar = Some retval ->
        let output := List.map (sel callee_s') argvars in
        let s' := add_remove_many args input output s in
        let s' := add ret retval s' in
        Step (d, callee_s', InCall s argvars retvar args ret Skip) (d, s', Skip).

  Inductive Outcome :=
  | EFailed
  | EFinished (st : rawdisk * Locals)
  | ECrashed (d : rawdisk).

  Inductive CrashStep : Stmt -> Prop :=
  | CrashSeq1 : forall a b,
      CrashStep a ->
      CrashStep (Seq a b)
  | CrashInCall : forall s argvars retvar args ret p,
      CrashStep p ->
      CrashStep (InCall s argvars retvar args ret p)
  | CrashRead : forall x a,
      CrashStep (DiskRead x a)
  | CrashWrite : forall a v,
      CrashStep (DiskWrite a v).

  Definition is_final (sst : State * Stmt) : Prop :=
    snd sst = Skip.

  Inductive Exec : State * Stmt -> Outcome -> Prop :=
  | EXStep : forall sst sst' out,
    Step sst sst' ->
    Exec sst' out ->
    Exec sst out
  | EXFail : forall sst,
    (~exists sst', Step sst sst') ->
    ~is_final sst ->
    Exec sst EFailed
  | EXCrash : forall d s p,
    CrashStep p ->
    Exec (d, s, p) (ECrashed d)
  | EXDone : forall st,
    Exec (st, Skip) (EFinished st).

  Hint Constructors Exec RunsTo Step : steps.

  Hint Constructors clos_refl_trans_1n : steps.

  Definition rt1n_front := Relation_Operators.rt1n_trans.

  Lemma rt1n_trans' : forall A R x y z,
    clos_refl_trans_1n A R x y ->
    clos_refl_trans_1n A R y z ->
    clos_refl_trans_1n A R x z.
  Proof.
    eauto using clos_rt_rt1n, clos_rt1n_rt, rt_trans with steps.
  Qed.

  Hint Extern 1 (clos_refl_trans_1n _ _ ?x ?y) =>
    match goal with
    | _ => is_evar x; fail 1
    | _ => is_evar y; fail 1
    | _ => eapply rt1n_trans'
    end : steps.


  Ltac do_inv :=
    match goal with
    | [ H : Step _ _ |- _ ] => invc H; eauto with steps
    | [ H : clos_refl_trans_1n _ _ _ _ |- _ ] => invc H; eauto with steps
    end.

  Lemma steps_incall :
    forall s0 argvars retvar args ret st p st' p',
      Step^* (st, p) (st', p') ->
      Step^* (st, InCall s0 argvars retvar args ret p) (st', InCall s0 argvars retvar args ret p').
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    - find_inversion. eauto with steps.
    - destruct y. eauto with steps.
  Qed.
  Hint Resolve steps_incall : steps.
    
  Lemma steps_sequence :
    forall p0 st p st' p',
      Step^* (st, p) (st', p') ->
      Step^* (st, Seq p p0) (st', Seq p' p0).
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    - find_inversion. eauto with steps.
    - destruct y. eauto with steps.
  Qed.
  Hint Resolve steps_sequence : steps.

  (* For some reason (probably involving tuples), the [Hint Constructors] isn't enough. *)
  Hint Extern 1 (Step (_, Assign _ _) _) =>
    eapply StepAssign : steps.
  Hint Extern 1 (Step (_, DiskRead _ _) _) =>
    eapply StepDiskRead : steps.
  Hint Extern 1 (Step (_, DiskWrite _ _) _) =>
    eapply StepDiskWrite : steps.
  Hint Extern 1 (Step (_, Call _ _ _) _) =>
    eapply StepStartCall : steps.
  Hint Extern 1 (Step (_, InCall _ _ _ _ _ _) _) =>
    eapply StepEndCall : steps.

  Theorem RunsTo_Steps :
    forall p st st',
      RunsTo p st st' ->
      Step^* (st, p) (st', Skip).
  Proof.
    intros.
    induction H; subst_definitions; subst; eauto 10 with steps.
  Qed.

  Inductive RunsTo_InCall : Stmt -> State -> State -> Prop :=
  (* We'd have to duplicate all the [RunsTo] constructors which are recursive anyway *)
  | RunsToICSkip : forall st,
      RunsTo_InCall Skip st st
  | RunsToICSeq : forall a b st st' st'',
      RunsTo_InCall a st st' ->
      RunsTo_InCall b st' st'' ->
      RunsTo_InCall (Seq a b) st st''
  | RunsToICIfTrue : forall cond t f st st',
      is_true (snd st) cond ->
      RunsTo_InCall t st st' ->
      RunsTo_InCall (If cond t f) st st'
  | RunsToICIfFalse : forall cond t f st st',
      is_false (snd st) cond ->
      RunsTo_InCall f st st' ->
      RunsTo_InCall (If cond t f) st st'
  | RunsToICWhileTrue : forall cond body st st' st'',
      let loop := While cond body in
      is_true (snd st) cond ->
      RunsTo_InCall body st st' ->
      RunsTo_InCall loop st' st'' ->
      RunsTo_InCall loop st st''
  | RunsToICWhileFalse : forall cond body st,
      let loop := While cond body in
      is_false (snd st) cond ->
      RunsTo_InCall loop st st
  | RunsToICAssign : forall x e d s s' v,
      (* rhs can't be a mutable object, to prevent aliasing *)
      eval s e = Some v ->
      can_alias v = true ->
      s' = add x v s ->
      RunsTo_InCall (Assign x e) (d, s) (d, s')
  | RunsToICDiskRead : forall x ae a d s s' v vs,
      eval s ae = Some (Num a) ->
      d a = Some (v, vs) ->
      s' = add x (Block v) s ->
      RunsTo_InCall (DiskRead x ae) (d, s) (d, s')
  | RunsToICDiskWrite : forall ae a ve v d d' s v0 v0s,
      eval s ae = Some (Num a) ->
      eval s ve = Some (Block v) ->
      d a = Some (v0, v0s) ->
      d' = upd d a (v, v0 :: v0s) ->
      RunsTo_InCall (DiskWrite ae ve) (d, s) (d', s)
  | RunsToICCallOp : forall x f args s spec d d' input callee_s' ret,
      StringMap.find f env = Some spec ->
      SourceStmt (Body spec) ->
      length args = length (ArgVars spec) ->
      mapM (sel s) args = Some input ->
      let callee_s := make_map (ArgVars spec) input in
      RunsTo_InCall (Body spec) (d, callee_s) (d', callee_s') ->
      sel callee_s' (RetVar spec) = Some ret ->
      let output := List.map (sel callee_s') (ArgVars spec) in
      let s' := add_remove_many args input output s in
      let s' := add x ret s' in
      RunsTo_InCall (Call x f args) (d, s) (d', s')
  | RunsToInCall : forall s0 x args argvars retvar input ret p d d' callee_s callee_s',
      mapM (sel s0) args = Some input ->
      length args = length argvars ->
      sel callee_s' retvar = Some ret ->
      let output := List.map (sel callee_s') argvars in
      let s' := add_remove_many args input output s0 in
      let s' := add x ret s' in
      RunsTo_InCall p (d, callee_s) (d', callee_s') ->
      RunsTo_InCall (InCall s0 argvars retvar args x p) (d, callee_s) (d', s').

  Hint Constructors SourceStmt.

  Lemma SourceStmt_RunsToInCall_RunsTo :
    forall p,
      SourceStmt p ->
      forall st st',
        RunsTo_InCall p st st' ->
        RunsTo p st st'.
  Proof.
    induction 2; intros; subst_definitions; invc H; eauto with steps.
  Qed.

  Hint Resolve SourceStmt_RunsToInCall_RunsTo : steps.

  Hint Constructors RunsTo_InCall : steps.

  Lemma RunsTo_RunsToInCall :
    forall p st st',
      RunsTo p st st' ->
      RunsTo_InCall p st st'.
  Proof.
    induction 1; intros; subst_definitions; eauto with steps.
  Qed.

  Hint Resolve RunsTo_RunsToInCall : steps.

  Ltac inv_runsto :=
    match goal with
    | [ H: RunsTo ?c _ _ |- _ ] =>
      (is_var c; fail 1) ||
      invc H
    | [ H: RunsTo_InCall _ _ _ |- _ ] =>
      invc H
    end.

  Lemma Step_RunsTo :
    forall st p st' p' st'',
      Step (st, p) (st', p') ->
      RunsTo_InCall p' st' st'' ->
      RunsTo_InCall p st st''.
  Proof.
    intros.
    prep_induction H0; induction H0; intros; subst_definitions; subst; do_inv.
    - subst_definitions. eauto with steps.
    - eapply RunsToICCallOp; eauto. assert (Some input = Some input0) by congruence. find_inversion. auto.
    - destruct st. eapply RunsToInCall; eauto.
  Qed.

  Hint Resolve Step_RunsTo : steps.

  Theorem Steps_RunsTo' :
    forall p st st',
      Step^* (st, p) (st', Skip) ->
      RunsTo_InCall p st st'.
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    - find_inversion. eauto with steps.
    - destruct y. eauto with steps.
  Qed.

  Theorem Steps_RunsTo :
    forall p st st',
      SourceStmt p ->
      Step^* (st, p) (st', Skip) ->
      RunsTo p st st'.
  Proof.
    intros.
    eauto using Steps_RunsTo' with steps.
  Qed.

  Theorem ExecFinished_Steps : forall p st st',
    Exec (st, p) (EFinished st') ->
    Step^* (st, p) (st', Skip).
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + destruct sst'. eauto with steps.
    + repeat find_inversion. eauto with steps.
  Qed.

  Theorem Steps_ExecFinished : forall p st st',
    Step^* (st, p) (st', Skip) ->
    Exec (st, p) (EFinished st').
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + find_inversion. eauto with steps.
    + destruct y. eauto with steps.
  Qed.

  Theorem ExecCrashed_Steps : forall p st d',
    Exec (st, p) (ECrashed d') ->
    exists s' p', Step^* (st, p) (d', s', p') /\ CrashStep p'.
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + destruct sst'. specialize (IHExec _ _ _ eq_refl eq_refl). repeat deex. eauto 8 with steps.
    + find_inversion. find_inversion. eauto 8 with steps.
  Qed.

  Theorem Steps_ExecCrashed : forall st p d' s' p',
    Step^* (st, p) (d', s', p') ->
    CrashStep p' ->
    Exec (st, p) (ECrashed d').
  Proof.
    intros.
    destruct st.
    prep_induction H; induction H; intros; subst.
    + repeat find_inversion. eauto with steps.
    + destruct y. destruct s. eauto with steps.
  Qed.

  Lemma Steps_Seq :
    forall p1 p2 p' st st'',
      Step^* (st, Seq p1 p2) (st'', p') ->
      (exists p1', Step^* (st, p1) (st'', p1') /\ p' = Seq p1' p2) \/
      (exists st', Step^* (st, p1) (st', Skip) /\ Step^* (st', p2) (st'', p')).
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    - find_inversion. eauto with steps.
    - destruct y. invc H.
      + destruct (IHclos_refl_trans_1n _ _ _ _ _ eq_refl eq_refl); eauto; deex; eauto with steps.
      + eauto with steps.
  Qed.

End EnvSection.

Notation "A ; B" := (Seq A B) (at level 201, B at level 201, left associativity, format "'[v' A ';' '/' B ']'") : facade_scope.
Notation "x <~ y" := (Assign x y) (at level 90) : facade_scope.
Notation "'__'" := (Skip) : facade_scope.
Notation "'While' A B" := (While A B) (at level 200, A at level 0, B at level 1000, format "'[v    ' 'While'  A '/' B ']'") : facade_scope.
Notation "'If' a 'Then' b 'Else' c 'EndIf'" := (If a b c) (at level 200, a at level 1000, b at level 1000, c at level 1000) : facade_scope.


(* TODO What here is actually necessary? *)

Class FacadeWrapper (WrappingType WrappedType: Type) :=
  { wrap:        WrappedType -> WrappingType;
    wrap_inj: forall v v', wrap v = wrap v' -> v = v' }.

Inductive ScopeItem :=
| SItem A {H: FacadeWrapper Value A} (v : A).

Notation "∅" := (StringMap.empty _) : map_scope.
Notation "k ->> v ;  m" := (StringMap.add k v m) (at level 21, right associativity) : map_scope.
Notation "k ~> v ;  m" := (StringMap.add k (SItem v) m) (at level 21, right associativity) : map_scope.
Delimit Scope map_scope with map.

Definition Scope := StringMap.t ScopeItem.

Definition SameValues (s : StringMap.t Value) (tenv : Scope) :=
  Forall
    (fun item =>
      match item with
      | (key, SItem val) =>
        match StringMap.find key s with
        | Some v => v = wrap val
        | None => False
        end
      end)
    (StringMap.elements tenv).

Notation "ENV \u2272 TENV" := (SameValues ENV TENV) (at level 50).

Definition ProgOk T env eprog (sprog : prog T) (initial_tstate : Scope) (final_tstate : T -> Scope) :=
  forall initial_state hm,
    (snd initial_state) \u2272 initial_tstate ->
    (forall final_state,
      Exec env (initial_state, eprog) (EFinished final_state) ->
      exists r hm',
        exec (fst initial_state) hm sprog (Finished (fst final_state) hm' r) /\
        (snd final_state) \u2272 (final_tstate r)) /\
    (forall final_disk,
      Exec env (initial_state, eprog) (ECrashed final_disk) ->
      exists hm',
        exec (fst initial_state) hm sprog (Crashed T final_disk hm')) /\
    (Exec env (initial_state, eprog) EFailed ->
      exec (fst initial_state) hm sprog (Failed T)).

Notation "'EXTRACT' SP {{ A }} EP {{ B }} // EV" :=
  (ProgOk EV EP%facade SP A B)
    (at level 60, format "'[v' 'EXTRACT'  SP '/' '{{'  A  '}}' '/'    EP '/' '{{'  B  '}}'  //  EV ']'").

Ltac FacadeWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | [ H : _ * _ |- _ ] => destruct H
                   | [ H : unit |- _ ] => destruct H
                   | [ H : _ = _ |- _ ] => inversion H; solve [eauto]
                   | _ => solve [eauto]
                   end).

Instance FacadeWrapper_Self {A: Type} : FacadeWrapper A A.
Proof.
  refine {| wrap := id;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_Num : FacadeWrapper Value W.
Proof.
  refine {| wrap := Num;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_valu : FacadeWrapper Value valu.
Proof.
  refine {| wrap := Block;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_unit : FacadeWrapper Value unit.
Proof.
  refine {| wrap := fun _ => EmptyStruct;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_dec {P Q} : FacadeWrapper Value ({P} + {Q}).
Proof.
  refine {| wrap := fun (v : {P} + {Q}) => if v then Num 1 else Num 0;
            wrap_inj := _ |}.
  destruct v; destruct v'; try congruence; intros; f_equal; apply proof_irrelevance.
Defined.

Definition extract_code := projT1.

Local Open Scope string_scope.

Local Open Scope map_scope.

Ltac find_cases var st := case_eq (StringMap.find var st); [
  let v := fresh "v" in
  let He := fresh "He" in
  intros v He; rewrite ?He in *
| let Hne := fresh "Hne" in
  intro Hne; rewrite Hne in *; exfalso; solve [ intuition idtac ] ].

Ltac inv_exec :=
  match goal with
  | [ H : Step _ _ _ |- _ ] => invc H
  | [ H : Exec _ _ _ |- _ ] => invc H
  | [ H : CrashStep _ |- _ ] => invc H
  end; try discriminate.

Example micro_noop : sigT (fun p =>
  EXTRACT Ret tt
  {{ ∅ }}
    p
  {{ fun _ => ∅ }} // ∅).
Proof.
  eexists.
  intro.
  instantiate (1 := Skip).
  intros.
  repeat split; intros; subst.
  econstructor.
  repeat inv_exec. exists hm. intuition.
  repeat inv_exec.
  repeat inv_exec.
  contradiction H2.
  econstructor; eauto.
Defined.

(*
Theorem extract_finish_equiv : forall A {H: FacadeWrapper Value A} scope cscope pr p,
  (forall d0,
    {{ SItemDisk (NTSome "disk") d0 (ret tt) :: scope }}
      p
    {{ [ SItemDisk (NTSome "disk") d0 pr; SItemRet (NTSome "out") d0 pr ] }} {{ cscope }} // disk_env) ->
  forall st st' d0,
    st \u2272 ( SItemDisk (NTSome "disk") d0 (ret tt) :: scope) ->
    RunsTo disk_env p st st' ->
    exists d', find "disk" st' = Some (Disk d') /\ exists r, @computes_to A pr d0 d' r.
Proof.
  unfold ProgOk.
  intros.
  specialize (H0 d0 st ltac:(auto)).
  intuition.
  specialize (H5 st' ltac:(auto)).
  simpl in *.
  find_cases "disk" st.
  find_cases "disk" st'.
  intuition.
  repeat deex.
  intuition eauto.
Qed.

Theorem extract_crash_equiv : forall A pscope scope pr p,
  (forall d0,
    {{ SItemDisk (NTSome "disk") d0 (ret tt) :: scope }}
      p
    {{ pscope }} {{ [ SItemDiskCrash (NTSome "disk") d0 pr ] }} // disk_env) ->
  forall st p' st' d0,
    st \u2272 (SItemDisk (NTSome "disk") d0 (ret tt) :: scope) ->
    (Step disk_env)^* (p, st) (p', st') ->
    exists d', find "disk" st' = Some (Disk d') /\ @computes_to_crash A pr d0 d'.
Proof.
  unfold ProgOk.
  intros.
  specialize (H d0 st ltac:(auto)).
  intuition.
  specialize (H st' p').
  simpl in *.
  intuition. find_cases "disk" st'.
  repeat deex. eauto.
Qed.
*)

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


Lemma extract_equiv_prog : forall T env A (B : T -> _) pr1 pr2 p,
  prog_equiv pr1 pr2 ->
  EXTRACT pr1
  {{ A }}
    p
  {{ B }} // env ->
  EXTRACT pr2
  {{ A }}
    p
  {{ B }} // env.
Proof.
  unfold prog_equiv, ProgOk.
  intros.
  repeat eforward H0. conclude H0 eauto. intuition.
  eforward H2. conclude H2 eauto. repeat deex.
  repeat eexists; eauto. apply H; eauto.
  eforward H0. conclude H0 eauto. repeat deex.
  repeat eexists; eauto. apply H; eauto.
  apply H; eauto.
Qed.

Lemma Forall_elements_add : forall V P k (v : V) m,
  Forall P (StringMap.elements (StringMap.add k v m)) <->
  P (k, v) /\ Forall P (StringMap.elements (StringMap.remove k m)).
Admitted.

(* TODO: Setoid rewriting? *)
Lemma Forall_elements_equal: forall V P (m1 m2 : StringMap.t V),
  Forall P (StringMap.elements m1) ->
  StringMap.Equal m2 m1 ->
  Forall P (StringMap.elements m2).
Admitted.
Hint Resolve Forall_elements_equal. (* in hintdb? *)

Lemma add_remove_comm : forall V k1 k2 (v : V) m,
  k1 <> k2 ->
  StringMap.Equal (StringMap.add k2 v (StringMap.remove k1 m)) (StringMap.remove k1 (StringMap.add k2 v m)).
Admitted.

Lemma add_remove_comm' : forall V k1 k2 (v : V) m,
  k1 <> k2 ->
  StringMap.Equal (StringMap.remove k1 (StringMap.add k2 v m)) (StringMap.add k2 v (StringMap.remove k1 m)).
Admitted.

Lemma add_remove_same : forall V k (v : V) m,
  StringMap.Equal (StringMap.remove k (StringMap.add k v m)) (StringMap.remove k m).
Admitted.

Lemma add_add_comm : forall V k1 k2 v1 v2 (m : StringMap.t V),
  k1 <> k2 ->
  StringMap.Equal (StringMap.add k2 v2 (StringMap.add k1 v1 m))
                  (StringMap.add k1 v1 (StringMap.add k2 v2 m)).
Admitted.

Lemma remove_remove_comm : forall V k1 k2 (m : StringMap.t V),
  k1 <> k2 ->
  StringMap.Equal (StringMap.remove k2 (StringMap.remove k1 m)) (StringMap.remove k1 (StringMap.remove k2 m)).
Admitted.

Lemma Forall_elements_remove_weaken : forall V P k (m : StringMap.t V),
  Forall P (StringMap.elements m) ->
  Forall P (StringMap.elements (StringMap.remove k m)).
Proof.
Admitted.

Lemma forall_In_Forall_elements : forall V (P : _ -> Prop) m,
  (forall k (v : V), StringMap.find k m = Some v -> P (k, v)) ->
  Forall P (StringMap.elements m).
Proof.
Admitted.

Lemma Forall_elements_forall_In : forall V (P : _ -> Prop) m,
  Forall P (StringMap.elements m) ->
  (forall k (v : V), StringMap.find k m = Some v -> P (k, v)).
Proof.
Admitted.

Lemma remove_empty : forall V k,
  StringMap.Equal (StringMap.remove k (StringMap.empty V)) (StringMap.empty V).
Proof.
  intros. intro.
  rewrite StringMapFacts.remove_o. destruct (StringMapFacts.eq_dec k y); eauto.
Qed.
Hint Resolve remove_empty.

Lemma Forall_elements_empty : forall V P,
  Forall P (StringMap.elements (StringMap.empty V)).
Proof.
  compute.
  auto.
Qed.
Hint Resolve Forall_elements_empty.

Lemma possible_sync_refl : forall AT AEQ (m: @mem AT AEQ _), possible_sync m m.
Proof.
  intros.
  unfold possible_sync.
  intros.
  destruct (m a).
  destruct p.
  right. repeat eexists. unfold incl. eauto.
  eauto.
Qed.

Hint Immediate possible_sync_refl.

Ltac set_hyp_evars :=
  repeat match goal with
  | [ H : context[?e] |- _ ] =>
    is_evar e;
    let H := fresh in
    set (H := e) in *
  end.

Ltac maps := unfold SameValues in *; repeat match goal with
  | [ H : Forall _ (StringMap.elements _) |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
      apply Forall_elements_add in H;
      destruct H as [H1 H2];
      try (eapply Forall_elements_equal in H2; [ | apply add_remove_comm; solve [ congruence ] ])
  | [ |- Forall _ (StringMap.elements _) ] =>
      apply Forall_elements_add; split
  | _ => discriminate
  | _ => congruence
  | _ => set_evars; set_hyp_evars; progress rewrite ?StringMapFacts.remove_neq_o, ?StringMapFacts.remove_eq_o,
                          ?StringMapFacts.add_neq_o, ?StringMapFacts.add_eq_o,
                          ?StringMapFacts.empty_o in * by congruence; subst_evars
  end.

Ltac find_all_cases :=
  repeat match goal with
  | [ H : match StringMap.find ?d ?v with | Some _ => _ | None => _ end |- _ ] => find_cases d v
  end; subst.

Lemma write_fails_not_present:
  forall env (a : W) (v : valu) st,
    StringMap.find "v" (snd st) = Some (wrap v) ->
    StringMap.find "a" (snd st) = Some (wrap a) ->
    ~ (exists st', Step env (st, DiskWrite (Var "a") (Var "v")) st') ->
    fst st a = None.
Proof.
  intros.
  assert (~exists v0, fst st a = Some v0).
  intuition.
  deex.
  contradiction H1.
  destruct v0, st. eexists. econstructor; eauto.
  destruct (fst st a); eauto. contradiction H2. eauto.
Qed.

Hint Resolve write_fails_not_present.

Example micro_write : sigT (fun p => forall a v,
  EXTRACT Write a v
  {{ "a" ~> a; "v" ~> v; ∅ }}
    p
  {{ fun _ => ∅ }} // ∅).
Proof.
  eexists.
  intros.
  instantiate (1 := (DiskWrite (Var "a") (Var "v"))%facade).
  intro. intros.
  maps.
  find_all_cases.
  intuition idtac.

  exists tt. eexists.
  repeat inv_exec. simpl in *. rewrite He, He0 in *. find_inversion. find_inversion.
  repeat eexists; intuition eauto.

  repeat inv_exec; eauto.

  repeat inv_exec; eauto.
  contradiction H0. econstructor; eauto.
Defined.

Lemma CompileSkip : forall env A,
  EXTRACT Ret tt
  {{ A }}
    Skip
  {{ fun _ => A }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition. econstructor.

  repeat inv_exec; eauto.
  repeat inv_exec; eauto.
  repeat inv_exec. contradiction H2. unfold is_final; eauto.
Qed.

Lemma CompileConst : forall env A var v,
  EXTRACT Ret v
  {{ A }}
    var <~ Const v
  {{ fun ret => var ~> ret; A }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition. econstructor.

  repeat inv_exec. simpl in *. find_inversion.
  repeat eexists. eauto. maps. trivial.
  eapply forall_In_Forall_elements. intros.
  pose proof (Forall_elements_forall_In _ H).
  simpl in *.
  destruct (StringMapFacts.eq_dec k var0); maps; try discriminate.
  specialize (H1 k v0 ltac:(eauto)). auto.

  repeat inv_exec; eauto.
  repeat inv_exec. contradiction H1; unfold is_final; eauto.
  contradiction H1. eexists. econstructor; simpl; eauto.
Qed.

Lemma CompileVar : forall env A var T (v : T) {H : FacadeWrapper Value T},
  EXTRACT Ret v
  {{ var ~> v; A }}
    Skip
  {{ fun ret => var ~> ret; A }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition. econstructor.

  repeat inv_exec; eauto.
  repeat inv_exec; eauto.
  repeat inv_exec; eauto.
  contradiction H3; unfold is_final; eauto.
Qed.

Lemma CompileBind : forall T T' {H: FacadeWrapper Value T} env A (B : T' -> _) p f xp xf var,
  EXTRACT p
  {{ A }}
    xp
  {{ fun ret => var ~> ret; A }} // env ->
  (forall (a : T),
    EXTRACT f a
    {{ var ~> a; A }}
      xf
    {{ B }} // env) ->
  EXTRACT Bind p f
  {{ A }}
    xp; xf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition.

  (* TODO: automate proof. ([crush] can probably do this) *)
  - subst. find_eapply_lem_hyp ExecFinished_Steps. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFinished.
    specialize (H0 _ hm ltac:(eauto)).
    intuition. specialize (H3 _ ltac:(eauto)). repeat deex.
    specialize (H1 _ _ hm' ltac:(eauto)). intuition.
    specialize (H3 _ ltac:(eauto)). repeat deex.
    eexists. exists hm'0. intuition eauto.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H5. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      repeat eforward H0. specialize (H0 ltac:(eauto)). intuition.
      specialize (H0 _ ltac:(eauto)). repeat deex; eauto.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      repeat eforward H0. conclude H0 eauto. intuition.
      eforward H3. conclude H3 eauto. repeat deex.
      repeat eforward H1. conclude H1 eauto. intuition.
      eforward H1. conclude H1 eauto. repeat deex.
      eauto.

  - admit.
Qed.

Lemma hoare_weaken_post : forall T env A (B1 B2 : T -> _) pr p,
  (forall x k e, StringMap.find k (B2 x) = Some e -> StringMap.find k (B1 x) = Some e) ->
  EXTRACT pr
  {{ A }} p {{ B1 }} // env ->
  EXTRACT pr
  {{ A }} p {{ B2 }} // env.
Proof.
  unfold ProgOk.
  intros.
  repeat eforward H0. conclude H0 eauto.
  intuition.
  eforward H0. conclude H0 eauto. repeat deex.
  repeat eexists; eauto.
  unfold SameValues in *.
  apply forall_In_Forall_elements. intros.
  eapply Forall_elements_forall_In in H6; eauto.
Qed.

Lemma hoare_strengthen_pre : forall T env A1 A2 (B : T -> _) pr p,
  (forall k e, StringMap.find k A1 = Some e -> StringMap.find k A2 = Some e) ->
  EXTRACT pr
  {{ A1 }} p {{ B }} // env ->
  EXTRACT pr
  {{ A2 }} p {{ B }} // env.
Proof.
  unfold ProgOk.
  intros.
  specialize (H0 initial_state hm). forward H0.
  unfold SameValues in *.
  apply forall_In_Forall_elements. intros.
  eapply Forall_elements_forall_In in H1; eauto.
  intuition.
Qed.

Lemma CompileBindDiscard : forall T' env A (B : T' -> _) p f xp xf,
  EXTRACT p
  {{ A }}
    xp
  {{ fun _ => A }} // env ->
  EXTRACT f
  {{ A }}
    xf
  {{ B }} // env ->
  EXTRACT Bind p (fun (_ : T') => f)
  {{ A }}
    xp; xf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition. eauto. apply H; auto.
  specialize (H _ hm ltac:(eauto)).
  intuition. eapply H in H2.
  repeat deex.
  eapply H0; eauto.

  (* TODO: automate proof. ([crush] can probably do this) *)
  subst. eapply Exec_RunsTo in H2. eapply RunsTo_Step in H2. eapply Step_Seq in H2.
  intuition; repeat deex. discriminate.
  eapply Step_RunsTo in H3. eapply Step_RunsTo in H4.
  eapply RunsTo_Exec in H3. eapply RunsTo_Exec in H4.
  specialize (H _ hm ltac:(eauto)).
  intuition. specialize (H _ ltac:(eauto)). repeat deex.
  specialize (H0 _ hm' ltac:(eauto)). intuition.
  specialize (H0 _ ltac:(eauto)). repeat deex.
  eexists. exists hm'0. intuition eauto.

  eapply Exec_Steps in H2. repeat deex. eapply Step_Seq in H3.
  intuition; repeat deex.
  + eapply Steps_Exec in H3.
    repeat eforward H. specialize (H ltac:(eauto)). intuition.
    specialize (H6 _ ltac:(eauto)). repeat deex.
    eexists. eauto. invc H4. auto.
  + destruct st'. eapply Step_RunsTo in H3. eapply RunsTo_Exec in H3. eapply Steps_Exec in H5; eauto.
    repeat eforward H. conclude H eauto. intuition.
    eforward H. conclude H eauto. repeat deex.
    repeat eforward H0. conclude H0 eauto. intuition.
    eforward H10. conclude H10 eauto. repeat deex.
    eauto.
Qed.

Example micro_inc : sigT (fun p => forall x,
  EXTRACT Ret (1 + x)
  {{ "x" ~> x; ∅ }}
    p
  {{ fun ret => "x" ~> ret; ∅ }} // ∅).
Proof.
  eexists.
  intros.
  instantiate (1 := ("x" <~ Const 1 + Var "x")%facade).
  intro. intros.
  intuition. admit.
  simpl. auto.
  repeat inv_exec.
  maps.
  simpl in *.
  find_all_cases.
  find_inversion. repeat eexists; eauto. maps; eauto.

  repeat inv_exec.
Admitted.

Lemma CompileIf : forall P Q {H1 : FacadeWrapper Value ({P}+{Q})}
                         T {H : FacadeWrapper Value T}
                         A B env (pt pf : prog T) (cond : {P} + {Q}) xpt xpf xcond retvar condvar,
  retvar <> condvar ->
  EXTRACT pt
  {{ A }}
    xpt
  {{ B }} // env ->
  EXTRACT pf
  {{ A }}
    xpf
  {{ B }} // env ->
  EXTRACT Ret cond
  {{ A }}
    xcond
  {{ fun ret => condvar ~> ret; A }} // env ->
  EXTRACT if cond then pt else pf
  {{ A }}
   xcond ; If Var condvar Then xpt Else xpf EndIf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition. apply H4. exact hm. auto.
Admitted.

Lemma CompileWeq : forall A (a b : valu) env xa xb retvar avar bvar,
  avar <> bvar ->
  avar <> retvar ->
  bvar <> retvar ->
  EXTRACT Ret a
  {{ A }}
    xa
  {{ fun ret => avar ~> ret; A }} // env ->
  (forall (av : valu),
  EXTRACT Ret b
  {{ avar ~> av; A }}
    xb
  {{ fun ret => bvar ~> ret; avar ~> av; A }} // env) ->
  EXTRACT Ret (weq a b)
  {{ A }}
    xa ; xb ; retvar <~ (Var avar = Var bvar)
  {{ fun ret => retvar ~> ret; A }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition. apply H2. exact hm. auto.
  econstructor. intuition. eapply H3. exact hm.
Admitted.

Lemma CompileRead : forall F avar vvar a,
  EXTRACT Read a
  {{ avar ~> a; F }}
    Call vvar "read" [avar]
  {{ fun ret => vvar ~> ret; avar ~> a; F }} // disk_env.
Proof.
  unfold ProgOk.
  intros.
  intuition.
  maps.
  find_all_cases.
  econstructor.
  unfold disk_env. maps. trivial.
  unfold sel. simpl. rewrite He. trivial.
  simpl. eauto.

  repeat inv_exec. simpl in *. maps.
  find_all_cases. unfold disk_env in *. maps. invc H8. simpl in *.
  repeat deex. destruct output; try discriminate. simpl in *.
  unfold sel in *. rewrite He in*. repeat find_inversion.
  repeat eexists. econstructor. eapply possible_sync_refl. eauto.
  subst_definitions. maps. trivial.
  (* TODO: automate the hell out of this! *)
  destruct (StringMapFacts.eq_dec vvar avar). {
    unfold StringKey.eq in e; subst.
    eapply Forall_elements_equal; [ | eapply add_remove_same ].
    eapply forall_In_Forall_elements. intros.
    eapply Forall_elements_forall_In in H1; eauto. destruct v0.
    destruct (StringMapFacts.eq_dec k avar).
    + unfold StringKey.eq in e; subst. maps.
    + maps.
  } {
    unfold StringKey.eq in n. eapply Forall_elements_equal; [ | eapply add_remove_comm'; congruence ]. maps.
    + rewrite He. trivial.
    + eapply Forall_elements_equal; [ | eapply remove_remove_comm; congruence ].
      eapply forall_In_Forall_elements. intros.
      destruct (StringMapFacts.eq_dec k avar). {
        unfold StringKey.eq in e; subst. maps.
      }
      destruct (StringMapFacts.eq_dec k vvar). {
        unfold StringKey.eq in e; subst. maps.
      }
      maps.
      eapply Forall_elements_forall_In in H1; eauto.
      maps.
  }

  repeat inv_exec.
  eauto.
Qed.

Lemma CompileWrite : forall F tvar avar vvar a v,
  avar <> vvar ->
  tvar <> avar ->
  tvar <> vvar ->
  StringMap.find tvar F = None ->
  EXTRACT Write a v
  {{ avar ~> a; vvar ~> v; F }}
    Call tvar "write" [avar; vvar]
  {{ fun _ => avar ~> a; vvar ~> v; F }} // disk_env.
Proof.
  unfold ProgOk.
  intros.
  intuition.
  maps.
  find_all_cases.
  econstructor.
  unfold disk_env. maps. trivial.
  unfold sel. simpl. rewrite He, He0. trivial.
  simpl. eauto.

  repeat inv_exec. simpl in *. maps.
  find_all_cases. unfold disk_env in *. maps. invc H12. simpl in *.
  repeat deex. do 2 (destruct output; try discriminate). simpl in *.
  unfold sel in *. rewrite He, He0 in *. repeat find_inversion.
  repeat eexists. econstructor. eapply possible_sync_refl. eauto.
  subst_definitions. maps. rewrite He0. trivial.
  eapply forall_In_Forall_elements. intros.
  pose proof (Forall_elements_forall_In _ H6).
  simpl in *.
  destruct (StringMapFacts.eq_dec k tvar); maps.
  destruct (StringMapFacts.eq_dec k vvar); maps. {
    find_inversion. trivial.
  }
  destruct (StringMapFacts.eq_dec k avar); maps.
  specialize (H7 k v). conclude H7 ltac:(maps; eauto).
  simpl in *. eauto.

  repeat inv_exec.
  eauto.
Qed.

Ltac reduce_or_fallback term continuation fallback :=
  match nat with
  | _ => let term' := (eval red in term) in let res := continuation term' in constr:(res)
  | _ => constr:(fallback)
  end.
Ltac find_fast value fmap :=
  match fmap with
  | @StringMap.empty _       => constr:(@None string)
  | StringMap.add ?k (SItem ?v) _    => let eq := constr:(eq_refl v : v = value) in
                     constr:(Some k)
  | StringMap.add ?k _ ?tail => let ret := find_fast value tail in constr:(ret)
  | ?other         => let ret := reduce_or_fallback fmap ltac:(fun reduced => find_fast value reduced) (@None string) in
                     constr:(ret)
  end.

Ltac match_variable_names_right :=
  match goal with
  | [ H : StringMap.find _ ?m = _ |- _ ] =>
    repeat match goal with
    | [ |- context[StringMap.add ?k (SItem ?v) _]] =>
      is_evar k;
      match find_fast v m with
      | Some ?k' => unify k k'
      end
    end
  end.

Ltac match_variable_names_left :=
  try (match goal with
  | [ H : context[StringMap.add ?k (SItem ?v) _] |- _ ] =>
    is_evar k;
    match goal with
    | [ |- StringMap.find _ ?m = _ ] =>
      match find_fast v m with
      | Some ?k' => unify k k'
      end
    end
  end; match_variable_names_left).

Ltac keys_equal_cases :=
  match goal with
  | [ H : StringMap.find ?k0 _ = _ |- _ ] =>
    match goal with
    | [ H : context[StringMap.add ?k (SItem ?v) _] |- _ ] => destruct (StringMapFacts.eq_dec k0 k); maps
    end
  end.

Ltac prepare_for_frame :=
  match goal with
  | [ H : ~ StringKey.eq _ ?k |- _ ] =>
    rewrite add_add_comm with (k1 := k) by congruence; maps (* A bit inefficient: don't need to rerun maps if it's still the same [k] *)
  end.

Ltac match_scopes :=
  simpl; intros;
  match_variable_names_left; match_variable_names_right;
  try eassumption; (* TODO this is not going to cover everything *)
  repeat keys_equal_cases;
  repeat prepare_for_frame;
  try eassumption.

Ltac compile :=
  repeat match goal with
  | [ |- @sigT _ _ ] => eexists
  | _ => eapply CompileBindDiscard
  | _ => let r := gensym "r" in eapply CompileBind with (var := r); intros
  | _ => eapply CompileConst
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; try match_scopes; maps
  | [ |- EXTRACT Read ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
    | Some ?k =>
      eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
        eapply CompileRead with (avar := k) ]]; try match_scopes; maps
    | None =>
      eapply extract_equiv_prog; [ eapply bind_left_id | ]
    end
  | [ |- EXTRACT Write ?a ?v {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
    | Some ?ka =>
      match find_fast v pre with
      | Some ?kv =>
        let tmp := gensym "_" in
        eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
          eapply CompileWrite with (avar := ka) (vvar := kv) (tvar := tmp) ]]; try match_scopes; maps
      | None =>
        eapply extract_equiv_prog; [ eapply bind_left_id | ]
      end
    | None =>
      eapply extract_equiv_prog; [
        let arg := fresh "arg" in
        set (arg := Write a v);
        pattern a in arg; subst arg;
        eapply bind_left_id | ]
    end
  end.

Definition swap_prog :=
  a <- Read 0;
  b <- Read 1;
  Write 0 b;;
  Write 1 a;;
  Ret tt.

Example micro_swap : sigT (fun p =>
  EXTRACT swap_prog {{ ∅ }} p {{ fun _ => ∅ }} // disk_env).
Proof.
  compile.
Defined.

Eval lazy in projT1 micro_swap.

Definition swap2_prog :=
  a <- Read 0;
  b <- Read 1;
  if weq a b then
    Ret tt
  else
    Write 0 b;;
    Write 1 a;;
    Ret tt.

Example micro_swap2 : sigT (fun p =>
  EXTRACT swap2_prog {{ ∅ }} p {{ fun _ => ∅ }} // disk_env).
Proof.
  compile.

  eapply hoare_weaken_post; [ | eapply CompileIf with (condvar := "c0") (retvar := "r") ];
    try match_scopes; maps.

  apply FacadeWrapper_unit.
  compile. apply H.

  compile.
  eapply CompileWeq.

  shelve.
  shelve.
  shelve.

  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  intros.
  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  Unshelve.
  all: congruence.
Defined.

Eval lazy in projT1 micro_swap2.
