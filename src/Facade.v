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

Definition W := nat. (* Assume bignums? *)

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

Inductive Stmt :=
| Skip : Stmt
| Seq : Stmt -> Stmt -> Stmt
| If : Expr -> Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt
| Call : var -> label -> list var -> Stmt
| Assign : var -> Expr -> Stmt.

Arguments Assign v val.

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

Section Extracted.

  Definition Locals := StringMap.t Value.


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

  (* TODO: throw out RunsTo? *)
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
  | RunsToCallOp : forall x f args s spec d d' input callee_s' ret,
      StringMap.find f env = Some spec ->
      length args = length (ArgVars spec) ->
      mapM (sel s) args = Some input ->
      let callee_s := make_map (ArgVars spec) input in
      RunsTo (Body spec) (d, callee_s) (d', callee_s') ->
      sel callee_s' (RetVar spec) = Some ret ->
      let output := List.map (sel callee_s') (ArgVars spec) in
      let s' := add_remove_many args input output s in
      let s' := add x ret s' in
      RunsTo (Call x f args) (d, s) (d', s').


  (* Control-stack small-step semantics *)

  Inductive Step0 : State * Stmt -> State * Stmt -> Prop :=
  | StepIfTrue : forall cond t f st,
      is_true (snd st) cond ->
      Step0 (st, If cond t f) (st, t)
  | StepIfFalse : forall cond t f st,
      is_false (snd st) cond ->
      Step0 (st, If cond t f) (st, f)
  | StepWhileTrue : forall cond body st,
      let loop := While cond body in
      is_true (snd st) cond ->
      Step0 (st, loop) (st, Seq body loop)
  | StepWhileFalse : forall cond body st,
      let loop := While cond body in
      is_false (snd st) cond ->
      Step0 (st, loop) (st, Skip)
  | StepAssign : forall x e d s s' v,
      (* rhs can't be a mutable object, to prevent aliasing *)
      eval s e = Some v ->
      can_alias v = true ->
      s' = add x v s ->
      Step0 (d, s, Assign x e) (d, s', Skip).

  Definition StepState := (State * list frame * Stmt)%type.

  Inductive Step : StepState * Stmt -> StepState * Stmt -> Prop :=
  | StepStep0 : forall a a' st st' fs k,
      Step0 (st, a) (st', a') ->
      Step (st, fs, k, a) (st', fs, k, a')
  | StepSeq : forall a b st fs k,
      Step (st, fs, k, Seq a b) (st, fs, Seq b k, a)
  | StepCont : forall st fs k1 k2,
      Step (st, fs, Seq k1 k2, Skip) (st, fs, k2, k1)
  | StepCallOp : forall x f args s spec d input fs k,
      StringMap.find f env = Some spec ->
      length args = length (ArgVars spec) ->
      mapM (sel s) args = Some input ->
      let callee_s := make_map (ArgVars spec) input in
      Step ((d, s), fs, k, Call x f args)
           ((d, callee_s), {| Locs := s; Cont := k; Spec := spec; Args := args; RetV := x |} :: fs, Skip, spec.(Body))
  | StepCallRet : forall x f args s callee_s' spec d input ret fs k,
      StringMap.find f env = Some spec ->
      mapM (sel s) args = Some input ->
      length args = length (ArgVars spec) ->
      sel callee_s' (RetVar spec) = Some ret ->
      let output := List.map (sel callee_s') (ArgVars spec) in
      let s' := add_remove_many args input output s in
      let s' := add x ret s' in
      Step ((d, callee_s'), {| Locs := s; Cont := k; Spec := spec; Args := args; RetV := x |} :: fs, Skip, Skip)
           ((d, s'), fs, k, Skip).

  Inductive Outcome :=
  | EFailed
  | EFinished (st : rawdisk * Locals)
  | ECrashed (d : rawdisk).

  Inductive CrashStep : Stmt -> Prop :=
  | CrashSeq1 : forall a b,
      CrashStep a ->
      CrashStep (Seq a b)
  | CrashCall : forall x f args,
      CrashStep (Call x f args).

  Definition is_final (sst : StepState * Stmt) : Prop :=
    let '(st, fs, k, c) := sst in
    fs = [] /\ k = Skip /\ c = Skip.

  Inductive Exec : StepState * Stmt -> Outcome -> Prop :=
  | EXStep : forall st st' out,
    Step st st' ->
    Exec st' out ->
    Exec st out
  | EXFail : forall st,
    (~exists st', Step st st') ->
    ~is_final st ->
    Exec st EFailed
  | EXCrash : forall d s fs k c,
    CrashStep c ->
    Exec (d, s, fs, k, c) (ECrashed d)
  | EXDone : forall st,
    Exec (st, [], Skip, Skip) (EFinished st).

  Hint Constructors Exec RunsTo Step Step0 : steps.

  Hint Constructors clos_refl_trans_1n : steps.

  Ltac do_inv :=
    match goal with
    | [ H : Step _ _ |- _ ] => invc H; eauto with steps
    | [ H : clos_refl_trans_1n _ _ _ _ |- _ ] => invc H; eauto with steps
    end.

  Lemma Steps_add_stack : forall st st' fs1 fs c c' k k',
    Step^* (st, fs1, c, k) (st', [], c', k') ->
    Step^* (st, fs1 ++ fs, c, k) (st', fs, c', k').
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    - find_inversion. eauto with steps.
    - destruct y. destruct s. destruct p. do_inv.
      + econstructor; eauto. econstructor; eauto. (* Why doesn't [eauto] apply [StepStep0]? :( *)
      + econstructor; eauto. econstructor; eauto.
      + econstructor; eauto. eapply StepCallRet; eauto.
  Qed.

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

  (* For some reason, the [Hint Constructors] isn't enough. *)
  Hint Extern 1 (Step (_, Seq _ _) _) =>
    eapply StepSeq : steps.
  Hint Extern 1 (Step (_, If _ _ _) _) =>
    eapply StepStep0; eapply StepIfTrue : steps.
  Hint Extern 1 (Step (_, If _ _ _) _) =>
    eapply StepStep0; eapply StepIfFalse : steps.
  Hint Extern 1 (Step (_, _) _) =>
    eapply StepStep0; eapply StepWhileTrue : steps.
  Hint Extern 1 (Step (_, _) _) =>
    eapply StepStep0; eapply StepWhileFalse : steps.
  Hint Extern 1 (Step (_, Assign _ _) _) =>
    eapply StepStep0; eapply StepAssign : steps.
  Hint Extern 1 (Step (_, Call _ _ _) _) =>
    eapply StepCallOp : steps.
  Hint Extern 1 (Step (_, _ :: _, _ _) _) =>
    eapply StepCallRet : steps.

  Theorem RunsTo_Step' : forall p st st' k,
    RunsTo p st st' ->
    Step^* (st, [], k, p) (st', [], k, Skip).
  Proof.
    intros.
    generalize (@nil frame).
    intros. generalizeEverythingElse H.
    induction H; intros; eauto 8 with steps.
    + eapply rt1n_trans'.
       eapply rt1n_front.
        apply StepCallOp; eauto.
        apply IHRunsTo.
       eapply rt1n_front.
        eapply StepCallRet; eauto. 
        subst_definitions. (* It's because of this subst_definitions that [eauto] doesn't work on this case. *)
         eauto with steps.
  Qed.

  Theorem RunsTo_Step : forall p st st',
    RunsTo p st st' ->
    Step^* (st, [], Skip, p) (st', [], Skip, Skip).
  Proof.
    intros. eapply RunsTo_Step'; eauto.
  Qed.

  Inductive InCallStmt :=
  | Cur (p: Stmt)
  | InCall (v0: Locals) (spec: OperationalSpec) (args: list var) (retv: var) (c: InCallStmt) (k: Stmt).

  Inductive RunsTo_InCall : InCallStmt -> State -> State -> Prop :=
  | RunsToCur : forall p st st',
      RunsTo p st st'
      -> RunsTo_InCall (Cur p) st st'
  | RunsToInCall : forall s0 x args spec input ret p k d d' d'' s'' callee_s callee_s',
      RunsTo_InCall p (d, callee_s) (d', callee_s')
      -> mapM (sel s0) args = Some input
      -> length args = length (ArgVars spec)
      -> sel callee_s' (RetVar spec) = Some ret
      -> let output := List.map (sel callee_s') (ArgVars spec) in
         let s' := add_remove_many args input output s0 in
         let s' := add x ret s' in
         RunsTo k (d', s') (d'', s'')
      -> RunsTo_InCall (InCall s0 spec args x p k) (d, callee_s) (d'', s'').

  Fixpoint equiv_stmt (fs : list frame) (c : InCallStmt) : InCallStmt :=
    match fs with
    | [] => c
    | {| Locs := s0; Cont := k; Spec := spec; Args := args; RetV := retv |} :: fs' =>
      equiv_stmt fs' (InCall s0 spec args retv c k)
    end.

  Fixpoint equiv_stmt_rev (fs : list frame) (c : InCallStmt) : InCallStmt :=
    match fs with
    | [] => c
    | {| Locs := s0; Cont := k; Spec := spec; Args := args; RetV := retv |} :: fs' =>
      (InCall s0 spec args retv (equiv_stmt_rev fs' c) k)
    end.

  Lemma equiv_stmt_last : forall l c s0 k spec args retv,
    equiv_stmt (l ++ [{| Locs := s0; Cont := k; Spec := spec; Args := args; RetV := retv |}]) c =
      InCall s0 spec args retv (equiv_stmt l c) k.
  Proof.
    induction l; intros; eauto.
    destruct a. simpl. rewrite IHl. trivial.
  Qed.

  Lemma equiv_stmt_rev_rev : forall l c,
    equiv_stmt (rev l) c = equiv_stmt_rev l c.
  Proof.
    induction l; eauto.
    destruct a. simpl. intros. rewrite equiv_stmt_last. rewrite IHl. trivial.
  Qed.

  Ltac inv_runsto :=
    match goal with
    | [ H: RunsTo ?c _ _ |- _ ] =>
      (is_var c; fail 1)
      || invc H
    | [ H: RunsTo_InCall (Cur ?c) _ _ |- _ ] =>
      invc H
    end.

  Hint Constructors RunsTo RunsTo_InCall : steps.

  Lemma runsto_inside : forall fs s s' s'' c,
    RunsTo_InCall c s s' ->
    RunsTo_InCall (equiv_stmt fs (Cur Skip)) s' s'' ->
    RunsTo_InCall (equiv_stmt fs c) s s''.
  Proof.
    intros.
    rewrite <- rev_involutive with (l := fs) in *.
    rewrite equiv_stmt_rev_rev in *.
    remember (rev fs) as rfs.
    clear fs Heqrfs.
    rename rfs into fs.
    revert s s' s'' c H H0.
    induction fs; intros.
    - simpl in *. invc H0. inv_runsto. eauto.
    - destruct a. simpl in *. invc H0. subst_definitions. destruct s.
      find_eapply_lem_hyp IHfs; eauto with steps.
  Qed.

  Lemma runsto_inside' : forall fs s s'' c,
    RunsTo_InCall (equiv_stmt fs c) s s'' ->
    exists s',
         RunsTo_InCall c s s'
      /\ RunsTo_InCall (equiv_stmt fs (Cur Skip)) s' s''.
  Proof.
    intros.
    rewrite <- rev_involutive with (l := fs) in *.
    rewrite equiv_stmt_rev_rev in *.
    remember (rev fs) as rfs.
    clear fs Heqrfs.
    rename rfs into fs.
    revert s s'' c H.
    induction fs; intros.
    - simpl in *. eauto with steps.
    - destruct a. simpl in *. invc H. subst_definitions.
      find_eapply_lem_hyp IHfs; eauto. deex. destruct s'. eexists; split; eauto with steps.
  Qed.

  Hint Resolve runsto_inside runsto_inside' : steps.

  Theorem Step_RunsTo' : forall fs p st st' k,
    Step^* (st, fs, k, p) (st', [], Skip, Skip) ->
    RunsTo_InCall (equiv_stmt fs (Cur (Seq p k))) st st'.
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    - find_inversion. simpl. eauto with steps.
    - destruct y. destruct s. destruct p0.
      specialize (IHclos_refl_trans_1n _ _ _ _ _ eq_refl eq_refl eq_refl).
      rename IHclos_refl_trans_1n into Hr.
      do_inv.
      + invc H2; eapply runsto_inside' in Hr; deex; repeat (inv_runsto; eauto with steps).
        * eapply runsto_inside. econstructor. econstructor; eauto. eauto with steps. eauto.
      + eapply runsto_inside' in Hr; deex. eapply runsto_inside' in H2; deex. repeat inv_runsto. eauto with steps.
      + eapply runsto_inside' in Hr; deex. eapply runsto_inside' in H2; deex. repeat inv_runsto. eauto with steps.
      + simpl in *. eapply runsto_inside' in Hr; deex. eapply runsto_inside' in H2; deex. repeat inv_runsto. invc H0. subst_definitions. inv_runsto. inv_runsto. inv_runsto.
        eapply runsto_inside; eauto. econstructor; eauto. econstructor; eauto. rewrite H11 in H15. invc H15. eauto with steps.
      + subst_definitions. simpl in *. eapply runsto_inside' in Hr; deex. repeat inv_runsto. eapply runsto_inside; eauto. destruct s'. eauto with steps.
  Qed.

  Theorem Step_RunsTo : forall p st st',
    Step^* (st, [], Skip, p) (st', [], Skip, Skip) ->
    RunsTo p st st'.
  Proof.
    intros.
    apply Step_RunsTo' in H. simpl in *. repeat inv_runsto. trivial.
  Qed.

  Theorem RunsToInCall_Step : forall fs p k st st',
    RunsTo_InCall (equiv_stmt fs (Cur (Seq p k))) st st' ->
    Step^* (st, fs, k, p) (st', [], Skip, Skip).
  Proof.
  Admitted.

  Theorem ExecFinished_Steps : forall fs k p st st',
    Exec (st, fs, k, p) (EFinished st') ->
    Step^* (st, fs, k, p) (st', [], Skip, Skip).
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + destruct st'. destruct st'0. destruct s. destruct p0.
      eauto with steps.
    + invc H2. invc H1. eauto with steps.
  Qed.

  Theorem Steps_ExecFinished' : forall fs p k st st',
    Step^* (st, fs, k, p) (st', [], Skip, Skip) ->
    Exec (st, fs, k, p) (EFinished st').
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + find_inversion. eauto with steps.
    + destruct y. destruct s. destruct p0.
      eauto with steps.
  Qed.

  Theorem ExecCrashed_Steps : forall fs p k st d',
    Exec (st, fs, k, p) (ECrashed d') ->
    exists s' fs' k' p', Step^* (st, fs, k, p) ((d', s'), fs', k', p') /\ CrashStep p'.
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + destruct st'. destruct s. destruct p0. specialize (IHExec _ _ _ _ _ eq_refl eq_refl). repeat deex. eauto 8 with steps.
    + find_inversion. find_inversion. eauto 8 with steps.
  Qed.

  Theorem Steps_ExecCrashed : forall st fs k p d' s' fs' k' p',
    Step^* (st, fs, k, p) ((d', s'), fs', k', p') ->
    CrashStep p' ->
    Exec (st, fs, k, p) (ECrashed d').
  Proof.
    intros.
    destruct st.
    prep_induction H; induction H; intros; subst.
    + repeat find_inversion. eauto with steps.
    + destruct y. destruct s. destruct p0. destruct s1. eauto with steps.
  Qed.

  CoInductive Safe : Stmt -> State -> Prop :=
  | SafeSkip : forall st, Safe Skip st
  | SafeSeq :
      forall a b st,
        Safe a st /\
        (forall st',
           RunsTo a st st' -> Safe b st') ->
        Safe (Seq a b) st
  | SafeIfTrue :
      forall cond t f st,
        is_true (snd st) cond ->
        Safe t st ->
        Safe (If cond t f) st
  | SafeIfFalse :
      forall cond t f st,
        is_false (snd st) cond ->
        Safe f st ->
        Safe (If cond t f) st
  | SafeWhileTrue :
      forall cond body st,
        let loop := While cond body in
        is_true (snd st) cond ->
        Safe body st ->
        (forall st',
           RunsTo body st st' -> Safe loop st') ->
        Safe loop st
  | SafeWhileFalse :
      forall cond body st,
        let loop := While cond body in
        is_false (snd st) cond ->
        Safe loop st
  | SafeAssign :
      forall x e st v,
        eval (snd st) e = Some v ->
        can_alias v = true ->
        Safe (Assign x e) st
  | SafeCallOp :
      forall x f args d d' s spec input,
        NoDup args ->
        StringMap.find f env = Some spec ->
        length args = length (ArgVars spec) ->
        mapM (sel s) args = Some input ->
        let callee_s := make_map (ArgVars spec) input in
        Safe (Body spec) (d, callee_s) ->
        (forall callee_s',
           RunsTo (Body spec) (d, callee_s) (d', callee_s') ->
           sel callee_s' (RetVar spec) <> None) ->
        Safe (Call x f args) (d, s).

(*
  Section Safe_coind.

    Variable R : Stmt -> State -> Prop.

    Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', Exec a st (EFinished st') -> R b st'.

    Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true (snd st) cond /\ R t st) \/ (is_false (snd st) cond /\ R f st).

    Hypothesis WhileCase :
      forall cond body st,
        let loop := While cond body in
        R loop st ->
        (is_true (snd st) cond /\ R body st /\ (forall st', Exec body st (EFinished st') -> R loop st')) \/
        (is_false (snd st) cond).

    Hypothesis AssignCase :
      forall x e st,
        R (Assign x e) st ->
        exists v, eval (snd st) e = Some v /\
                  can_alias v = true.

    Hypothesis CallCase :
      forall x f args st,
        R (Call x f args) st ->
        exists input,
          mapM (sel (snd st)) args = Some input /\
          ((exists spec,
              StringMap.find f env = Some spec /\
              PreCond spec (fst st) input)).

    Hint Constructors Safe.

    Ltac openhyp :=
      repeat match goal with
               | H : _ /\ _ |- _  => destruct H
               | H : _ \/ _ |- _ => destruct H
               | H : exists x, _ |- _ => destruct H
             end.


    Theorem Safe_coind : forall c st, R c st -> Safe c st.
      cofix; intros; destruct c.
      - eauto.
      - eapply SeqCase in H; openhyp; eapply SafeSeq; eauto.
      - eapply IfCase in H; openhyp; eauto.
      - eapply WhileCase in H; openhyp; eauto.
      - eapply CallCase in H; openhyp; simpl in *; intuition eauto.
      - eapply AssignCase in H; openhyp; eauto.
    Qed.

  End Safe_coind.
*)
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

Notation "\u2205" := (StringMap.empty _) : map_scope.
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
    Safe env eprog initial_state /\
    (forall final_state,
      Exec env (initial_state, [], Skip, eprog) (EFinished final_state) ->
      exists r hm',
        exec (fst initial_state) hm sprog (Finished (fst final_state) hm' r) /\
        (snd final_state) \u2272 (final_tstate r)) /\
    (forall final_disk,
      Exec env (initial_state, [], Skip, eprog) (ECrashed final_disk) ->
      exists hm',
        exec (fst initial_state) hm sprog (Crashed T final_disk hm')).

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


Definition read : AxiomaticSpec.
  refine {|
    PreCond := fun disk args => exists (a : addr),
      args = [wrap a];
    PostCond := fun disk disk' args ret => exists (a : addr) (v : valu) (x : list valu),
      args = [(wrap a, Some (wrap a))] /\
      disk a = Some (v, x) /\
      ret = wrap (v) /\
      disk' = disk
  |}.
Defined.

Definition write : AxiomaticSpec.
  refine {|
    PreCond := fun disk args => exists (a : addr) (v : valu),
      args = [wrap a; wrap v];
    PostCond := fun disk disk' args ret => exists (a : addr) (v v0 : valu) (x : list valu),
      args = [(wrap a, Some (wrap a)); (wrap v, Some (wrap v))] /\
      disk a = Some (v0, x) /\
      disk' = upd disk a (v, v0 :: x) /\
      ret = wrap tt
  |}.
Defined.


Local Open Scope map_scope.

Definition disk_env : Env := "write" ->> write ; "read" ->> read ; \u2205.

Ltac find_cases var st := case_eq (StringMap.find var st); [
  let v := fresh "v" in
  let He := fresh "He" in
  intros v He; rewrite ?He in *
| let Hne := fresh "Hne" in
  intro Hne; rewrite Hne in *; exfalso; solve [ intuition idtac ] ].

Ltac inv_exec :=
  match goal with
  | [ H : Step _ _ _ |- _ ] => invc H
  | [ H : Exec _ _ _ _ |- _ ] => invc H
  | [ H : CrashStep _ |- _ ] => invc H
  end; try discriminate.

Example micro_noop : sigT (fun p =>
  EXTRACT Ret tt
  {{ \u2205 }}
    p
  {{ fun _ => \u2205 }} // \u2205).
Proof.
  eexists.
  intro.
  instantiate (1 := Skip).
  intros.
  repeat split; intros; subst.
  econstructor.
  repeat inv_exec. exists tt. exists hm. intuition.
  repeat inv_exec.
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
  eforward H0. conclude H0 eauto. repeat deex.
  repeat eexists. apply H; eauto. eauto.
  eforward H4. conclude H4 eauto. repeat deex.
  repeat eexists. apply H; eauto.
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

Example micro_write : sigT (fun p => forall a v,
  EXTRACT Write a v
  {{ "a" ~> a; "v" ~> v; \u2205 }}
    p
  {{ fun _ => \u2205 }} // disk_env).
Proof.
  eexists.
  intros.
  instantiate (1 := (Call "_" "write" ["a"; "v"])%facade).
  intro. intros.
  maps.
  find_all_cases.
  intuition idtac.

  econstructor.
  unfold disk_env.
  maps. trivial.
  simpl. unfold sel. rewrite He, He0. trivial.
  simpl. repeat deex. repeat eexists.

  repeat deex.
  repeat inv_exec. unfold disk_env in *. maps. invc H8. unfold sel in *. simpl in *. rewrite He, He0 in *. subst_definitions.
  repeat deex. simpl in *. do 2 (destruct output; try discriminate). find_inversion. find_inversion.

  repeat eexists; intuition. econstructor.

  apply possible_sync_refl.
  econstructor; eauto.

  subst. repeat inv_exec. eexists. econstructor. econstructor.
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

  repeat inv_exec.
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
Qed.

Lemma Step_Seq : forall env p1 p2 p' st st'',
  (Step env)^* (Seq p1 p2, st) (p', st'') ->
  (exists p1', (Step env)^* (p1, st) (p1', st'') /\ p' = Seq p1' p2) \/
  (exists st', (Step env)^* (p1, st) (Skip, st') /\ (Step env)^* (p2, st') (p', st'')).
Proof.
  intros.
  prep_induction H. induction H; intros; subst.
  + find_inversion. left. eexists. econstructor. econstructor. trivial.
  + destruct y. invc H.
    - destruct (IHclos_refl_trans_1n env a' p2 p' s0 st''); eauto. {
        deex. left. eexists. intuition. econstructor; eauto.
      } {
        deex. right. eexists. intuition. econstructor; eauto. eauto.
      }
    - right. eexists. split. econstructor. eauto.
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
  econstructor. intuition. apply H0. exact hm. auto.
  specialize (H0 _ hm ltac:(eauto)).
  intuition. eapply H0 in H3.
  repeat deex.
  eapply H1; eauto.

  (* TODO: automate proof. ([crush] can probably do this) *)
  subst. eapply Exec_RunsTo in H3. eapply RunsTo_Step in H3. eapply Step_Seq in H3.
  intuition; repeat deex. discriminate.
  eapply Step_RunsTo in H4. eapply Step_RunsTo in H5.
  eapply RunsTo_Exec in H4. eapply RunsTo_Exec in H5.
  specialize (H0 _ hm ltac:(eauto)).
  intuition. specialize (H0 _ ltac:(eauto)). repeat deex.
  specialize (H1 _ _ hm' ltac:(eauto)). intuition.
  specialize (H1 _ ltac:(eauto)). repeat deex.
  eexists. exists hm'0. intuition eauto.

  eapply Exec_Steps in H3. repeat deex. eapply Step_Seq in H4.
  intuition; repeat deex.
  + eapply Steps_Exec in H4.
    repeat eforward H0. specialize (H0 ltac:(eauto)). intuition.
    specialize (H7 _ ltac:(eauto)). repeat deex.
    eexists. eauto. invc H5. auto.
  + destruct st'. eapply Step_RunsTo in H4. eapply RunsTo_Exec in H4. eapply Steps_Exec in H6; eauto.
    repeat eforward H0. conclude H0 eauto. intuition.
    eforward H0. conclude H0 eauto. repeat deex.
    repeat eforward H1. conclude H1 eauto. intuition.
    eforward H11. conclude H11 eauto. repeat deex.
    eauto.
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
  {{ "x" ~> x; \u2205 }}
    p
  {{ fun ret => "x" ~> ret; \u2205 }} // \u2205).
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
  EXTRACT swap_prog {{ \u2205 }} p {{ fun _ => \u2205 }} // disk_env).
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
  EXTRACT swap2_prog {{ \u2205 }} p {{ fun _ => \u2205 }} // disk_env).
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
