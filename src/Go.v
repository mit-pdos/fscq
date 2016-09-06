Require Import PeanoNat String List FMapAVL.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import StringMap.
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


(*
Semantics for Go
================

* No pointer aliasing. Use pointers for types which can be mutated. (Or for everything?)
* Disallow shadowing (good idea?)
*)

Notation W := nat. (* Assume bignums? *)

Module Go.

  Definition label := string.
  Definition var := string.

  Inductive binop := Plus | Minus | Times.
  Inductive test := Eq | Ne | Lt | Le.

  Inductive expr :=
  | Var : var -> expr
  | Const : W -> expr
  | Binop : binop -> expr -> expr -> expr
  | TestE : test -> expr -> expr -> expr.

  Notation "A < B" := (TestE Lt A B) : go_scope.
  Notation "A <= B" := (TestE Le A B) : go_scope.
  Notation "A <> B" := (TestE Ne A B) : go_scope.
  Notation "A = B" := (TestE Eq A B) : go_scope.
  Delimit Scope go_scope with facade.

  Notation "! x" := (x = 0)%facade (at level 70, no associativity).
  Notation "A * B" := (Binop Times A B) : go_scope.
  Notation "A + B" := (Binop Plus A B) : go_scope.
  Notation "A - B" := (Binop Minus A B) : go_scope.

  Inductive type :=
  | Num
  | EmptyStruct
  | DiskBlock.

  Definition type_denote (t : type) : Type :=
    match t with
      | Num => W
      | EmptyStruct => unit
      | DiskBlock => valu
    end.

  Definition can_alias t :=
    match t with
      | Num => true
      | EmptyStruct => true
      | DiskBlock => false
    end.

  Inductive value :=
  | Val t (v : type_denote t).

  Definition type_of (v : value) :=
    match v with Val t _ => t end.

  Definition default_value (t : type) :=
    match t with
      | Num => Val Num 0
      | EmptyStruct => Val EmptyStruct tt
      | DiskBlock => Val DiskBlock $0
    end.

  Definition scope := StringMap.t type.
  Definition locals := StringMap.t value.

  Inductive stmt :=
  | Skip : stmt
  | Seq : stmt -> stmt -> stmt
  | If : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt
  | Call : list var -> label -> list var -> stmt
  | Assign : var -> expr -> stmt
  | Declare : var -> type -> stmt
  | DiskRead : var -> expr -> stmt
  | DiskWrite : expr -> expr -> stmt
  (* Only appears at runtime *)
  | InCall (s0: locals) (argvars: list var) (retvars: list var) (args: list var) (rets: list var) (p: stmt).

  (* Program does not contain an InCall. Could probably be expressed directly if we had generics. *)
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
  | SCall : forall x f args, source_stmt (Call x f args)
  | SAssign : forall x e, source_stmt (Assign x e)
  | SDeclare : forall x e, source_stmt (Declare x e)
  | SDiskRead : forall x a, source_stmt (DiskRead x a)
  | SDiskWrite : forall a v, source_stmt (DiskWrite a v).

  Fixpoint is_source_stmt (p : stmt) : bool :=
    match p with
      | Seq a b => is_source_stmt a && is_source_stmt b
      | If cond t f => is_source_stmt t && is_source_stmt f
      | While cond body => is_source_stmt body
      | InCall _ _ _ _ _ _ => false
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

  Definition eval_binop_m (op : binop + test) (oa ob : option value) : option value :=
    match oa, ob with
      | Some (Val Num a), Some (Val Num b) => Some (Val Num (eval_binop op a b))
      | _, _ => None
    end.

  Fixpoint eval (st : locals) (e : expr) : option value :=
    match e with
      | Var x => StringMap.find x st
      | Const w => Some (Val Num w)
      | Binop op a b => eval_binop_m (inl op) (eval st a) (eval st b)
      | TestE op a b => eval_binop_m (inr op) (eval st a) (eval st b)
    end.

  Hint Unfold eval.

  Definition eval_bool st e : option bool :=
    match eval st e with
      | Some (Val Num w) => Some (if Nat.eq_dec w 0 then false else true)
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
              | false, Some v => StringMap.add k v st
              | false, None => StringMap.remove k st
              | _, _ => st
            end in
        add_remove_many keys' input' output' st'
      | _, _, _ => st
    end.

  Fixpoint add_many keys (output : list value) st :=
    match keys, output with
      | k :: keys', v :: output' =>
        let st' := StringMap.add k v st in
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

  Definition is_none_or_not_in (v : option string) vs :=
    match v with
      | None => true
      | Some rv => negb (is_in rv vs)
    end.

  Record OperationalSpec := {
    ArgVars : list var;
    RetVars : list var;
    Body : stmt;
    (* ret_not_in_args : dont_intersect RetVars ArgVars = true; *)
    args_no_dup : is_no_dup ArgVars = true;
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

    Definition sel T m := fun k => StringMap.find k m : option T.

    Fixpoint make_map {elt} keys values :=
      match keys, values with
        | k :: keys', v :: values' => StringMap.add k v (make_map keys' values')
        | _, _ => @StringMap.empty elt
      end.

    Eval hnf in rawdisk.

    Definition maybe_add V k (v : V) m :=
      match k with
        | None => m
        | Some kk => StringMap.add kk v m
      end.


    Inductive RunsTo : stmt -> state -> state -> Prop :=
    | RunsToSkip : forall st,
                     RunsTo Skip st st
    | RunsToSeq : forall a b st st' st'',
                    RunsTo a st st' ->
                    RunsTo b st' st'' ->
                    RunsTo (Seq a b) st st'
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
                       can_alias (type_of v) = true ->
                       s' = StringMap.add x v s ->
                       RunsTo (Assign x e) (d, s) (d, s')
    | RunsToDiskRead : forall x ae a d s s' v vs,
                         eval s ae = Some (Val Num a) ->
                         d a = Some (v, vs) ->
                         s' = StringMap.add x (Val DiskBlock v) s ->
                         RunsTo (DiskRead x ae) (d, s) (d, s')
    | RunsToDiskWrite : forall ae a ve v (d : rawdisk) d' s v0 v0s,
                          eval s ae = Some (Val Num a) ->
                          eval s ve = Some (Val DiskBlock v) ->
                          d a = Some (v0, v0s) ->
                          d' = upd d a (v, v0 :: v0s) ->
                          RunsTo (DiskWrite ae ve) (d, s) (d', s)
    | RunsToCallOp : forall retvars f args s spec d d' input callee_s' ret,
                       StringMap.find f env = Some spec ->
                       source_stmt (Body spec) ->
                       length args = length (ArgVars spec) ->
                       mapM (sel s) args = Some input ->
                       let callee_s := make_map (ArgVars spec) input in
                       RunsTo (Body spec) (d, callee_s) (d', callee_s') ->
                       all_some (List.map (fun rv => sel callee_s' rv) (RetVars spec)) = Some ret ->
                       let output := List.map (sel callee_s') (ArgVars spec) in
                       let s' := add_remove_many args input output s in
                       let s' := add_many retvars ret s' in
                       RunsTo (Call retvars f args) (d, s) (d', s').

    Inductive Step : state * stmt -> state * stmt -> Prop :=
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
          match retvar with
            | None => ret = None
            | Some rv => sel callee_s' rv = Some retval
          end ->
          let output := List.map (sel callee_s') argvars in
          let s' := add_remove_many args input output s in
          let s' := maybe_add ret retval s' in
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

    Hint Unfold is_final.

    Inductive Exec : State * Stmt -> Outcome -> Prop :=
    | EXStep : forall sst sst' out,
                 Step sst sst' ->
                 Exec sst' out ->
                 Exec sst out
    | EXFail : forall sst,
                 (~exists st' p', Step sst (st', p')) ->
                 ~is_final sst ->
                 Exec sst EFailed
    | EXCrash : forall d s p,
                  CrashStep p ->
                  Exec (d, s, p) (ECrashed d)
    | EXDone : forall st,
                 Exec (st, Skip) (EFinished st).

    Hint Constructors Exec RunsTo Step.

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
        | [ H : Step _ _ |- _ ] => invc H; eauto
        | [ H : clos_refl_trans_1n _ _ _ _ |- _ ] => invc H; eauto
      end.

    Lemma steps_incall :
      forall s0 argvars retvar args ret st p st' p',
        Step^* (st, p) (st', p') ->
        Step^* (st, InCall s0 argvars retvar args ret p) (st', InCall s0 argvars retvar args ret p').
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. eauto.
    Qed.
    Hint Resolve steps_incall.

    Lemma steps_sequence :
      forall p0 st p st' p',
        Step^* (st, p) (st', p') ->
        Step^* (st, Seq p p0) (st', Seq p' p0).
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. eauto.
    Qed.
    Hint Resolve steps_sequence.

    (* For some reason (probably involving tuples), the [Hint Constructors] isn't enough. *)
    Hint Extern 1 (Step (_, Assign _ _) _) =>
    eapply StepAssign.
    Hint Extern 1 (Step (_, DiskRead _ _) _) =>
    eapply StepDiskRead.
    Hint Extern 1 (Step (_, DiskWrite _ _) _) =>
    eapply StepDiskWrite.
    Hint Extern 1 (Step (_, Call _ _ _) _) =>
    eapply StepStartCall.
    Hint Extern 1 (Step (_, InCall _ _ _ _ _ _) _) =>
    eapply StepEndCall.

    Theorem RunsTo_Steps :
      forall p st st',
        RunsTo p st st' ->
        Step^* (st, p) (st', Skip).
    Proof.
      intros.
      induction H; subst_definitions; subst; eauto 10.
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
                         match RetVar spec with
                           | None => x = None
                           | Some rv => sel callee_s' rv = Some ret
                         end ->
                         let output := List.map (sel callee_s') (ArgVars spec) in
                         let s' := add_remove_many args input output s in
                         let s' := maybe_add x ret s' in
                         RunsTo_InCall (Call x f args) (d, s) (d', s')
    | RunsToInCall : forall s0 x args (argvars : list var) retvar input ret p d d' callee_s callee_s',
                       mapM (sel s0) args = Some input ->
                       length args = length argvars ->
                       match retvar with
                         | None => x = None
                         | Some rv => sel callee_s' rv = Some ret
                       end ->
                       let output := List.map (sel callee_s') argvars in
                       let s' := add_remove_many args input output s0 in
                       let s' := maybe_add x ret s' in
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
      induction 2; intros; subst_definitions; invc H; eauto.
    Qed.

    Hint Resolve SourceStmt_RunsToInCall_RunsTo.

    Hint Constructors RunsTo_InCall.

    Lemma RunsTo_RunsToInCall :
      forall p st st',
        RunsTo p st st' ->
        RunsTo_InCall p st st'.
    Proof.
      induction 1; intros; subst_definitions; eauto.
    Qed.

    Hint Resolve RunsTo_RunsToInCall.

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
      - subst_definitions. eauto.
      - eapply RunsToICCallOp; eauto. assert (Some input = Some input0) by congruence. find_inversion. auto.
      - destruct st. eapply RunsToInCall; eauto.
    Qed.

    Hint Resolve Step_RunsTo.

    Theorem Steps_RunsTo' :
      forall p st st',
        Step^* (st, p) (st', Skip) ->
        RunsTo_InCall p st st'.
    Proof.
      intros.
      prep_induction H; induction H; intros; subst.
      - find_inversion. eauto.
      - destruct y. eauto.
    Qed.

    Theorem Steps_RunsTo :
      forall p st st',
        SourceStmt p ->
        Step^* (st, p) (st', Skip) ->
        RunsTo p st st'.
    Proof.
      intros.
      eauto using Steps_RunsTo'.
    Qed.

    Theorem ExecFinished_Steps : forall p st st',
                                   Exec (st, p) (EFinished st') ->
                                   Step^* (st, p) (st', Skip).
    Proof.
      intros.
      prep_induction H; induction H; intros; subst; try discriminate.
      + destruct sst'. eauto.
      + repeat find_inversion. eauto.
    Qed.

    Theorem Steps_ExecFinished : forall p st st',
                                   Step^* (st, p) (st', Skip) ->
                                   Exec (st, p) (EFinished st').
    Proof.
      intros.
      prep_induction H; induction H; intros; subst; try discriminate.
      + find_inversion. eauto.
      + destruct y. eauto.
    Qed.

    Theorem ExecCrashed_Steps : forall p st d',
                                  Exec (st, p) (ECrashed d') ->
                                  exists s' p', Step^* (st, p) (d', s', p') /\ CrashStep p'.
    Proof.
      intros.
      prep_induction H; induction H; intros; subst; try discriminate.
      + destruct sst'. specialize (IHExec _ _ _ eq_refl eq_refl). repeat deex. eauto 8.
      + find_inversion. find_inversion. eauto 8.
    Qed.

    Theorem Steps_ExecCrashed : forall st p d' s' p',
                                  Step^* (st, p) (d', s', p') ->
                                  CrashStep p' ->
                                  Exec (st, p) (ECrashed d').
    Proof.
      intros.
      destruct st.
      prep_induction H; induction H; intros; subst.
      + repeat find_inversion. eauto.
      + destruct y. destruct s. eauto.
    Qed.

    Theorem ExecFailed_Steps :
      forall st p,
        Exec (st, p) EFailed ->
        exists st' p', Step^* (st, p) (st', p') /\ ~is_final (st', p') /\ ~exists st'' p'', Step (st', p') (st'', p'').
    Proof.
      intros.
      unfold is_final; simpl.
      prep_induction H; induction H; intros; subst; try discriminate; eauto.
      - destruct sst'. repeat eforward IHExec. repeat conclude IHExec eauto. repeat deex.
        eauto 10.
    Qed.

    Theorem Steps_ExecFailed :
      forall st p st' p',
        ~is_final (st', p') ->
        (~exists st'' p'', Step (st', p') (st'', p'')) ->
        Step^* (st, p) (st', p') ->
        Exec (st, p) EFailed.
    Proof.
      induction 3; eauto.
    Qed.

    Lemma Steps_Seq :
      forall p1 p2 p' st st'',
        Step^* (st, Seq p1 p2) (st'', p') ->
        (exists p1', Step^* (st, p1) (st'', p1') /\ p' = Seq p1' p2) \/
        (exists st', Step^* (st, p1) (st', Skip) /\ Step^* (st', p2) (st'', p')).
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