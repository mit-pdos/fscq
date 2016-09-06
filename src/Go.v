Require Import PeanoNat String List FMapAVL.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import VerdiTactics.
Require Import StringMap.
Require Import Mem AsyncDisk.
Require Import Word.

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


(*
Semantics for Go
================

* No pointer aliasing. Use pointers for types which can be mutated. (Or for everything?)
* Ony declare variables at beginning of block
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
  | Block : scope -> stmt -> stmt
  | Seq : stmt -> stmt -> stmt
  | If : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt
  | Call : list var -> label -> list var -> stmt
  | Assign : var -> expr -> stmt
  | DiskRead : var -> expr -> stmt
  | DiskWrite : expr -> expr -> stmt
  (* Only appears at runtime *)
  | InCall (s0: locals) (argvars: list var) (retvars: list var) (args: list var) (rets: list var) (p: stmt).

  (* Program does not contain an InCall. Could probably be expressed directly if we had generics. *)
  Inductive source_stmt : stmt -> Prop :=
  | SSkip : source_stmt Skip
  | SBlock :
      forall sc a,
        source_stmt a ->
        source_stmt (Block sc a)
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
  | SDiskRead : forall x a, source_stmt (DiskRead x a)
  | SDiskWrite : forall a v, source_stmt (DiskWrite a v).

  Fixpoint is_source_stmt (p : stmt) : bool :=
    match p with
      | Block _ a => is_source_stmt a 
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
    RetVar : option var;
    Body : stmt;
    ret_not_in_args : is_none_or_not_in RetVar ArgVars = true;
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

  
End Go.