Require Import PeanoNat String List FMapAVL Structures.OrderedTypeEx.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import StringMap MoreMapFacts.
Require Import Eqdep.
Require Import VerdiTactics.
Require Import Word.
Require Import Mem AsyncDisk PredCrash Prog.
Require Import MapUtils.
Import AddrMap.

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
Module MoreVarMapFacts := MoreMapFacts.MoreFacts_fun(Nat_as_OT)(VarMap).
Module MoreAddrMapFacts := MoreMapFacts.MoreFacts_fun(Nat_as_OT)(AddrMap.Map).

Module Go.

  Definition label := string.
  Definition var := nat.

  Inductive numop := Plus | Minus | Times.
  Inductive test := Eq | Ne | Lt | Le.

  Module Map := AddrMap.Map.

  Inductive type :=
  | Num
  | Bool
  | EmptyStruct
  | DiskBlock
  | Slice : type -> type
  | Pair : type -> type -> type
  | AddrMap : type -> type
  .

  Inductive movable T :=
  | Here (v : T)
  | Moved
  .

  Arguments Here {T} v.
  Arguments Moved {T}.

  Fixpoint can_alias t :=
    match t with
    | Num => false
    | Bool => true
    | EmptyStruct => true
    | DiskBlock => false
    | Slice _ => false
    | Pair t1 t2 => can_alias t1 && can_alias t2
    | AddrMap _ => false
    end.

  Fixpoint type_denote (t : type) : Type :=
    match t with
    | Num => movable W
    | Bool => bool
    | EmptyStruct => unit
    | DiskBlock => movable valu
    | Slice t' => movable (list (type_denote t')) (* kept in reverse order to make cons = append *)
    | Pair t1 t2 => type_denote t1 * type_denote t2
    | AddrMap vt => movable (Map.t (type_denote vt))
    end.

  Definition type_eq_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
    decide equality.
  Defined.

  Inductive expr :=
  | Var : var -> expr
  | Const : forall t, type_denote t -> expr
  | TestE : test -> expr -> expr -> expr.

  Inductive modify_op :=
  | SetConst {t} (v : type_denote t)
  | DuplicateOp
  | AppendOp
  | Uncons
  | ModifyNumOp (nop : numop)
  | SplitPair
  | JoinPair
  | MapAdd
  | MapRemove
  | MapFind
  | MapCardinality
  | MapElements
  .

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

  Eval cbn in (type_denote Num).
  
  Fixpoint default_value' (t : type) : type_denote t :=
    match t return type_denote t with
    | Num => Here 0
    | Bool => false
    | EmptyStruct => tt
    | DiskBlock => Here $0
    | Slice _ => Here nil
    | Pair t1 t2 => (default_value' t1, default_value' t2)
    | AddrMap vt => Here (Map.empty (type_denote vt))
    end.

  Definition default_value (t : type) : value :=
    Val t (default_value' t).

  Fixpoint moved_value' (t : type) (old : type_denote t) : type_denote t :=
    match t return type_denote t -> type_denote t with
    | Num => fun _ => Moved
    | Bool => fun old => old
    | EmptyStruct => fun old => old
    | DiskBlock => fun _ => Moved
    | Slice _ => fun _ => Moved
    | Pair t1 t2 =>
      fun old =>
        let '(v1, v2) := old
        in (moved_value' t1 v1, moved_value' t2 v2)
    | AddrMap vt => fun _ => Moved
    end old.

  Definition moved_value (old : value) : value :=
    let '(Val t o) := old in
    Val t (moved_value' t o).

  Lemma moved_value'_idem : forall (T : type) (t : type_denote T),
    moved_value' _ (moved_value' _ t) = moved_value' _ t.
  Proof.
    intros.
    induction T; simpl in *; try congruence.
    destruct t; congruence.
  Qed.

  Definition scope := VarMap.t type.
  Definition locals := VarMap.t value.

  Definition state := (rawdisk * locals)%type.

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

  Section Helpers.

    Fixpoint mapM A B (f : A -> option B) ls :=
      match ls with
      | x :: xs =>
        match f x, mapM f xs with
        | Some y, Some ys => Some (y :: ys)
        | _, _ => None
        end
      | nil => Some nil
      end.
    
    Definition split_pair_func A B C D (f : A -> B) (g: C -> D) : A * C -> B * D :=
      fun p => let (a, c) := p in (f a, g c).

  End Helpers.

  Section NTuple.

    Fixpoint n_tuple n T : Type :=
      match n with
      | 0 => unit
      | 1 => T
      | S n' => n_tuple n' T * T
      end.
    
    Definition tupled_rev T (l : list T) : n_tuple (length l) T.
      induction l.
      - exact tt.
      - simpl in *.
        destruct l.
        + exact a.
        + simpl in *.
          exact (IHl, a).
    Defined.

    Definition map_nt {A B n} (f : A -> B) : n_tuple n A -> n_tuple n B.
      induction n.
      - exact (fun _ => tt).
      - simpl in *; destruct n.
        + exact f.
        + apply split_pair_func; assumption.
    Defined.

    Definition collect {T n} : n_tuple n (option T) -> option (n_tuple n T).
      induction n.
      - exact (fun _ => Some tt).
      - simpl in *; destruct n.
        + exact id.
        + intros [ts tl].
          destruct tl; [ | exact None ].
          destruct (IHn ts); [ | exact None ].
          exact (Some (n0, t)).
    Defined.

    Definition combine_nt {A B n} : n_tuple n A -> n_tuple n B -> n_tuple n (A * B).
      induction n; intros ta tb.
      - exact tt.
      - simpl in *; destruct n.
        + exact (ta, tb).
        + exact (IHn (fst ta) (fst tb), (snd ta, snd tb)).
    Defined.

    Definition seq_nt (start len : nat) : n_tuple len nat.
      induction len.
      - exact tt.
      - simpl in *; destruct len.
        + exact start.
        + exact (IHlen, S (start + len)).
    Defined.

  End NTuple.

  Section NiceImpls.

    Inductive var_update :=
    | SetTo (newval : value)
    | Move
    | Leave (*unchanged*).

    Definition op_impl n := n_tuple n value -> option (n_tuple n var_update).

    Definition numop_impl' (op : numop) (a b : nat) : n_tuple 3 var_update :=
      (SetTo (Val Num (Here (match op with
                             | Plus => a + b
                             | Minus => a - b
                             | Times => a * b
                             end))),
       Leave, Leave).

    Definition setconst_impl t (v : type_denote t) : op_impl 1 :=
      fun _ => Some (SetTo (Val t v)).

    Definition duplicate_impl : op_impl 2 :=
      fun args => let (_, a) := args in Some (SetTo a, Leave).

    Definition append_impl' t (l : list (type_denote t)) (a : type_denote t) : n_tuple 2 var_update :=
      (SetTo (Val (Slice t) (Here (a :: l))), Move).

    Definition uncons_impl' t (l : list (type_denote t)) : n_tuple 4 var_update :=
      (Move,
       SetTo (Val Bool (match l with [] => false | _ => true end)),
       SetTo (Val t (match l with [] => default_value' _ | x :: _ => x end)),
       SetTo (Val (Slice t) (match l with [] => default_value' _ | _ :: xs => Here xs end))).

    Definition split_pair_impl' ta tb (a : type_denote ta) (b : type_denote tb) : n_tuple 3 var_update :=
      (Move, SetTo (Val ta a), SetTo (Val tb b)).

    Definition join_pair_impl' ta tb (va : type_denote ta) (vb : type_denote tb) : n_tuple 3 var_update :=
      (SetTo (Val (Pair ta tb) (va, vb)), Move, Move).

    Definition map_add_impl' tv m (k : addr) (v : type_denote tv) : n_tuple 3 var_update :=
      (SetTo (Val (AddrMap tv) (Here (Map.add k v m))), Leave, Move).

    Definition map_card_impl' tv (m : Map.t (type_denote tv)) : n_tuple 2 var_update :=
      (Leave, SetTo (Val Num (Here (Map.cardinal m)))).

    Definition map_find_impl' tv m (k : addr) : n_tuple 3 var_update :=
      (Leave, Leave, SetTo (Val (Pair Bool tv) (match Map.find k m with
                                                 | Some x => (true, x)
                                                 | None => (false, default_value' tv)
                                                 end))).

    Definition map_remove_impl' tv m k : n_tuple 2 var_update :=
      (SetTo (Val (AddrMap tv) (Here (Map.remove k m))), Leave).

    Definition map_elements_impl' tv (m : Map.t (type_denote tv)) : n_tuple 2 var_update :=
      (Leave, SetTo (Val (Slice (Pair Num tv))
        (Here (map (fun x => (Here (fst x), snd x)) (Map.elements m))))).
  End NiceImpls.

  Section NastyImpls.

    Definition numop_impl (op : numop) : op_impl 3 :=
      fun args => let '(vo, va, vb) := args in
               match vo, va, vb with
               | Val Num _, Val Num (Here a), Val Num (Here b) =>
                 Some (numop_impl' op a b)
               | _, _, _ => None
               end.

    Definition append_impl : op_impl 2.
      refine (fun args => let '(Val t1 l, Val t2 a) := args in
                       match t1 with
                       | Slice t1' => fun l => _
                       | _ => fun _ => None
                       end l).
      destruct (type_eq_dec t1' t2); [ | exact None ].
      rewrite e in l.
      destruct l as [ l | ]; [ | exact None ].
      refine (Some (append_impl' _ l a)).
    Defined.

    Definition uncons_impl : op_impl 4.
      refine (fun args => let '(Val t1 l, _, _, _) := args in
                       match t1 with
                       | Slice t1' => fun l => _
                       | _ => fun _ => None
                       end l).
      destruct l as [ l | ]; [ | exact None ].
      refine (Some (uncons_impl' _ l)).
    Defined.

    Definition split_pair_impl : op_impl 3.
      refine (fun args => let '(Val tp p, Val ta _, Val tb _) := args in
                       match tp with
                       | Pair ta' tb' => fun p => _
                       | _ => fun _ => None
                       end p).
      refine (let '(a, b) := p in _).
      destruct (type_eq_dec ta' ta); [ | exact None ].
      destruct (type_eq_dec tb' tb); [ | exact None ].
      subst.
      refine (Some (split_pair_impl' ta tb a b)).
    Defined.

    Definition join_pair_impl : op_impl 3.
      refine (fun args => let '(Val tp _, Val ta va, Val tb vb) := args in
                       match tp with
                       | Pair ta' tb' => fun va vb => _
                       | _ => fun _ _ => None
                       end va vb).
      destruct (type_eq_dec ta' ta); [ | exact None ].
      destruct (type_eq_dec tb' tb); [ | exact None ].
      subst.
      refine (Some (join_pair_impl' ta tb va vb)).
    Defined.

    Definition map_add_impl : op_impl 3.
      refine (fun args => let '(Val tm m, Val tk k, Val tv v) := args in
                        match tm with
                        | AddrMap tv' => fun m => _
                        | _ => fun _ => None
                        end m).
      destruct (type_eq_dec tk Num); [ | exact None ].
      destruct (type_eq_dec tv tv'); [ | exact None ].
      destruct m as [m | ]; [ | exact None ].
      subst tv' tk.
      destruct k as [k | ]; [ | exact None ].
      refine (Some (map_add_impl' tv m k v)).
    Defined.

    Definition map_card_impl : op_impl 2.
      refine (fun args => let '(Val tm m, Val tc c) := args in
                        match tm with
                        | AddrMap tv' => fun m => _
                        | _ => fun _ => None
                        end m).
      destruct (type_eq_dec tc Num); [ | exact None ].
      destruct m as [ m | ]; [ | exact None ].
      refine (Some (map_card_impl' tv' m)).
    Defined.

    Definition map_find_impl : op_impl 3.
      refine (fun args => let '(Val tm m, Val tk k, Val tr r) := args in
                        match tm with
                        | AddrMap tv' => fun m => _
                        | _ => fun _ => None
                        end m).
      destruct (type_eq_dec tk Num); [ | exact None].
      destruct (type_eq_dec tr (Pair Bool tv')); [ | exact None ].
      subst tr tk.
      destruct m as [m | ]; [ | exact None].
      destruct k as [k | ]; [ | exact None].
      refine (Some (map_find_impl' tv' m k)).
    Defined.

    Definition map_remove_impl : op_impl 2.
      refine (fun args => let '(Val tm m, Val tk k) := args in
                        match tm with
                        | AddrMap tv' => fun m => _
                        | _ => fun _ => None
                        end m).
      destruct (type_eq_dec tk Num); [ | exact None ].
      subst tk.
      destruct m as [m | ]; [ | exact None].
      destruct k as [k | ]; [ | exact None].
      refine (Some (map_remove_impl' tv' m k)).
    Defined.

    Definition map_elements_impl : op_impl 2.
      refine (fun args => let '(Val tm m, Val tl l) := args in
                        match tm with
                        | AddrMap tm => fun m => _
                        | _ => fun _ => None
                        end m).
      destruct (type_eq_dec tl (Slice (Pair Num tm))); [ | exact None].
      destruct m as [m | ]; [ | exact None].
      refine (Some (map_elements_impl' tm m)).
    Defined.
  End NastyImpls.

  Definition impl_for (op : modify_op) : { n : nat & op_impl n } :=
    match op with
    | @SetConst t v => existT _ _ (setconst_impl t v)
    | DuplicateOp => existT _ _ duplicate_impl
    | AppendOp => existT _ _ append_impl
    | Uncons => existT _ _ uncons_impl
    | ModifyNumOp nop => existT _ _ (numop_impl nop)
    | SplitPair => existT _ _ split_pair_impl
    | JoinPair => existT _ _ join_pair_impl
    | MapAdd => existT _ _ map_add_impl
    | MapRemove => existT _ _ map_remove_impl
    | MapFind => existT _ _ map_find_impl
    | MapCardinality => existT _ _ map_card_impl
    | MapElements => existT _ _ map_elements_impl
    end.

  Definition op_arity (op : modify_op) : nat := projT1 (impl_for op).

  Definition eval_test_m (op : test) (oa ob : option value) : option value :=
    match oa, ob with
    | Some (Val Num (Here a)), Some (Val Num (Here b)) => eval_test_num op a b
    | Some (Val Bool a), Some (Val Bool b) => eval_test_bool op a b
    | _, _ => None
    end.

  Fixpoint eval (st : locals) (e : expr) : option value :=
    match e with
    | Var x => VarMap.find x st
    | Const t v => Some (Val t v)
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

  Inductive stmt :=
  | Skip : stmt
  | Seq : stmt -> stmt -> stmt
  | If : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt
  | Call num_params
         (f: label) (* The function to call *)
         (argvars: n_tuple num_params var) (* The caller's variables to pass in *)
  | Declare : type -> (var -> stmt) -> stmt
  | Assign : var -> expr -> stmt
  | Modify : forall op : modify_op, n_tuple (op_arity op) var -> stmt
  | DiskRead : var -> expr -> stmt
  | DiskWrite : expr -> expr -> stmt
  | DiskSync : stmt
  (* InCall and Undeclare only appear at runtime *)
  | Undeclare : var -> stmt
  | InCall (s0: locals) (* The stack frame inside the function *)
           num_params
           (argvars: n_tuple num_params var) (* The caller's variables which it passed in *)
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
  | SCall : forall np f argvars, source_stmt (Call np f argvars)
  | SAssign : forall x e, source_stmt (Assign x e)
  | SModify : forall op vars, source_stmt (Modify op vars)
  | SDeclare :
      forall t cont,
        (forall var, source_stmt (cont var)) ->
        source_stmt (Declare t cont)
  | SDiskRead : forall x a, source_stmt (DiskRead x a)
  | SDiskWrite : forall a v, source_stmt (DiskWrite a v)
  | SDiskSync : source_stmt (DiskSync).

  Hint Resolve andb_prop.
  Hint Resolve andb_true_intro.

  Definition mapsto_can_alias x st :=
    match find x st with
    | Some v => can_alias v
    | None => true
    end.

  (* Update the caller's scope after a function call *)
  Fixpoint add_remove_many keys (input : list value) (output : list (option value)) st :=
    match keys, input, output with
    | k :: keys', i :: input', o :: output' =>
      let st' :=
          if can_alias (type_of i)
          then st
          else MoreVarMapFacts.update k o st
      in
      add_remove_many keys' input' output' st'
    | _, _, _ => st
    end.

  Definition value_well_typed type value :=
    match value with
    | Val t _ =>
      if type_eq_dec type t
      then true
      else false
    end.

  Definition values_well_typed {n} :
    forall (types : n_tuple n type) (values : n_tuple n value),
      bool.
    induction n; intros.
    - exact true.
    - simpl in *; destruct n.
      + exact (value_well_typed types values).
      + exact (value_well_typed (snd types) (snd values) && IHn (fst types) (fst values)).
  Defined.

  Definition update_one key old (update : var_update) st :=
    match update with
    | SetTo v =>
      if type_eq_dec (type_of old) (type_of v)
      then Some (VarMap.add key v st)
      else None
    | Move => Some (VarMap.add key (moved_value old) st)
    | Leave => Some st
    end.

  (* Update a scope for an operation *)
  Definition update_many {n} :
    forall (keys : n_tuple n var) (old : n_tuple n value) (update : n_tuple n var_update) (st : VarMap.t value),
      option (VarMap.t value).
    induction n; intros.
    - exact (Some st). (* n = 0 *)
    - simpl in *; destruct n.
      + exact (update_one keys old update st). (* n = 1 *)
      + exact (let ost' := update_one (snd keys) (snd old) (snd update) st
               in match ost' with
                  | None => None
                  | Some st' => IHn (fst keys) (fst old) (fst update) st'
                  end). (* n > 1 *)
  Defined.

  Definition add_many {n} :
    forall (keys : n_tuple n var) (values : n_tuple n value) (st : VarMap.t value),
      VarMap.t value.
    induction n; intros.
    - exact st.
    - simpl in *; destruct n.
      + exact (VarMap.add keys values st).
      + exact (VarMap.add (snd keys) (snd values) (IHn (fst keys) (fst values) st)).
  Defined.
 
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

  Record FunctionSpec :=
    {
      (* Parameters are numbered in [0, NumParamVars). *)
      NumParamVars : nat;
      ParamVars : n_tuple NumParamVars type;
      Body : stmt;
      body_source : source_stmt Body;
      (* TODO syntax_ok with is_actual_args_no_dup ? *)
    }.

  Definition Env := StringMap.t FunctionSpec.

  Record frame :=
    {
      Locs : locals;
      Cont : stmt;
      Spec : FunctionSpec;
      Args : list var;
      RetV : var;
    }.

  Section EnvSection.

    Variable env : Env.

    Definition sel T m := fun k => VarMap.find k m : option T.

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
    | RunsToModify : forall op vars (s s' : locals) d
                       (vs0 : n_tuple (op_arity op) value)
                       (vs : n_tuple (op_arity op) var_update),
        collect (map_nt (sel s) vars) = Some vs0 ->
        projT2 (impl_for op) vs0 = Some vs ->
        Some s' = update_many vars vs0 vs s ->
        runsto (Modify op vars) (d, s) (d, s')
    | RunsToDiskRead : forall x ae a d s s' v0 v vs,
        VarMap.find x s = Some v0 -> (* variable must be declared *)
        type_of v0 = DiskBlock -> (* and have the correct type *)
        eval s ae = Some (Val Num (Here a)) ->
        d a = Some (v, vs) ->
        s' = VarMap.add x (Val DiskBlock (Here v)) s ->
        runsto (DiskRead x ae) (d, s) (d, s')
    | RunsToDiskWrite : forall ae a ve v (d : rawdisk) d' s v0 v0s,
        eval s ae = Some (Val Num (Here a)) ->
        eval s ve = Some (Val DiskBlock (Here v)) ->
        d a = Some (v0, v0s) ->
        d' = upd d a (v, v0 :: v0s) ->
        runsto (DiskWrite ae ve) (d, s) (d', s)
    | RunsToDiskSync : forall (d : rawdisk) d' s,
        d' = sync_mem d ->
        runsto DiskSync (d, s) (d', s)
    | RunsToCall : forall spec f argvars s s' d d' argvals argvals' callee_s',
        StringMap.find f env = Some spec ->
        source_stmt spec.(Body) ->
        collect (map_nt (sel s) argvars) = Some argvals ->
        values_well_typed spec.(ParamVars) argvals = true ->
        let param_names := seq_nt 0 spec.(NumParamVars) in
        let callee_s := add_many param_names argvals (VarMap.empty _) in
        runsto spec.(Body) (d, callee_s) (d', callee_s') ->
        collect (map_nt (sel callee_s') param_names) = Some argvals' ->
        update_many argvars argvals (map_nt SetTo argvals') s = Some s' ->
        runsto (Call spec.(NumParamVars) f argvars) (d, s) (d', s').

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
    | StepModify : forall op vars (s s' : locals) d
                     (vs0 : n_tuple (op_arity op) value)
                     (vs : n_tuple (op_arity op) var_update),
        collect (map_nt (sel s) vars) = Some vs0 ->
        projT2 (impl_for op) vs0 = Some vs ->
        Some s' = update_many vars vs0 vs s ->
        step (d, s, Modify op vars) (d, s', Skip)
    | StepDiskRead : forall x ae a d s s' v v0 vs,
        VarMap.find x s = Some v0 -> (* variable must be declared *)
        type_of v0 = DiskBlock -> (* and have the correct type *)
        eval s ae = Some (Val Num (Here a)) ->
        d a = Some (v, vs) ->
        s' = VarMap.add x (Val DiskBlock (Here v)) s ->
        step (d, s, DiskRead x ae) (d, s', Skip)
    | StepDiskWrite : forall ae a ve v d d' s v0 v0s,
        eval s ae = Some (Val Num (Here a)) ->
        eval s ve = Some (Val DiskBlock (Here v)) ->
        d a = Some (v0, v0s) ->
        d' = upd d a (v, v0 :: v0s) ->
        step (d, s, DiskWrite ae ve) (d', s, Skip)
    | StepDiskSync : forall (d : rawdisk) d' s,
        d' = sync_mem d ->
        step (d, s, DiskSync) (d', s, Skip)
    | StepStartCall :
        forall spec s f argvars d argvals,
          StringMap.find f env = Some spec ->
          source_stmt (Body spec) ->
          collect (map_nt (sel s) argvars) = Some argvals ->
          values_well_typed spec.(ParamVars) argvals = true ->
          let param_names := seq_nt 0 spec.(NumParamVars) in
          let callee_s := add_many param_names argvals (VarMap.empty _) in
          step (d, s, Call spec.(NumParamVars) f argvars)
               (d, callee_s, InCall s spec.(NumParamVars) argvars spec.(Body))
    | StepInCall :
        forall st p st' p' s0 np argvars,
          step (st, p) (st', p') ->
          step (st, InCall s0 np argvars p)
               (st', InCall s0 np argvars p')
    | StepEndCall :
        forall callee_s' s s' d numparams argvals argvals' argvars,
          collect (map_nt (sel s) argvars) = Some argvals ->
          let param_names := seq_nt 0 numparams in
          collect (map_nt (sel callee_s') param_names) = Some argvals' ->
          update_many argvars argvals (map_nt SetTo argvals') s = Some s' ->
          step (d, callee_s', InCall s numparams argvars Skip) (d, s', Skip).

    Inductive outcome :=
    | Failed
    | Finished (st : rawdisk * locals)
    | Crashed (d : rawdisk).

    Inductive crash_step : stmt -> Prop :=
    | CrashSeq1 : forall a b,
        crash_step a ->
        crash_step (Seq a b)
    | CrashInCall : forall s np args p,
        crash_step p ->
        crash_step (InCall s np args p)
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

    Hint Extern 1 (_ = Datatypes.length (snd (split _))) => rewrite split_length_r.

    Ltac do_inv :=
      match goal with
      | [ H : step _ _ |- _ ] => invc H; eauto
      | [ H : clos_refl_trans_1n _ _ _ _ |- _ ] => invc H; eauto
      end.

    Lemma steps_incall :
      forall s0 np args st p st' p',
        step^* (st, p) (st', p') ->
        step^* (st, InCall s0 np args p) (st', InCall s0 np args p').
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
    Hint Extern 1 (step (_, _, Assign _ _) _) =>
    eapply StepAssign.
    Hint Extern 1 (step (_, _, Modify _ _) _) =>
    eapply StepModify.
    Hint Extern 1 (step (_, _, Declare _ _) _) =>
    eapply StepDeclare.
    Hint Extern 1 (step (_, _, Undeclare _) _) =>
    eapply StepUndeclare.
    Hint Extern 1 (step (_, _, DiskRead _ _) _) =>
    eapply StepDiskRead.
    Hint Extern 1 (step (_, _, DiskWrite _ _) _) =>
    eapply StepDiskWrite.
    Hint Extern 1 (step (_, _, DiskSync) _) =>
    eapply StepDiskSync.
    Hint Extern 1 (step (_, Call _ _ _) _) =>
    eapply StepStartCall.
    Hint Extern 1 (step (_, InCall _ _ _ _) _) =>
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
    | RunsToICModify : forall op vars (s s' : locals) d
                         (vs0 : n_tuple (op_arity op) value)
                         (vs : n_tuple (op_arity op) var_update),
        collect (map_nt (sel s) vars) = Some vs0 ->
        projT2 (impl_for op) vs0 = Some vs ->
        Some s' = update_many vars vs0 vs s ->
        runsto_InCall (Modify op vars) (d, s) (d, s')
    | RunsToICDiskRead : forall x ae a d s s' v v0 vs,
        VarMap.find x s = Some v0 -> (* variable must be declared *)
        type_of v0 = DiskBlock -> (* and have the correct type *)
        eval s ae = Some (Val Num (Here a)) ->
        d a = Some (v, vs) ->
        s' = VarMap.add x (Val DiskBlock (Here v)) s ->
        runsto_InCall (DiskRead x ae) (d, s) (d, s')
    | RunsToICDiskWrite : forall ae a ve v d d' s v0 v0s,
        eval s ae = Some (Val Num (Here a)) ->
        eval s ve = Some (Val DiskBlock (Here v)) ->
        d a = Some (v0, v0s) ->
        d' = upd d a (v, v0 :: v0s) ->
        runsto_InCall (DiskWrite ae ve) (d, s) (d', s)
    | RunsToICDiskSync : forall (d : rawdisk) d' s,
        d' = sync_mem d ->
        runsto_InCall DiskSync (d, s) (d', s)
    | RunsToICCall : forall spec f argvars s s' d d' argvals argvals' callee_s',
        StringMap.find f env = Some spec ->
        source_stmt (Body spec) ->
        collect (map_nt (sel s) argvars) = Some argvals ->
        values_well_typed spec.(ParamVars) argvals = true ->
        let param_names := seq_nt 0 spec.(NumParamVars) in
        let callee_s := add_many param_names argvals (VarMap.empty _) in
        runsto_InCall (Body spec) (d, callee_s) (d', callee_s') ->
        collect (map_nt (sel callee_s') param_names) = Some argvals' ->
        update_many argvars argvals (map_nt SetTo argvals') s = Some s' ->
        runsto_InCall (Call spec.(NumParamVars) f argvars) (d, s) (d', s')
    | RunsToInCall : forall p callee_s callee_s' s s' d d' numparams argvals argvals' argvars,
          collect (map_nt (sel s) argvars) = Some argvals ->
          let param_names := seq_nt 0 numparams in
          collect (map_nt (sel callee_s') param_names) = Some argvals' ->
          update_many argvars argvals (map_nt SetTo argvals') s = Some s' ->
          runsto_InCall p (d, callee_s) (d', callee_s') ->
          runsto_InCall (InCall s numparams argvars p) (d, callee_s) (d', s').

    Hint Constructors source_stmt.

    Lemma source_stmt_RunsToInCall_runsto :
      forall p,
        source_stmt p ->
        forall st st',
          runsto_InCall p st st' ->
          runsto p st st'.
    Proof.
      induction 2; intros; subst_definitions; invc H; eauto 10;
        repeat find_apply_lem_hyp inj_pair2; subst; eauto.
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
      - destruct st', st''. invc H0_0. eauto.
      - repeat find_apply_lem_hyp inj_pair2; subst.
        assert (Some argvals = Some argvals0) by congruence.
        find_inversion. eauto.
      - repeat find_apply_lem_hyp inj_pair2; subst. destruct st. eauto.
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

Notation "A ; B" := (Go.Seq A B) (at level 201, B at level 201, left associativity, format "'[v' A ';' '/' B ']'") : go_scope.
Notation "x <~ y" := (Go.Assign x y) (at level 90) : go_scope.
(* TODO: better syntax *)
Notation "x <~const v" := (Go.Modify (Go.SetConst v) (x : Go.n_tuple 1 Go.var)) (at level 90): go_scope.
Notation "x <~dup y" := (Go.Modify Go.DuplicateOp (x, y)) (at level 90): go_scope.
Notation "x <~num A * B" := (Go.Modify (Go.ModifyNumOp Go.Times) (x, A, B)) (at level 90): go_scope.
Notation "x <~num A + B" := (Go.Modify (Go.ModifyNumOp Go.Plus ) (x, A, B)) (at level 90): go_scope.
Notation "x <~num A - B" := (Go.Modify (Go.ModifyNumOp Go.Minus) (x, A, B)) (at level 90): go_scope.
Notation "'__'" := (Go.Skip) : go_scope.
Notation "'While' A B" := (Go.While A B) (at level 200, A at level 0, B at level 1000, format "'[v    ' 'While'  A '/' B ']'") : go_scope.
Notation "'If' a 'Then' b 'Else' c 'EndIf'" := (Go.If a b c) (at level 200, a at level 1000, b at level 1000, c at level 1000) : go_scope.