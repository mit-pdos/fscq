Require Import PeanoNat String List FMapAVL.
Require Import Word StringMap.

Import ListNotations.

Local Open Scope string_scope.

(* TODO: Call something other than "Facade?" *)

Set Implicit Arguments.

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
(* | Call : var -> label -> list var -> Stmt (* TODO *) *)
| Assign : var -> Expr -> Stmt.

Inductive Value :=
| SCA : W -> Value.
(* TODO ADT *)


Definition State := StringMap.t Value.

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
    | Some (SCA a), Some (SCA b) => Some (SCA (eval_binop op a b))
    | _, _ => None
  end.

Fixpoint eval (st : State) (e : Expr) : option Value :=
  match e with
    | Var x => find x st
    | Const w => Some (SCA w)
    | Binop op a b => eval_binop_m (inl op) (eval st a) (eval st b)
    | TestE op a b => eval_binop_m (inr op) (eval st a) (eval st b)
  end.

Definition eval_bool st e : option bool :=
  match eval st e with
    | Some (SCA w) => Some (if Nat.eq_dec w 0 then false else true)
    | _ => None
  end.

Definition is_true st e := eval_bool st e = Some true.
Definition is_false st e := eval_bool st e = Some false.

Definition not_mapsto_adt x st :=
  match find x st with
  | Some (SCA _) => true
  (* | Some _ => false *) (* TODO *)
  | None => true
  end.

(* Definition Env := StringMap.t _. *)

Inductive RunsTo (* TODO env *) : Stmt -> State -> State -> Prop :=
| RunsToSkip : forall st,
    RunsTo Skip st st
| RunsToSeq : forall a b st st' st'',
    RunsTo a st st' ->
    RunsTo b st' st'' ->
    RunsTo (Seq a b) st st''
| RunsToIfTrue : forall cond t f st st',
    is_true st cond ->
    RunsTo t st st' ->
    RunsTo (If cond t f) st st'
| RunsToIfFalse : forall cond t f st st',
    is_false st cond ->
     RunsTo f st st' ->
    RunsTo (If cond t f) st st'
| RunsToWhileTrue : forall cond body st st' st'',
    let loop := While cond body in
    is_true st cond ->
    RunsTo body st st' ->
    RunsTo loop st' st'' ->
    RunsTo loop st st''
| RunsToWhileFalse : forall cond body st st',
    let loop := While cond body in
    is_false st cond ->
    RunsTo loop st st'
| RunsToAssign : forall x e st st' w,
    (* rhs can't be an ADT object, to prevent aliasing *)
    eval st e = Some (SCA w) ->
    (* lhs can't be already referring to an ADT object, to prevent memory leak *)
    not_mapsto_adt x st = true ->
    st' = add x (SCA w) st ->
    RunsTo (Assign x e) st st'.


Notation "A ; B" := (Seq A B) (at level 201, B at level 201, left associativity, format "'[v' A ';' '/' B ']'") : facade_scope.
Notation "x <- y" := (Assign x y) (at level 90) : facade_scope.
Notation "'__'" := (Skip) : facade_scope.
Notation "'While' A B" := (While A B) (at level 200, A at level 0, B at level 1000, format "'[v    ' 'While'  A '/' B ']'") : facade_scope.
Notation "'If' a 'Then' b 'Else' c 'EndIf'" := (If a b c) (at level 200, a at level 1000, b at level 1000, c at level 1000) : facade_scope.


(* TODO What here is actually necessary? *)

Class FacadeWrapper (WrappingType WrappedType: Type) :=
  { wrap:        WrappedType -> WrappingType;
    wrap_inj: forall v v', wrap v = wrap v' -> v = v' }.

Inductive NameTag T :=
| NTNone : NameTag T
| NTSome (key: string) (H: FacadeWrapper Value T) : NameTag T.

Arguments NTNone {T}.
Arguments NTSome {T} key {H}.

Inductive ScopeItem :=
| SItem T (key : NameTag T) (val : T).

Notation "` k ->> v" := (SItem (NTSome k) v) (at level 50).

(* Not really a telescope; should maybe just be called Scope *)
Definition Telescope := list ScopeItem.

(* TODO: allow forgetting values? maybe just allow forgetting anything, including ADTs, if we're assuming GC *)
Definition StatesEqual (m1 m2: State) := forall k v, StringMap.MapsTo k v m1 <-> StringMap.MapsTo k v m2.

(* TODO: doesn't need to be a fixpoint *)
Fixpoint SameValues st (tenv : Telescope) :=
  match tenv with
  | [] => StringMap.Empty st
  | SItem key val :: tail =>
    match key with
    | NTSome k =>
      match StringMap.find k st with
      | Some v => wrap val = v /\ SameValues (StringMap.remove k st) tail
      | None => False
      end
    | NTNone => SameValues st tail
    end
  end.

Notation "ENV ≲ TENV" := (SameValues ENV TENV) (at level 50).

Definition ProgOk (* env *) prog (initial_tstate final_tstate : Telescope) :=
  forall initial_state : State,
    initial_state ≲ initial_tstate ->
    (* Safe ... /\ *)
    forall final_state : State,
      RunsTo (* env *) prog initial_state final_state ->
      (final_state ≲ final_tstate).
Arguments ProgOk prog%facade_scope initial_tstate final_tstate.

Notation "{{ A }} P {{ B }}" :=
  (ProgOk (* EV *) P A B)
    (at level 60, format "'[v' '{{'  A  '}}' '/'    P '/' '{{'  B  '}}' ']'").

Ltac FacadeWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | [ H : _ = _ |- _ ] => inversion H; solve [eauto]
                   | _ => solve [eauto]
                   end).

Instance FacadeWrapper_SCA : FacadeWrapper Value W.
Proof.
  refine {| wrap := SCA;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_Self {A: Type} : FacadeWrapper A A.
Proof.
  refine {| wrap := id;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [ `"out" ->> post ] }}) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'     ").

Example micro_plus :
  ParametricExtraction
    #vars      x y
    #program   x + y
    #arguments [`"x" ->> x ; `"y" ->> y].
Proof.
  eexists.
  intros.
  instantiate (1 := Assign "out" (Binop Plus (Var "x") (Var "y"))).
  (* TODO! *)
Abort.
