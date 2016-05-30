Require Import PeanoNat String List FMapAVL.
Require Import Word StringMap.

Import ListNotations.

(* TODO: Call something other than "Facade?" *)

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

Local Open Scope string_scope.

Definition diskstate := bool.

Definition dummy_diskstate : diskstate := false. (* :/ *)


Inductive prog T :=
| Done (v: T)
| SetState (s: diskstate) (rx: unit -> prog T)
| GetState (rx: diskstate -> prog T).

Inductive step T : diskstate -> prog T -> diskstate -> prog T -> Prop :=
| StepSet : forall s s' rx, step s (SetState s' rx) s' (rx tt)
| StepGet : forall s rx, step s (GetState rx) s (rx s).

Hint Constructors step.

Inductive outcome (T : Type) :=
| Finished (d: diskstate) (v: T).

Inductive exec T : diskstate -> prog T -> outcome T -> Prop :=
| XStep : forall d p d' p' out,
  step d p d' p' ->
  exec d' p' out ->
  exec d p out
| XDone : forall d v,
  exec d (Done v) (Finished d v).

Hint Constructors exec.


Definition computes_to A (p : forall T, (A -> prog T) -> prog T) (d d' : diskstate) (x : A) :=
  forall T (rx : A -> prog T) d'' (y : T),
    exec d' (rx x) (Finished d'' y) <-> exec d (p T rx) (Finished d'' y).

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

Arguments Assign v val%facade.

Inductive Value :=
| SCA : W -> Value
| Disk : diskstate -> Value.

Definition is_mutable v :=
  match v with
  | SCA _ => false
  | Disk _ => true
  end.


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

Definition mapsto_mutable x st :=
  match find x st with
  | Some v => is_mutable v
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
| RunsToAssign : forall x e st st' v,
    (* rhs can't be a mutable object, to prevent aliasing *)
    eval st e = Some v ->
    is_mutable v = false ->
    st' = add x v st ->
    RunsTo (Assign x e) st st'.

Arguments RunsTo prog%facade st st'.

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
| NTSome (key: string) (H: FacadeWrapper Value T) : NameTag T.

Arguments NTSome {T} key {H}.

(*
Inductive ScopeValue A :=
| ProgRet (start : diskstate) (p : forall T, (A -> prog T) -> prog T)
| ProgDisk (start : diskstate) (p : forall T, (A -> prog T) -> prog T).

Definition ScopeValueIs A (val : ScopeValue A) :=
  match val return (match val with
                    | ProgRet _ _ => A
                    | ProgDisk _ _ => diskstate
                    end) -> Prop with
  | ProgRet d p => fun r => exists d', computes_to p d d' r
  | ProgDisk d p => fun d' => exists r, computes_to p d d' r
  end.

Infix "↝" := ScopeValueIs (at level 60).
*)

Inductive ScopeItem :=
| SItemRet A (key : NameTag A) (start : diskstate) (p : forall T, (A -> prog T) -> prog T)
| SItemDisk A (key : NameTag diskstate) (start : diskstate) (p : forall T, (A -> prog T) -> prog T).

(*
Notation "` k ->> v" := (SItemRet (NTSome k) v) (at level 50).
*)

(* Not really a telescope; should maybe just be called Scope *)
(* TODO: use fmap *)
Definition Telescope := list ScopeItem.

Fixpoint SameValues (st : State) (tenv : Telescope) :=
  match tenv with
  | [] => True
  | SItemRet key d0 p :: tail =>
    match key with
    | NTSome k =>
      match StringMap.find k st with
      | Some v => exists v' d, computes_to p d0 d v' /\ v = wrap v'
      | None => False
      end /\ SameValues (StringMap.remove k st) tail
    end
  | SItemDisk key d0 p :: tail =>
    match key with
    | NTSome k =>
      match StringMap.find k st with
      | Some d => exists d' r, computes_to p d0 d' r /\ d = wrap d'
      | None => False
      end /\ SameValues (StringMap.remove k st) tail
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

Instance FacadeWrapper_Disk : FacadeWrapper Value diskstate.
Proof.
  refine {| wrap := Disk;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

(*
Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [ `"out" ->> post ] }}) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'     ").
*)

Definition ret A (x : A) : forall T, (A -> prog T) -> prog T := fun T rx => rx x.

Definition extract_code := projT1.

Ltac invert H := inversion H; subst; clear H.

(* TODO: use Pred.v's *)
Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; intuition subst
  end.


Lemma ret_computes_to : forall A (x x' : A) d d', computes_to (ret x) d d' x' -> x = x'.
Proof.
  unfold ret, computes_to.
  intros.
  specialize (H A (@Done A) d x).
  destruct H as [_ H].
  specialize (H ltac:(do 2 econstructor)).
  invert H.
  invert H0.
  trivial.
Qed.

Lemma ret_computes_to_disk : forall A (x x' : A) d d', computes_to (ret x) d d' x' -> d = d'.
Proof.
  unfold ret, computes_to.
  intros.
  specialize (H A (@Done A) d x).
  destruct H as [_ H].
  specialize (H ltac:(do 2 econstructor)).
  invert H.
  invert H0.
  trivial.
Qed.

Lemma ret_computes_to_refl : forall A (x : A) d, computes_to (ret x) d d x.
Proof.
  split; eauto.
Qed.

Hint Resolve ret_computes_to_refl.


Example micro_noop : sigT (fun p => forall d0,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }} p {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }}).
Proof.
  eexists.
  intros.
  instantiate (1 := Skip).
  intro. intros.
  invert H0. eauto.
Defined.


Example micro_write5 : sigT (fun p => forall d0,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }} p {{ [ SItemDisk (NTSome "disk") d0 (fun T => @SetState T false) ] }}).
Proof.
  (* Can't instantiate this yet -- need a way to write in the extraction. *)
Abort.

Ltac maps := rewrite ?StringMapFacts.remove_neq_o, ?StringMapFacts.add_neq_o, ?StringMapFacts.add_eq_o in * by congruence.

Example micro_plus : sigT (fun p => forall d0 x y,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "x") d0 (ret x) ; SItemRet (NTSome "y") d0 (ret y) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "out") d0 (ret (x + y)) ] }}).
Proof.
  eexists.
  intros.
  instantiate (1 := ("out" <- (Var "x" + Var "y"))%facade).
  intro. intros.
  invert H0.
  simpl in *.
  maps.
  destruct (find "disk" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "x" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "y" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  intuition idtac.
  repeat deex.
  simpl in *.
  invert H3.
  eexists. exists d0. intuition.
  apply ret_computes_to in H2.
  apply ret_computes_to in H1.
  apply ret_computes_to_disk in H0.
  subst.
  trivial.
Defined.


(*
Example micro_double :
  ParametricExtraction
    #vars        x
    #program     (fun T => @Double T x)
    #arguments [`"x" ->> ret x ].
Proof.
  eexists.
  intros.
  instantiate (1 := ("out" <- Var "x" + Var "x")%facade).
  (* TODO! *)
  intro.
  intros.
  simpl in H.
  inversion H0.
  simpl.
  subst.
  rewrite StringMapFacts.add_eq_o; intuition.
  simpl in H3.
  destruct (find "x" initial_state); intuition.
  destruct v, v0.
  simpl in H3.
  deex.
  inversion H3; inversion H5; subst.
  apply ret_computes_to in H1; subst.
  eexists.
  split; [ | trivial ].
  split; eauto.
  intros.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  trivial.
Defined.


Example micro_if :
  ParametricExtraction
    #vars      flag (x y : nat)
    #program   ret (if (Bool.bool_dec flag true) then x else y)
    #arguments [`"flag" ->> ret flag ; `"x" ->> ret x ; `"y" ->> ret y].
Proof.
  eexists.
  intros.
  instantiate (1 := (If (Var "flag") Then (Assign "out" (Var "x")) Else (Assign "out" (Var "y")) EndIf)%facade).
  (* TODO! *)
  intro.
  intros.
  simpl in H.
  inversion H0.
  - inversion H7. simpl; subst; intuition.
    repeat rewrite StringMapFacts.add_eq_o in * by congruence.
    repeat rewrite StringMapFacts.remove_neq_o in * by congruence.
    unfold is_true, is_false, eval_bool, eval in *.
    destruct (find "flag" initial_state); intuition; subst.
    destruct (find "x" initial_state); intuition; subst.
    destruct (find "y" initial_state); intuition; subst.
    repeat deex.
    apply ret_computes_to in H3; apply ret_computes_to in H2; apply ret_computes_to in H1; subst.
    inversion H10; subst.
    eexists; intuition eauto.
    destruct (Bool.bool_dec v'1 true); try solve [ destruct (Nat.eq_dec 0 0); congruence ].
  - inversion H7. simpl; subst; intuition.
    repeat rewrite StringMapFacts.add_eq_o in * by congruence.
    repeat rewrite StringMapFacts.remove_neq_o in * by congruence.
    unfold is_true, is_false, eval_bool, eval in *.
    destruct (find "flag" initial_state); intuition; subst.
    destruct (find "x" initial_state); intuition; subst.
    destruct (find "y" initial_state); intuition; subst.
    repeat deex.
    apply ret_computes_to in H3; apply ret_computes_to in H2; apply ret_computes_to in H1; subst.
    inversion H10; subst.
    eexists; intuition eauto.
    destruct (Bool.bool_dec v'1 true); try solve [ destruct (Nat.eq_dec 1 0); congruence ].
Defined.

Definition micro_if_code := Eval lazy in (extract_code micro_if).
Print micro_if_code.*)
