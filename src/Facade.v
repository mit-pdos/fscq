Require Import PeanoNat String List FMapAVL.
Require Import Word StringMap.

Import ListNotations.

(* TODO: Call something other than "Facade?" *)

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

Local Open Scope string_scope.

Definition addr := nat.
Definition valu := nat.

Definition diskstate := addr -> valu.

Definition upd (a : addr) (v : valu) (d : diskstate) :=
  fun a0 =>
    if Nat.eq_dec a a0 then v else d a0.

Opaque upd.

Inductive prog T :=
| Done (v: T)
| Read (a: addr) (rx: valu -> prog T)
| Write (a: addr) (v: valu) (rx: unit -> prog T).

Inductive step T : diskstate -> prog T -> diskstate -> prog T -> Prop :=
| StepRead : forall d a rx, step d (Read a rx) d (rx (d a))
| StepWrite : forall d a v rx, step d (Write a v rx) (upd a v d) (rx tt).

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
| Call : var -> label -> list var -> Stmt
| Assign : var -> Expr -> Stmt.

Arguments Assign v val%facade.

Inductive Value :=
| SCA : W -> Value
| Disk : diskstate -> Value.

Definition can_alias v :=
  match v with
  | SCA _ => true
  | Disk _ => false
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

Record AxiomaticSpec := {
  PreCond (input : list Value) : Prop;
  PostCond (input_output : list (Value * option Value)) (ret : Value) : Prop;
  (* PreCondTypeConform : type_conforming PreCond *)
}.

Definition Env := StringMap.t AxiomaticSpec.

Inductive RunsTo (env : Env) : Stmt -> State -> State -> Prop :=
| RunsToSkip : forall st,
    RunsTo env Skip st st
| RunsToSeq : forall a b st st' st'',
    RunsTo env a st st' ->
    RunsTo env b st' st'' ->
    RunsTo env (Seq a b) st st''
| RunsToIfTrue : forall cond t f st st',
    is_true st cond ->
    RunsTo env t st st' ->
    RunsTo env (If cond t f) st st'
| RunsToIfFalse : forall cond t f st st',
    is_false st cond ->
    RunsTo env f st st' ->
    RunsTo env (If cond t f) st st'
| RunsToWhileTrue : forall cond body st st' st'',
    let loop := While cond body in
    is_true st cond ->
    RunsTo env body st st' ->
    RunsTo env loop st' st'' ->
    RunsTo env loop st st''
| RunsToWhileFalse : forall cond body st st',
    let loop := While cond body in
    is_false st cond ->
    RunsTo env loop st st'
| RunsToAssign : forall x e st st' v,
    (* rhs can't be a mutable object, to prevent aliasing *)
    eval st e = Some v ->
    can_alias v = true ->
    st' = add x v st ->
    RunsTo env (Assign x e) st st'
| RunsToCallAx : forall x f args st spec input output ret,
    StringMap.find f env = Some spec ->
    mapM (fun k => find k st) args = Some input ->
    mapsto_can_alias x st = true ->
    PreCond spec input ->
    length input = length output ->
    PostCond spec (List.combine input output) ret ->
    let st' := add_remove_many args input output st in
    let st' := add x ret st' in
    RunsTo env (Call x f args) st st'.

Arguments RunsTo env prog%facade st st'.

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

Definition ProgOk env prog (initial_tstate final_tstate : Telescope) :=
  forall initial_state : State,
    initial_state ≲ initial_tstate ->
    (* Safe ... /\ *)
    forall final_state : State,
      RunsTo env prog initial_state final_state ->
      (final_state ≲ final_tstate).

Arguments ProgOk env prog%facade_scope initial_tstate final_tstate.

Notation "{{ A }} P {{ B }} // EV" :=
  (ProgOk EV P A B)
    (at level 60, format "'[v' '{{'  A  '}}' '/'    P '/' '{{'  B  '}}'  //  EV ']'").

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

Ltac maps := rewrite ?StringMapFacts.remove_neq_o, ?StringMapFacts.add_neq_o, ?StringMapFacts.add_eq_o in * by congruence.


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
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }} p {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }} // empty _).
Proof.
  eexists.
  intros.
  instantiate (1 := Skip).
  intro. intros.
  invert H0. eauto.
Defined.

Definition write : AxiomaticSpec.
  refine {|
    PreCond := fun args => exists (d : diskstate) (a : addr) (v : valu),
      args = (wrap d) :: (wrap a) :: (wrap v) :: nil;
    PostCond := fun args ret => exists (d : diskstate) (a : addr) (v : valu),
      args = (wrap d, Some (wrap (upd a v d))) :: (wrap a, None) :: (wrap v, None) :: nil
  |}.
Defined.

Definition disk_env : Env := add "write" write (empty _).

Example micro_write : sigT (fun p => forall d0 a v,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "a") d0 (ret a) ; SItemRet (NTSome "v") d0 (ret v) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (fun T => @Write T a v) ] }} // disk_env).
Proof.
  eexists.
  intros.
  (* TODO: when I pass wrong # of arguments, this just becomes trivially provable..... *)
  instantiate (1 := (Call "_" "write" ["disk"; "a"; "v"])%facade).
  intro. intros.
  invert H0.
  simpl in *.
  maps.
  compute in H4.
  invert H4.
  simpl in *.
  destruct (find "disk" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "a" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "v" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  intuition idtac.
  repeat deex.
  apply ret_computes_to in H1.
  apply ret_computes_to in H2.
  apply ret_computes_to_disk in H0.
  invert H.
  invert H5.
  do 3 (destruct output; try discriminate).
  simpl in *.
  invert H7.
  subst st'.
  maps.
  do 2 eexists; intuition.
  econstructor.
  econstructor.
  econstructor.
  eauto.
  intro.
  invert H.
  invert H0.
  eauto.
Defined.

Example micro_plus : sigT (fun p => forall d0 x y,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "x") d0 (ret x) ; SItemRet (NTSome "y") d0 (ret y) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "out") d0 (ret (x + y)) ] }} // empty _).
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
