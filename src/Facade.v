Require Import PeanoNat String List FMapAVL.
Require Import Word StringMap.

Import ListNotations.

(* TODO: Call something other than "Facade?" *)

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.


Ltac invert H := inversion H; subst; clear H.

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

Definition addr := nat.
Definition valu := nat.

Definition memory := addr -> valu.

Definition upd (a : addr) (v : valu) (d : memory) :=
  fun a0 =>
    if Nat.eq_dec a a0 then v else d a0.

Opaque upd.

Inductive prog T :=
| Done (v: T)
| Read (a: addr) (rx: valu -> prog T)
| Write (a: addr) (v: valu) (rx: unit -> prog T).

Inductive step T : memory -> prog T -> memory -> prog T -> Prop :=
| StepRead : forall d a rx, step d (Read a rx) d (rx (d a))
| StepWrite : forall d a v rx, step d (Write a v rx) (upd a v d) (rx tt).

Hint Constructors step.

Inductive outcome (T : Type) :=
| Failed
| Finished (d: memory) (v: T)
| Crashed (d: memory).

Inductive exec T : memory -> prog T -> outcome T -> Prop :=
| XStep : forall d p d' p' out,
  step d p d' p' ->
  exec d' p' out ->
  exec d p out
| XFail : forall d p, (~exists d' p', step d p d' p') ->
  (~exists r, p = Done r) ->
  exec d p (Failed T)
| XCrash : forall d p, exec d p (Crashed T d)
| XDone : forall d v,
  exec d (Done v) (Finished d v).

Hint Constructors exec.

Definition trace := list (addr * valu).

Inductive step_trace T : memory -> trace -> prog T -> memory -> trace -> prog T -> Prop :=
| StepTRead : forall d tr a rx , step_trace d tr (Read a rx) d tr (rx (d a))
| StepTWrite : forall d tr a v rx, step_trace d tr (Write a v rx) (upd a v d) ((a, v) :: tr) (rx tt).

Hint Constructors step_trace.

Inductive exec_trace T : memory -> trace -> prog T -> outcome T -> trace -> Prop :=
| XTStep : forall d p d' p' out tr tr' tr'',
  step_trace d tr p d' tr' p' ->
  exec_trace d' tr' p' out tr'' ->
  exec_trace d tr p out tr''
| XTFail : forall d p tr, (~exists d' p', step d p d' p') ->
  (~exists r, p = Done r) ->
  exec_trace d tr p (Failed T) tr
| XTCrash : forall d p tr, exec_trace d tr p (Crashed T d) tr
| XTDone : forall d v tr,
  exec_trace d tr (Done v) (Finished d v) tr.

Hint Constructors exec_trace.

Notation diskstate := (memory * trace)%type.

Definition computes_to A (p : forall T, (A -> prog T) -> prog T) (d d' : diskstate) (x : A) :=
  forall T (rx : A -> prog T) d'' (y : T),
    exec_trace (fst d') (snd d') (rx x) (Finished (fst d'') y) (snd d'') <-> exec_trace (fst d) (snd d) (p T rx) (Finished (fst d'') y) (snd d'').

Definition computes_to_notrace A (p : forall T, (A -> prog T) -> prog T) (d d' : memory) (x : A) :=
  forall T (rx : A -> prog T) d'' (y : T),
    exec d' (rx x) (Finished d'' y) <-> exec d (p T rx) (Finished d'' y).

Lemma step_trace_equiv_1 : forall T d p d' p',
  @step T d p d' p' -> forall tr, exists tr', step_trace d tr p d' (tr' ++ tr) p'.
Proof.
  intros.
  destruct H; eexists; try solve [instantiate (1 := []); eauto]; try solve [instantiate (1 := [_]); simpl; eauto].
Qed.

Lemma step_trace_equiv_2 : forall T d p d' p' tr tr',
  step_trace d tr p d' (tr' ++ tr) p' -> @step T d p d' p'.
Proof.
  intros.
  repeat deex. destruct H; eauto.
Qed.

Hint Resolve step_trace_equiv_2.

Lemma step_trace_prepends : forall T d tr p d' tr' p',
  @step_trace T d tr p d' tr' p' -> exists tr0, tr' = tr0 ++ tr.
Proof.
  intros.
  destruct H; eexists.
  + instantiate (1 := []); reflexivity.
  + instantiate (1 := [_]); reflexivity.
Qed.

Lemma exec_trace_prepends : forall T d tr p tr' out,
  @exec_trace T d tr p out tr' -> exists tr0, tr' = tr0 ++ tr.
Proof.
  intros.
  induction H; try solve [ exists []; trivial ].
  apply_in_hyp step_trace_prepends. repeat deex. eexists. apply app_assoc.
Qed.


Lemma step_trace_append : forall T d tr p d' tr' p' tr0,
  @step_trace T d tr p d' tr' p' -> step_trace d (tr ++ tr0) p d' (tr' ++ tr0) p'.
Proof.
  intros.
  destruct H; eauto.
  econstructor.
Qed.

Hint Resolve step_trace_append.

Lemma exec_trace_append : forall T d tr p tr' out tr0,
  @exec_trace T d tr p out tr' -> exec_trace d (tr ++ tr0) p out (tr' ++ tr0).
Proof.
  intros.
  induction H; eauto.
  econstructor. eapply step_trace_append; eauto. eauto.
Qed.

Hint Resolve exec_trace_append.

Lemma exec_trace_equiv_1 : forall T d p out,
  @exec T d p out -> forall tr, exists tr', exec_trace d tr p out (tr' ++ tr).
Proof.
  intros. revert tr.
  induction H; try solve [ exists []; eauto].
  intro.
  apply_in_hyp step_trace_equiv_1.
  deex. specialize (IHexec tr'). deex. eauto.
Qed.

Lemma exec_trace_equiv_2 : forall T d p out tr tr',
  exec_trace d tr p out (tr' ++ tr) -> @exec T d p out.
Proof.
  intros.
  repeat deex.
  induction H; eauto.
  econstructor; eauto.
  assert (H2 := H).
  apply_in_hyp step_trace_prepends.
  repeat deex. eauto.
Qed.

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

Definition sel T m := fun k => find k m : option T.

Section EnvSection.

  Variable env : Env.

  Inductive RunsTo : Stmt -> State -> State -> Prop :=
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
      can_alias v = true ->
      st' = add x v st ->
      RunsTo (Assign x e) st st'
  | RunsToCallAx : forall x f args st spec input output ret,
      StringMap.find f env = Some spec ->
      mapM (sel st) args = Some input ->
      mapsto_can_alias x st = true ->
      PreCond spec input ->
      length input = length output ->
      PostCond spec (List.combine input output) ret ->
      let st' := add_remove_many args input output st in
      let st' := add x ret st' in
      RunsTo (Call x f args) st st'.

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
        is_true st cond ->
        Safe t st ->
        Safe (If cond t f) st
  | SafeIfFalse :
      forall cond t f st,
        is_false st cond ->
        Safe f st ->
        Safe (If cond t f) st
  | SafeWhileTrue :
      forall cond body st,
        let loop := While cond body in
        is_true st cond ->
        Safe body st ->
        (forall st',
           RunsTo body st st' -> Safe loop st') ->
        Safe loop st
  | SafeWhileFalse :
      forall cond body st,
        let loop := While cond body in
        is_false st cond ->
        Safe loop st
  | SafeAssign :
      forall x e st w,
        eval st e = Some (SCA w) ->
        mapsto_can_alias x st = true ->
        Safe (Assign x e) st
  | SafeCallAx :
      forall x f args st spec input,
        StringMap.find f env = Some spec ->
        mapM (sel st) args = Some input ->
        mapsto_can_alias x st = true ->
        PreCond spec input ->
        Safe (Call x f args) st.

  Section Safe_coind.

    Variable R : Stmt -> State -> Prop.

    Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', RunsTo a st st' -> R b st'.

    Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true st cond /\ R t st) \/ (is_false st cond /\ R f st).

    Hypothesis WhileCase :
      forall cond body st,
        let loop := While cond body in
        R loop st ->
        (is_true st cond /\ R body st /\ (forall st', RunsTo body st st' -> R loop st')) \/
        (is_false st cond).

    Hypothesis AssignCase :
      forall x e st,
        R (Assign x e) st ->
        mapsto_can_alias x st = true /\
        exists w, eval st e = Some (SCA w).

    Hypothesis CallCase :
      forall x f args st,
        R (Call x f args) st ->
        mapsto_can_alias x st = true /\
        exists input,
          mapM (sel st) args = Some input /\
          ((exists spec,
              StringMap.find f env = Some spec /\
              PreCond spec input)).

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

End EnvSection.

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
    (* Safe ... /\ *) (* TODO this is important! *)
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
                   | [ H : _ * _ |- _ ] => destruct H
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
  destruct d, d'.
  simpl in *.
  congruence.
Qed.

Lemma ret_computes_to_refl : forall A (x : A) d, computes_to (ret x) d d x.
Proof.
  split; eauto.
Qed.

Hint Resolve ret_computes_to_refl.

Lemma CompileSeq :
  forall (tenv1 tenv1' tenv2: Telescope) env p1 p2,
    {{ tenv1 }}
      p1
    {{ tenv1' }} // env ->
    {{ tenv1' }}
      p2
    {{ tenv2 }} // env ->
    {{ tenv1 }}
      (Seq p1 p2)
    {{ tenv2 }} // env.
Proof.
  unfold ProgOk.
  intros.
  invert H2.
  eauto.
Qed.

Local Open Scope string_scope.


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
      args = (wrap d, Some (wrap (upd a v (fst d), (a, v) :: snd d))) :: (wrap a, None) :: (wrap v, None) :: nil
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
  (* TODO: when I pass wrong # of arguments, this just becomes trivially provable. Need to prove Safe too! *)
  instantiate (1 := (Call "_" "write" ["disk"; "a"; "v"])%facade).
  intro. intros.
  invert H0.
  simpl in *.
  maps.
  compute in H4.
  invert H4.
  unfold sel in *.
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
  destruct d3, d2.
  simpl in *.
  invert H7.
  subst st'.
  maps.
  do 2 eexists; intuition.
  econstructor; simpl.
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

Example micro_write_and_ret : sigT (fun p => forall d0 a v,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "a") d0 (ret a) ; SItemRet (NTSome "v") d0 (ret v) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (fun T rx => @Write T a v (fun _ => rx (a + v))) ;
       SItemRet (NTSome "out") d0 (fun T rx => @Write T a v (fun _ => rx (a + v))) ] }} // disk_env).
Proof.
  eexists.
  intros.
  instantiate (1 := (Call "_" "write" ["disk"; "a"; "v"]; "out" <- Var "a" + Var "v")%facade).
  intro. intros.
  invert H0.
  invert H3.
  invert H6.
  simpl in *.
  maps.
  compute in H4.
  invert H4.
  unfold sel in *.
  simpl in *.
  repeat match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; subst
  end.
  do 3 (destruct output; try discriminate).
  invert H0.
  simpl in *.
  subst st'0.
  maps.
  destruct (find "disk" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "a" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "v" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct H. destruct H0. destruct H1. repeat match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; subst
  end.
  repeat match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end.
  repeat match goal with
  | [ H : computes_to _ _ _ _ |- _ ] =>
      let H' := fresh H in
      assert (H' := H); apply ret_computes_to in H; apply ret_computes_to_disk in H'; subst
  end.
  invert H5.
  simpl in *.
  invert H2.
  intuition idtac.
  do 2 eexists; intuition.
  destruct d.
  econstructor.
  econstructor.
  econstructor.
  eauto.
  intro.
  invert H.
  invert H0.
  eauto.
  do 2 eexists; intuition.
  destruct d.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  instantiate (d := (upd a0 v1 (fst d), (a0, v1) :: (snd d))).
  eauto.
  intro.
  invert H.
  invert H0.
  eauto.
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
