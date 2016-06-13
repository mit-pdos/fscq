Require Import PeanoNat String List FMapAVL.
Require Import Relation_Operators Operators_Properties.
Require Import VerdiTactics.
Require Import StringMap.
Require Import Mem AsyncDisk PredCrash.

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

Section Prog.

  Inductive prog : Type -> Type :=
    | Ret T (v: T) : prog T
    | Read (a: addr) : prog valu
    | Write (a: addr) (v: valu) : prog unit
    | Sync : prog unit
    | Bind T T' (p1: prog T) (p2: T -> prog T') : prog T'.

  Arguments Ret {T} v.

  Inductive outcome (T : Type) :=
    | Failed
    | Finished (m: rawdisk) (hm: hashmap) (v: T)
    | Crashed (m: rawdisk) (hm: hashmap).

  Inductive step : forall T,
      rawdisk -> hashmap -> prog T ->
      rawdisk -> hashmap -> T -> Prop :=
  | StepRead : forall m a v x hm,
      m a = Some (v, x) ->
      step m hm (Read a) m hm v
  | StepWrite : forall m a v v0 x hm,
      m a = Some (v0, x) ->
      step m hm (Write a v) (upd m a (v, v0 :: x)) hm tt
  | StepSync : forall m hm,
      step m hm (Sync) (sync_mem m) hm tt.

  Inductive fail_step : forall T,
      rawdisk -> prog T -> Prop :=
  | FailRead : forall m a,
      m a = None ->
      fail_step m (Read a)
  | FailWrite : forall m a v,
      m a = None ->
      fail_step m (Write a v).

  Inductive crash_step : forall T, prog T -> Prop :=
  | CrashRead : forall a,
      crash_step (Read a)
  | CrashWrite : forall a v,
      crash_step (Write a v).

  Inductive exec : forall T, rawdisk -> hashmap -> prog T -> outcome T -> Prop :=
  | XRet : forall T m hm (v: T),
      exec m hm (Ret v) (Finished m hm v)
  | XStep : forall T m hm (p: prog T) m' m'' hm' v,
      possible_sync m m' ->
      step m' hm p m'' hm' v ->
      exec m hm p (Finished m'' hm' v)
  | XBindFinish : forall m hm T (p1: prog T) m' hm' (v: T)
                    T' (p2: T -> prog T') out,
      exec m hm p1 (Finished m' hm' v) ->
      exec m' hm' (p2 v) out ->
      exec m hm (Bind p1 p2) out
  | XBindFail : forall m hm T (p1: prog T)
                  T' (p2: T -> prog T'),
      exec m hm p1 (Failed T) ->
      (* note p2 need not execute at all if p1 fails, a form of lazy
      evaluation *)
      exec m hm (Bind p1 p2) (Failed T')
  | XBindCrash : forall m hm T (p1: prog T) m' hm'
                   T' (p2: T -> prog T'),
      exec m hm p1 (Crashed T m' hm') ->
      exec m hm (Bind p1 p2) (Crashed T' m' hm')
  | XFail : forall m hm T (p: prog T),
      fail_step m p ->
      exec m hm p (Failed T)
  | XCrash : forall m hm T (p: prog T),
      crash_step p ->
      exec m hm p (Crashed T m hm).
End Prog.

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
| SCA : W -> Value.

Definition can_alias v :=
  match v with
  | SCA _ => true
  (* | ADT _ => false *)
  end.

Section Extracted.

  Definition State := (rawdisk * StringMap.t Value)%type.
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

  Fixpoint eval (st : StringMap.t Value) (e : Expr) : option Value :=
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
    PreCond (disk_in : rawdisk) (input : list Value) : Prop;
    PostCond (disk_in disk_out : rawdisk) (input_output : list (Value * option Value)) (ret : Value) : Prop;
    (* PreCondTypeConform : type_conforming PreCond *)
  }.

  Definition Env := StringMap.t AxiomaticSpec.

End Extracted.

Notation "R ^*" := (clos_refl_trans_1n _ R) (at level 0).

Section EnvSection.

  Import StringMap.

  Variable env : Env.

  Definition sel T m := fun k => find k m : option T.

  (* TODO: throw out RunsTo, I think *)
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
  | RunsToCallAx : forall x f args s spec d d' input output ret,
      StringMap.find f env = Some spec ->
      mapM (sel s) args = Some input ->
      PreCond spec d input ->
      length input = length output ->
      PostCond spec d d' (List.combine input output) ret ->
      let s' := add_remove_many args input output s in
      let s' := add x ret s' in
      RunsTo (Call x f args) (d, s) (d', s').

  Inductive Step : Stmt * State -> Stmt * State -> Prop :=
  | StepSeq1 : forall a a' b st st',
      Step (a, st) (a', st') ->
      Step (Seq a b, st) (Seq a' b, st')
  | StepSeq2 : forall a st,
      Step (Seq Skip a, st) (a, st)
  | StepIfTrue : forall cond t f st,
      is_true (snd st) cond ->
      Step (If cond t f, st) (t, st)
  | StepIfFalse : forall cond t f st,
      is_false (snd st) cond ->
      Step (If cond t f, st) (f, st)
  | StepWhileTrue : forall cond body st,
      let loop := While cond body in
      is_true (snd st) cond ->
      Step (loop, st) (Seq body loop, st)
  | StepWhileFalse : forall cond body st,
      let loop := While cond body in
      is_false (snd st) cond ->
      Step (loop, st) (Skip, st)
  | StepAssign : forall x e d s s' v,
      (* rhs can't be a mutable object, to prevent aliasing *)
      eval s e = Some v ->
      can_alias v = true ->
      s' = add x v s ->
      Step (Assign x e, (d, s)) (Skip, (d, s'))
  | StepCallAx : forall x f args s spec d d' input output ret,
      StringMap.find f env = Some spec ->
      mapM (sel s) args = Some input ->
      PreCond spec d input ->
      length input = length output ->
      PostCond spec d d' (List.combine input output) ret ->
      let s' := add_remove_many args input output s in
      let s' := add x ret s' in
      Step (Call x f args, (d, s)) (Skip, (d', s')).

  Inductive Outcome :=
  | EFailed
  | EFinished (st : State)
  | ECrashed (d : rawdisk).

  Inductive Exec : Stmt -> State -> Outcome -> Prop :=
  | EXStep : forall d p d' p' out,
    Step (p, d) (p', d') ->
    Exec p' d' out ->
    Exec p d out
  | EXFail : forall d p, (~exists d' p', Step (p, d) (p', d')) ->
    (p <> Skip) ->
    Exec p d EFailed
  | EXCrash : forall p d s, Exec p (d, s) (ECrashed d)
  | EXDone : forall d,
    Exec Skip d (EFinished d).

  Hint Constructors Exec RunsTo Step : steps.

  Hint Constructors clos_refl_trans_1n : steps.

  Lemma Step_Sequence : forall a b a' st st',
    Step^* (a, st) (a', st') ->
    Step^* (Seq a b, st) (Seq a' b, st').
  Proof.
    intros.
    prep_induction H; induction H; intros; subst.
    + find_inversion; eauto with steps.
    + destruct y. econstructor; try eapply StepSeq1; eauto.
  Qed.
  Hint Resolve Step_Sequence : steps.

  Hint Resolve clos_rt_rt1n clos_rt1n_rt : steps.
  Hint Extern 1 (clos_refl_trans _ _ ?x ?y) =>
    match goal with
    | _ => is_evar x; fail 1
    | _ => is_evar y; fail 1
    | _ => eapply rt_trans
    end : steps.


  Theorem RunsTo_Step : forall st p st',
    RunsTo p st st' ->
    Step^* (p, st) (Skip, st').
  Proof.
    intros.
    induction H; intros; subst_definitions; eauto 9 with steps;
      econstructor; do 2 eauto with steps.
  Qed.

  Ltac do_inv := match goal with
  | [ H : Step _ _ |- _ ] => invc H; eauto with steps
  | [ H : clos_refl_trans_1n _ _ _ _ |- _ ] => invc H; eauto with steps
  end.

  Lemma Step_RunsTo_Seq : forall a b st st',
    Step^* (Seq a b, st) (Skip, st')
    -> exists st0, Step^* (a, st) (Skip, st0) /\ Step^* (b, st0) (Skip, st').
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    destruct y. do_inv.
    destruct (IHclos_refl_trans_1n _ _ _ _ eq_refl eq_refl eq_refl).
    intuition eauto with steps.
  Qed.
  Hint Resolve Step_RunsTo_Seq : steps.

  (* Steps will look like: (StepWhileTrue StepSeq1* StepSeq2)* StepWhileFalse *)
  Lemma Step_RunsTo_While : forall cond body,
    (forall st st', Step^* (body, st) (Skip, st') -> RunsTo body st st')
    -> forall st st' p1, Step^* (p1, st) (Skip, st')
      -> (p1 = While cond body -> RunsTo (While cond body) st st')
      /\ (forall p', p1 = Seq p' (While cond body) -> exists st1, Step^* (p', st) (Skip, st1) /\ RunsTo (While cond body) st1 st').
  Proof.
    intros.
    prep_induction H0; induction H0; intuition; subst; repeat find_inversion.
    + do 3 do_inv.
      - destruct (IHclos_refl_trans_1n cond body ltac:(auto) _ _ _ eq_refl eq_refl eq_refl).
        destruct (H0 _ eq_refl). intuition eauto with steps.
      - destruct (IHclos_refl_trans_1n cond Skip ltac:(auto) _ _ _ eq_refl eq_refl eq_refl).
        destruct (H0 _ eq_refl). intuition eauto with steps.
    + do_inv.
      - destruct (IHclos_refl_trans_1n cond body ltac:(auto) _ _ _ eq_refl eq_refl eq_refl).
        destruct (H1 _ eq_refl).
        intuition eauto with steps.
      - destruct (IHclos_refl_trans_1n cond body ltac:(auto) _ _ _ eq_refl eq_refl eq_refl).
        intuition eauto with steps.
  Qed.

  Theorem Step_RunsTo : forall p st st',
    Step^* (p, st) (Skip, st') ->
    RunsTo p st st'.
  Proof.
    induction p; intros; subst.
    + repeat do_inv.
    + destruct (Step_RunsTo_Seq H); intuition eauto with steps.
    + repeat do_inv.
    + eapply Step_RunsTo_While; [ intros; eapply IHp | ..]; eauto.
    + repeat do_inv. subst_definitions. eauto with steps.
    + repeat do_inv.
  Qed.
  Hint Resolve Step_RunsTo.

  Theorem RunsTo_Exec : forall p st st',
    RunsTo p st st' ->
    Exec p st (EFinished st').
  Proof.
    intros.
    eapply RunsTo_Step in H.
    prep_induction H; induction H; intros; subst.
    + find_inversion. eauto with steps.
    + destruct y. eauto with steps.
  Qed.

  Theorem Exec_RunsTo : forall p st st',
    Exec p st (EFinished st') ->
    RunsTo p st st'.
  Proof.
    intros.
    eapply Step_RunsTo.
    prep_induction H; induction H; intros; subst; eauto with steps; try discriminate.
    find_inversion. eauto with steps.
  Qed.

  Theorem Steps_Exec : forall p st p' s' d',
    Step^* (p, st) (p', (d', s')) ->
    Exec p st (ECrashed d').
  Proof.
    intros.
    destruct st.
    prep_induction H; induction H; intros; subst.
    + repeat find_inversion. eauto with steps.
    + destruct y. destruct s0. eauto with steps.
  Qed.

  Theorem Exec_Steps : forall p st d',
    Exec p st (ECrashed d') ->
    exists p' s', Step^* (p, st) (p', (d', s')).
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + specialize (IHExec _ eq_refl). repeat deex. repeat eexists. econstructor; eauto.
    + find_inversion. eauto with steps.
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
  | SafeCallAx :
      forall x f args st spec input,
        StringMap.find f env = Some spec ->
        mapM (sel (snd st)) args = Some input ->
        PreCond spec (fst st) input ->
        Safe (Call x f args) st.

  Section Safe_coind.

    Variable R : Stmt -> State -> Prop.

    Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', RunsTo a st st' -> R b st'.

    Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true (snd st) cond /\ R t st) \/ (is_false (snd st) cond /\ R f st).

    Hypothesis WhileCase :
      forall cond body st,
        let loop := While cond body in
        R loop st ->
        (is_true (snd st) cond /\ R body st /\ (forall st', RunsTo body st st' -> R loop st')) \/
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

Inductive ScopeItem :=
| SItem A {H: FacadeWrapper Value A} (v : A).

(*
Notation "` k ->> v" := (SItemRet (NTSome k) v) (at level 50).
*)

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
  forall initial_state : State,
    (snd initial_state) \u2272 initial_tstate ->
    Safe env eprog initial_state /\
    forall out,
      Exec env eprog initial_state out ->
      (forall final_state,
        out = EFinished final_state ->
        exists r hm,
          exec (fst initial_state) hm sprog (Finished (fst final_state) hm r) /\
          (snd final_state) \u2272 (final_tstate r)) /\
      (forall final_disk,
        out = ECrashed final_disk ->
        exists hm,
          exec (fst initial_state) hm sprog (Crashed T final_disk hm)).

Notation "'EXTRACT' SP {{ A }} EP {{ B }} // EV" :=
  (ProgOk EV EP%facade SP A B)
    (at level 60, format "'[v' 'EXTRACT' SP '/' '{{'  A  '}}' '/'    EP '/' '{{'  B  '}}' // EV ']'").

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

Definition extract_code := projT1.

Ltac maps := rewrite ?StringMapFacts.remove_neq_o, ?StringMapFacts.add_neq_o, ?StringMapFacts.add_eq_o in * by congruence.

Local Open Scope string_scope.


Definition read : AxiomaticSpec.
  refine {|
    PreCond := fun args => exists (d : rawdisk) (a : addr),
      args = (wrap d) :: (wrap a) ::  nil;
    PostCond := fun args ret => exists (d : rawdisk) (a : addr),
      args = (wrap d, Some (wrap d)) :: (wrap a, None) :: nil /\
      ret = wrap (fst d a)
  |}.
Defined.

Definition write : AxiomaticSpec.
  refine {|
    PreCond := fun args => exists (d : rawdisk) (a : addr) (v : valu),
      args = (wrap d) :: (wrap a) :: (wrap v) :: nil;
    PostCond := fun args ret => exists (d : rawdisk) (a : addr) (v : valu),
      args = (wrap d, Some (wrap (upd a v (fst d), (a, v) :: snd d))) :: (wrap a, None) :: (wrap v, None) :: nil
  |}.
Defined.

Definition disk_env : Env := add "write" write (add "read" read (empty _)).

Ltac find_cases var st := case_eq (find var st); [
  let v := fresh "v" in
  let He := fresh "He" in
  intros v He; rewrite ?He in *
| let Hne := fresh "Hne" in
  intro Hne; rewrite Hne in *; exfalso; solve [ intuition idtac ] ].

Ltac invert_ret_computes_to :=
  repeat match goal with
  | [ H : computes_to _ _ _ _ |- _ ] =>
      let H' := fresh H in
      assert (H' := H); apply ret_computes_to in H; apply ret_computes_to_disk in H'; subst
  end.

Lemma computes_to_computes_to_crash : forall A p d d' r,
  @computes_to A p d d' r -> computes_to_crash p d d'.
Proof.
  unfold computes_to, computes_to_crash.
  intros.
  (* I believe this is not provable. *)
Abort.

Lemma computes_to_crash_refl : forall A p d,
  @computes_to_crash A p d d.
Proof.
  unfold computes_to_crash. eauto.
Qed.

Example micro_noop : sigT (fun p => forall d0,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }}
  {{ [ SItemDiskCrash (NTSome "disk") d0 (ret tt) ] }} // empty _).
Proof.
  eexists.
  intros.
  instantiate (1 := Skip).
  intro. intros.
  repeat split.
  econstructor.
  invc H0. simpl in H. find_cases "disk" crash_state. intuition. repeat deex. invert_ret_computes_to.
  eexists. intuition eauto using computes_to_crash_refl.
  invc H1. invc H0. simpl in *. intuition.
Defined.

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

Ltac invert_steps :=
  match goal with
  | [ H : Step _ _ _ |- _ ] => invc H
  | [ H : (Step _)^* _ _ |- _ ] => invc H
  end.

Ltac invert_runsto :=
  match goal with
  | [ H : RunsTo _ _ _ _ |- _ ] => invc H
  end.
Example micro_write : sigT (fun p => forall d0 a v,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "a") d0 (ret a) ; SItemRet (NTSome "v") d0 (ret v) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (fun T => @Write T a v) ] }} {{ [ SItemDiskCrash (NTSome "disk") d0 (fun T => @Write T a v) ] }} // disk_env).
Proof.
  eexists.
  intros.
  instantiate (1 := (Call "_" "write" ["disk"; "a"; "v"])%facade).
  intro. intros.
  simpl in *.
  maps.
  find_cases "disk" initial_state.
  find_cases "a" initial_state.
  find_cases "v" initial_state.
  intuition idtac.

  econstructor.
  unfold disk_env.
  maps. trivial.
  simpl. unfold sel. rewrite He, He0, He1. trivial.
  simpl. repeat deex. repeat eexists.

  repeat deex.
  invert_steps; invert_ret_computes_to. rewrite He. eexists; intuition auto using computes_to_crash_refl.

  invert_steps. invert_steps. maps. subst_definitions. invc H7. unfold sel in *. repeat find_rewrite. repeat find_inversion.
  do 3 (destruct output; try discriminate). unfold disk_env in *. maps. find_inversion. simpl in *.
  repeat deex. repeat find_inversion. maps. eexists; intuition.
  econstructor. econstructor. econstructor 3.

  invert_steps.

  invert_runsto. invc H8. repeat deex. unfold sel in *. rewrite He1 in *. rewrite He in *. rewrite He0 in *. repeat find_inversion.
  do 3 (destruct output; try discriminate).
  simpl in *.
  unfold disk_env in *. maps. find_inversion. simpl in *. repeat deex. repeat find_inversion.
  subst_definitions. maps.
  invert_ret_computes_to.
  do 2 eexists; intuition.
  econstructor; simpl.
  econstructor.
  econstructor.
  eauto.
  intro.
  invc H.
  invc H0.
  eauto.
Defined.

Example micro_inc : sigT (fun p => forall d0 x,
  {{ [ SItemRet (NTSome "x") d0 (ret x) ] }}
    p
  {{ [ SItemRet (NTSome "x") d0 (ret (1 + x)) ] }}
  {{ [] }} // empty _).
Proof.
  eexists.
  intros.
  instantiate (1 := ("x" <- Const 1 + Var "x")%facade).
  intro. intros.
  intuition. admit.
  simpl. auto.
  invc H0.
  maps.
  simpl in *.
  find_cases "x" initial_state.
  intuition.
  simpl in *.
  repeat deex.
  invc H3.
  invert_ret_computes_to.
  maps.
  eauto.
Admitted.

(*
Lemma CompileCompose :
  forall env var (f g : nat -> nat) p1 p2,
    (forall d0 x,
      {{ [ SItemRet (NTSome var) d0 (ret x) ] }}
        p1
      {{ [ SItemRet (NTSome var) d0 (ret (f x)) ] }} // env) ->
    (forall d0 y,
      {{ [ SItemRet (NTSome var) d0 (ret y) ] }}
        p2
      {{ [ SItemRet (NTSome var) d0 (ret (g y)) ] }} // env) ->
    forall d0 x,
      {{ [ SItemRet (NTSome var) d0 (ret x) ] }}
        (Seq p1 p2)
      {{ [ SItemRet (NTSome var) d0 (ret (g (f x))) ] }} // env.
Proof.
  intros.
  unfold ProgOk in *.
  intros.
  specialize (H d0 x initial_state H1).
  intuition.
  + econstructor. intuition. eapply H0. eauto.
  + invc H. eapply H0; eauto.
Qed.

Example micro_inc_two : sigT (fun p => forall d0 x,
  {{ [ SItemRet (NTSome "x") d0 (ret x) ] }}
    p
  {{ [ SItemRet (NTSome "x") d0 (ret (2 + x)) ] }}
  {{ [] }} // empty _).
Proof.
  eexists.
  intros.
  set (f := fun x => 1 + x).
  change (2 + x) with (f (f x)).
  eapply CompileCompose; eapply (projT2 micro_inc).
Qed.
*)

Ltac find_all_cases :=
  repeat match goal with
  | [ H : match find ?d ?v with | Some _ => _ | None => _ end |- _ ] => find_cases d v
  end.

Lemma CompileRead : forall A avar vvar pr (f : A -> nat) d0,
  avar <> "disk" ->
  vvar <> "disk" ->
  {{ [ SItemDisk (NTSome "disk") d0 pr; SItemRet (NTSome avar) d0 (pr |> f) ] }}
    Call vvar "read" ["disk"; avar]
  {{ [ SItemDisk (NTSome "disk") d0 (fun T rx => pr T (fun a => @Read T (f a) rx));
       SItemRet (NTSome vvar) d0 (fun T rx => pr T (fun a => @Read T (f a) rx)) ] }}
  {{ [ SItemDiskCrash (NTSome "disk") d0 (fun T rx => pr T (fun a => @Read T (f a) rx)) ] }} // disk_env.
Proof.
  unfold ProgOk.
  intros.
  intuition.
  simpl in *.
  maps.
  intuition.
  find_all_cases.
  econstructor.
  unfold disk_env. maps. trivial.
  unfold sel. simpl. rewrite He. rewrite He0. trivial.
  intuition. repeat deex.
  simpl. eauto.

  invert_steps. simpl in *. intuition. maps.
  find_all_cases. repeat deex. eexists; intuition.
  unfold computes_to, computes_to_crash in *.
  intros.
  (* Welp! This is unprovable. *)

  invert_runsto.
  simpl in *.
  unfold sel in *.
  maps.
  find_cases "disk" initial_state.
  find_cases avar initial_state.
  find_inversion.
  do 2 (destruct output; try discriminate).
  simpl in *.
  destruct H1 as [? [? _]].
  subst st'.
  unfold disk_env in *.
  maps.
  repeat find_inversion.
  repeat deex.
  unfold computes_to in *.
  repeat deex.
  simpl in *.
  repeat deex.
  repeat find_inversion.
  maps.
  repeat eexists; intros. eauto.
  simpl in *.
  repeat deex.
  repeat find_inversion.
  repeat eexists; intros. eapply H2.
  econstructor. econstructor. eapply H1.
  eauto.
  eapply H2 in H1.
  invc H1.
  invc H5.
  eauto.
  simpl in *.
  assert (Hc := H2).
  eapply computes_to_after in H2.
  pose proof (computes_to_det_ret H3 H2); subst.
  pose proof (computes_to_det_disk H3 H2); subst.
  unfold computes_to in *.
  repeat deex.
  repeat find_inversion.
  repeat eexists; intro.
  eapply Hc.
  econstructor. econstructor.
  eauto.
  eapply Hc in H1.
  invc H1. invc H5. eauto.
Qed.

Lemma CompileWrite : forall A avar vvar (af vf : A -> nat) pr d0,
  avar <> "disk" ->
  vvar <> "disk" ->
  avar <> vvar ->
  {{ [ SItemDisk (NTSome "disk") d0 pr; SItemRet (NTSome avar) d0 (pr |> af); SItemRet (NTSome vvar) d0 (pr |> vf)] }}
    Call "_" "write" ["disk"; avar; vvar]
  {{ [ SItemDisk (NTSome "disk") d0 (fun T rx => pr T (fun x => @Write T (af x) (vf x) rx))] }} // disk_env.
Proof.
  unfold ProgOk.
  intros.
  intuition.
  simpl in *.
  maps.
  find_cases "disk" initial_state.
  find_cases avar initial_state.
  find_cases vvar initial_state.
  econstructor.
  unfold disk_env. maps. trivial.
  unfold sel. simpl. rewrite He. rewrite He0. rewrite He1. trivial.
  intuition. repeat deex.
  simpl. eauto.
  invert_runsto.
  simpl in *.
  unfold sel in *.
  maps.
  find_cases "disk" initial_state.
  find_cases avar initial_state.
  find_cases vvar initial_state.
  find_inversion.
  do 3 (destruct output; try discriminate).
  simpl in *.
  destruct H2 as [? [? [? _]]].
  subst st'.
  unfold disk_env in *.
  maps.
  repeat find_inversion.
  repeat deex.
  assert (Hc := H3).
  eapply computes_to_after in Hc.
  pose proof (computes_to_det_disk Hc H5); subst.
  pose proof (computes_to_det_ret Hc H5); subst.
  assert (Hc' := H3).
  eapply computes_to_after in Hc'.
  pose proof (computes_to_det_disk Hc' H4); subst.
  pose proof (computes_to_det_ret Hc' H4); subst.
  unfold computes_to in *.
  repeat deex.
  simpl in *.
  repeat deex.
  repeat find_inversion.
  maps.
  repeat eexists; intros. simpl in *. eauto.
  eapply H3. eauto.
  eapply H3 in H2. invc H2. invc H7. eauto.
Qed.

Definition inc_disk_prog T rx : prog T := Read 0 (fun x => Write 0 x rx).

Example micro_inc_disk : sigT (fun p => forall d0,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 inc_disk_prog ] }} // disk_env).
Proof.
  unfold inc_disk_prog.
  eexists; intro.
  eapply CompileSeq.
  instantiate (Goal := ("a" <- Const 0; _)%facade).
  eapply CompileSeq.
  instantiate (tenv1'0 := [SItemDisk (NTSome "disk") d0 (ret tt); SItemRet (NTSome "a") d0 (ret 0)]).
  {
  intro. intros.
  simpl in *.
  find_cases "disk" initial_state.
  intuition; repeat deex.
  econstructor. simpl. trivial. trivial.
  invert_runsto.
  simpl in *. find_inversion.
  maps. rewrite He.
  invert_ret_computes_to.
  do 2 eexists. intuition.
  invert_runsto.
  simpl in *. find_inversion.
  maps.
  do 2 eexists. intuition.
  }
  change (ret 0) with (ret tt |> (fun x => 0)).
  eapply CompileRead. congruence. instantiate (1 := "v"). congruence.
  unfold inc_disk_prog. unfold ret.
  instantiate (Goal1 := ("a" <- Const 0; _)%facade).
  eapply CompileSeq.
  instantiate (tenv1' := [SItemDisk (NTSome "disk") d0 (fun T rx => Read 0 rx);
                          SItemRet (NTSome "a") d0 (fun T rx => Read 0 (fun _ => rx 0));
                          SItemRet (NTSome "v") d0 (fun T rx => Read 0 rx)]).
  {
  intro. intros.
  simpl in *. maps.
  find_cases "disk" initial_state.
  find_cases "v" initial_state.
  destruct H as [[? [? [? ?]]] [[? [? [? ?]]] _]]; subst.
  split.
  econstructor.
  simpl. trivial. trivial.
  intros. invert_runsto. maps. maps. rewrite He. rewrite He0.
  pose proof (computes_to_det_disk H H1); subst.
  pose proof (computes_to_det_ret H H1); subst.
  intuition; do 2 eexists; intuition eauto.
  eapply computes_to_after in H. eapply H. invc H4. trivial.
  }
  change (fun T rx => Read 0 (fun _ : valu => rx 0)) with ((fun T => @Read T 0) |> (fun _ => 0)).
  change (SItemRet (NTSome "v") d0 (fun T rx => Read 0 rx)) with (SItemRet (NTSome "v") d0 ((fun T => @Read T 0) |> (fun x => x))).
  eapply CompileWrite; congruence.
Qed.

(*
Lemma CompileBind : forall env (pr1 : forall T, (nat -> prog T) -> prog T) (pr2 : nat -> forall T, (nat -> prog T) -> prog T) v1 v2 p1 p2,
  (forall d0,
    {{ [SItemDisk (NTSome "disk") d0 pr1; SItemRet (N
  forall d0,
    {{ [SItemDisk (NTSome "disk") d0 pr1; SItemRet (NTSome v1) d0 pr1] }}
      (Seq p1 p2)
    {{ [SItemDisk (NTSome "disk") d0 (fun T rx => pr1 T (fun x => pr2 x T rx));
      SItemRet (NTSome v2) d0 (fun T rx => pr1 T (fun x => pr2 x T rx))] }} // env.
  Check CompileRead.

Example micro_plus : sigT (fun p => forall d0 x y,
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "x") d0 (ret x) ; SItemRet (NTSome "y") d0 (ret y) ] }}
    p
  {{ [ SItemDisk (NTSome "disk") d0 (ret tt) ; SItemRet (NTSome "out") d0 (ret (x + y)) ] }} // empty _).
Proof.
  eexists.
  intros.
  instantiate (1 := ("out" <- (Var "x" + Var "y"))%facade).
  intro. intros.
  invc H0.
  simpl in *.
  maps.
  destruct (find "disk" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "x" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  destruct (find "y" initial_state); [ | exfalso; solve [ intuition idtac ] ].
  intuition idtac.
  repeat deex.
  simpl in *.
  invc H3.
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
  invc H0.
  invc H3.
  invc H6.
  simpl in *.
  maps.
  compute in H4.
  invc H4.
  unfold sel in *.
  simpl in *.
  repeat match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; subst
  end.
  do 3 (destruct output; try discriminate).
  invc H0.
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
  invc H5.
  simpl in *.
  invc H2.
  intuition idtac.
  do 2 eexists; intuition.
  destruct d.
  econstructor.
  econstructor.
  econstructor.
  eauto.
  intro.
  invc H.
  invc H0.
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
  invc H.
  invc H0.
  eauto.
Defined.

*)
