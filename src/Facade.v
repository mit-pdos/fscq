Require Import PeanoNat String List FMapAVL.
Require Import Relation_Operators Operators_Properties.
Require Import VerdiTactics.
Require Import StringMap.
Require Import Mem AsyncDisk PredCrash Prog ProgMonad SepAuto.
Require Import Gensym.

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
      | Some (Num a), Some (Num b) => Some (Num (eval_binop op a b))
      | _, _ => None
    end.

  Fixpoint eval (st : StringMap.t Value) (e : Expr) : option Value :=
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

  Inductive CrashStep : Stmt -> Prop :=
  | CrashSeq1 : forall a b,
      CrashStep a ->
      CrashStep (Seq a b)
  | CrashCall : forall x f args,
      CrashStep (Call x f args).

  Inductive Exec : Stmt -> State -> Outcome -> Prop :=
  | EXStep : forall d p d' p' out,
    Step (p, d) (p', d') ->
    Exec p' d' out ->
    Exec p d out
  | EXFail : forall d p, (~exists d' p', Step (p, d) (p', d')) ->
    (p <> Skip) ->
    Exec p d EFailed
  | EXCrash : forall p d s,
    CrashStep p ->
    Exec p (d, s) (ECrashed d)
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

  Theorem Exec_Steps : forall p st d',
    Exec p st (ECrashed d') ->
    exists p' s', Step^* (p, st) (p', (d', s')) /\ CrashStep p'.
  Proof.
    intros.
    prep_induction H; induction H; intros; subst; try discriminate.
    + specialize (IHExec _ eq_refl). repeat deex. repeat eexists; eauto. econstructor; eauto.
    + find_inversion. eauto with steps.
  Qed.

  Theorem Steps_Exec : forall p st p' s' d',
    Step^* (p, st) (p', (d', s')) ->
    CrashStep p' ->
    Exec p st (ECrashed d').
  Proof.
    intros.
    destruct st.
    prep_induction H; induction H; intros; subst.
    + repeat find_inversion. eauto with steps.
    + destruct y. destruct s0. eauto with steps.
  Qed.

  CoInductive Safe : Stmt -> State -> Prop :=
  | SafeSkip : forall st, Safe Skip st
  | SafeSeq :
      forall a b st,
        Safe a st /\
        (forall st',
           Exec a st (EFinished st') -> Safe b st') ->
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
           Exec body st (EFinished st') -> Safe loop st') ->
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
      Exec env eprog initial_state (EFinished final_state) ->
      exists r hm',
        exec (fst initial_state) hm sprog (Finished (fst final_state) hm' r) /\
        (snd final_state) \u2272 (final_tstate r)) /\
    (forall final_disk,
      Exec env eprog initial_state (ECrashed final_disk) ->
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