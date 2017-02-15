Require Import FunctionalExtensionality ProofIrrelevance.
Require Import Nat PeanoNat List Structures.OrderedTypeEx.
Require Import RelationClasses Morphisms.
Require Import Rounding.
Require Import Omega VerdiTactics GoTactics1.
Require Import GoSemantics.
Require Import Word Bytes Prog ProgMonad Pred AsyncDisk.
Require Import String.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Class GoWrapper (WrappedType: Type) :=
  {
    wrap_type: Go.type;
    wrap':     WrappedType -> Go.type_denote wrap_type;
    wrap_inj:  forall a1 a2, wrap' a1 = wrap' a2 -> a1 = a2;
  }.

Definition wrap T {Wr: GoWrapper T} (t : T) : Go.value := Go.Val wrap_type (wrap' t).

Definition pred := @Pred.pred Go.var Nat.eq_dec Go.value.

Notation "k ~> v" := (k |-> (wrap v))%pred (at level 35) : pred_scope.

Definition mem_of := ((fun m k => VarMap.find k m) : Go.locals -> @Mem.mem Go.var Nat.eq_dec Go.value).

Notation "m ≲ p" := (mem_of m ## p) (at level 70).


Notation "k ~>? T" := (exists val, k |-> Go.Val (@wrap_type T _) val)%pred (at level 35) : pred_scope.

Definition ProgOk T env eprog (sprog : prog T) (initial_tstate : pred) (final_tstate : T -> pred) :=
  forall initial_state hm,
    (snd initial_state) ≲ initial_tstate ->
    forall out,
      Go.exec env (initial_state, eprog) out ->
    (forall final_state, out = Go.Finished final_state ->
      exists r hm',
        exec (fst initial_state) hm sprog (Finished (fst final_state) hm' r) /\
        (snd final_state ≲ final_tstate r)) /\
    (forall final_disk,
      out = Go.Crashed final_disk ->
      exists hm',
        exec (fst initial_state) hm sprog (Crashed T final_disk hm')) /\
    (out = Go.Failed ->
      exec (fst initial_state) hm sprog (Failed T)).

Notation "'EXTRACT' SP {{ A }} EP {{ B }} // EV" :=
  (ProgOk EV EP%go SP A%pred B%pred)
    (at level 60, format "'[v' 'EXTRACT'  SP '/' '{{'  A  '}}' '/'    EP '/' '{{'  B  '}}'  //  EV ']'").


Create HintDb gowrapper discriminated.

Hint Resolve wrap_inj : gowrapper.

Lemma eq_rect_inj : forall A x P p1 p2 y e,
    @eq_rect A x P p1 y e = @eq_rect A x P p2 y e -> p1 = p2.
Proof.
  unfold eq_rect; intros.
  destruct e.
  auto.
Qed.


Lemma valu2bytes_inj : forall a b,
    valu2bytes a = valu2bytes b -> a = b.
Proof.
  intros.
  eapply eq_rect_inj.
  eassumption.
Qed.
Hint Resolve valu2bytes_inj : gowrapper.


Ltac GoWrapper_finish :=
  solve [simpl; (f_equal + idtac); eauto using inj_pair2 with gowrapper].

Ltac GoWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | _ => progress (repeat find_inversion_safe)
                   | [ H : unit |- _ ] => destruct H
                   | [ H : _ * _ |- _ ] => destruct H
                   | _ => GoWrapper_finish
                   end).

Instance GoWrapper_Num : GoWrapper W.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.Num |}; GoWrapper_t.
Defined.

Instance GoWrapper_Bool : GoWrapper bool.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.Bool |}; GoWrapper_t.
Defined.

Instance GoWrapper_String : GoWrapper string.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.String |}; GoWrapper_t.
Defined.

Instance GoWrapper_valu : GoWrapper valu.
Proof.
  refine {| wrap' := fun v => Go.Here (existT _ _ v);
            wrap_type := Go.DiskBlock |}; GoWrapper_t.
Defined.

Create HintDb divisible discriminated.

Hint Resolve Nat.mod_divide Nat.mod_divides Nat.divide_add_r : divisible.

Lemma mul_divides : forall a b c,
    a * b = c -> Nat.divide b c.
Proof.
  intros.
  rewrite <- H.
  apply Nat.divide_mul_r.
  apply Nat.divide_refl.
Qed.
Hint Resolve mul_divides : divisible.

Lemma mod_divide_1 : forall a b,
    b <> 0 ->
    Nat.divide b a -> a mod b = 0.
Proof.
  intros. apply Nat.mod_divide; auto.
Qed.
Hint Resolve mod_divide_1 : divisible.

Instance GoWrapper_word nbits : GoWrapper (word nbits).
Proof.
  refine {| wrap' := fun v => Go.Here (existT _ _ v);
            wrap_type := Go.Buffer |}; GoWrapper_t.
Defined.

Definition immut_word := word.
Typeclasses Opaque immut_word.

Instance GoWrapper_immut_word nbits : GoWrapper (immut_word nbits).
Proof.
  refine {| wrap' := existT _ _;
            wrap_type := Go.ImmutableBuffer |}; GoWrapper_t.
Defined.


Instance GoWrapper_unit : GoWrapper unit.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.Struct nil |}; GoWrapper_t.
Defined.

Instance GoWrapper_pair {A B} {WA : GoWrapper A} {WB : GoWrapper B} : GoWrapper (A * B).
Proof.
  refine {| wrap' := fun p => (wrap' (fst p), wrap' (snd p));
            wrap_type := Go.Pair (@wrap_type _ WA) (@wrap_type _ WB) |}; GoWrapper_t.
Defined.

Lemma map_inj_inj :
  forall A B (f : A -> B),
    (forall a1 a2, f a1 = f a2 -> a1 = a2) ->
    forall as1 as2,
      map f as1 = map f as2 ->
      as1 = as2.
Proof.
  induction as1; intros; destruct as2; simpl in *; try discriminate; auto.
  find_inversion.
  f_equal; eauto.
Qed.
Hint Resolve map_inj_inj : gowrapper.

Instance GoWrapper_list T {Wr: GoWrapper T} : GoWrapper (list T).
Proof.
  refine {| wrap' := fun l => Go.Here (map wrap' l);
            wrap_type := Go.Slice wrap_type |}; GoWrapper_t.
Defined.

Instance GoWrapper_option {A} {WA : GoWrapper A} : GoWrapper (option A).
Proof.
  refine {| wrap' := fun o => match o with
                              | None => (false, Go.default_value' _)
                              | Some x => (true, wrap' x) end;
            wrap_type := Go.Pair Go.Bool (@wrap_type _ WA)|}.
  intros a b H.
  destruct a, b; invc H; GoWrapper_t.
Defined.

Instance GoWrapper_addrmap {T} {WT : GoWrapper T} : GoWrapper (Go.Map.t T).
Proof.
  refine {| wrap_type := Go.AddrMap (@wrap_type _ WT);
            wrap' := fun m => Go.Here (Go.Map.map (@wrap' _ WT) m) |}.
  intros.
  apply MapUtils.addrmap_equal_eq.
  pose proof (MapUtils.AddrMap.MapFacts.Equal_refl
    (Go.Map.map wrap' a1)) as H0.
  find_inversion_go. rewrite H in H0 at 2.
  eapply MoreAddrMapFacts.map_inj_equal; eauto.
  exact (@wrap_inj _ WT).
Defined.

Instance GoWrapper_type_denote_wrap_type {t} : GoWrapper (Go.type_denote t).
Proof.
  case_eq t; intros;
  match goal with
  | [ H: t = ?tt |- _ ] =>
    refine {| wrap' := id; wrap_type := tt |};
    unfold id; auto
  end.
Defined.

Class DefaultValue T {Wrapper : GoWrapper T} :=
  {
    zeroval : T;
    default_zero : wrap zeroval = Go.default_value wrap_type;
  }.

Arguments DefaultValue T {Wrapper}.

Instance num_default_value : DefaultValue nat := {| zeroval := 0 |}. auto. Defined.

Lemma word2bytes_zero : forall nbits nbytes e,
    @word2bytes nbits nbytes e $0 = $0.
Proof.
  intros.
  unfold word2bytes.
  rewrite e.
  reflexivity.
Qed.

Instance bool_default_value : DefaultValue bool := {| zeroval := false |}. auto. Defined.
Instance emptystruct_default_value : DefaultValue unit := {| zeroval := tt |}. auto. Defined.

Instance option_default_value T {H : GoWrapper T} : DefaultValue (option T) := {| zeroval := None |}. auto. Defined.

Import Go ListNotations.

Lemma default_zero' :
  forall T {W : GoWrapper T} v,
    wrap v = default_value wrap_type -> wrap' v = default_value' wrap_type.
Proof.
  unfold wrap, default_value; intros.
  eauto using value_inj.
Qed.

Instance pair_default_value A B {Wa : GoWrapper A} {Wb : GoWrapper B}
  {Da : DefaultValue A} {Db : DefaultValue B} : DefaultValue (A * B) := {| zeroval := (zeroval, zeroval) |}.
  destruct Da, Db. unfold wrap; simpl. repeat find_apply_lem_hyp default_zero'.
  repeat find_rewrite. reflexivity.
Defined.

Instance list_default_value A {W : GoWrapper A} : DefaultValue (list A) := {| zeroval := [] |}. auto. Defined.
Instance immut_word_default_value nbits : DefaultValue (immut_word nbits) := {| zeroval := $0 |}. auto. Defined.

Class WrapByTransforming T := {
  T' : Type;
  WrT' : GoWrapper T';
  transform : T -> T';
  transform_inj : forall t1 t2 : T, transform t1 = transform t2 -> t1 = t2;
}.

Instance GoWrapper_transform T {Tr : WrapByTransforming T} : GoWrapper T.
  refine {| wrap_type := wrap_type;
            wrap' := fun t => @wrap' _ (@WrT' _ Tr) (@transform _ Tr t) |}.
  intros.
  apply wrap_inj in H.
  auto using transform_inj.
Defined.


Theorem transform_pimpl : forall T {Tr : WrapByTransforming T} k (t : T),
  (k |-> (@wrap _ (@GoWrapper_transform _ Tr) t) : pred) <=p=> k |-> (@wrap _ WrT' (transform t)).
Proof.
  intros.
  reflexivity.
Qed.

Instance transform_dec {P Q} : WrapByTransforming ({P} + {Q}) :=
  { T' := bool }.
  - intros. destruct H; [ exact true | exact false ].
  - intros. destruct t1, t2; f_equal; try discriminate; apply proof_irrelevance.
Defined.

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
  setoid_rewrite <- H.
  auto.
Qed.


Module VarMapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(VarMap).

Theorem add_upd :
  forall m k v,
    mem_of (VarMap.add k v m) = Mem.upd (mem_of m) k v.
Proof.
  intros.
  extensionality k0.
  unfold mem_of, Mem.upd.
  rewrite VarMapFacts.add_o.
  repeat break_match; congruence.
Qed.

Theorem remove_delete :
  forall m k,
    mem_of (VarMap.remove k m) = Mem.delete (mem_of m) k.
Proof.
  intros.
  extensionality k0.
  unfold mem_of, Mem.delete.
  rewrite VarMapFacts.remove_o.
  repeat break_match; congruence.
Qed.

Fact sep_star_ptsto_some_find : forall l var val A,
  l ≲ (var |-> val * A) -> VarMap.find var l = Some val.
Proof.
  intros.
  find_eapply_lem_hyp sep_star_ptsto_some.
  eauto.
Qed.

Hint Resolve sep_star_ptsto_some_find. (* TODO hintdb *)

Inductive Declaration :=
| Decl (T : Type) {Wr: GoWrapper T}.

Arguments Decl T {Wr}.

Fixpoint nth_var {n} m : n_tuple n var -> var :=
  match n with
  | 0 => fun _ => 0
  | S n' =>
    match m with
    | 0 => fun t => fst t
    | S m' => fun t => nth_var m' (snd t)
    end
  end.

Definition decls_pre (decls : list Declaration) {n} (vars : n_tuple n var) : nat -> pred.
  induction decls; intro m.
  - exact emp.
  - destruct a.
    exact ((nth_var m vars ~>? T * IHdecls (S m))%pred).
Defined.

Lemma decls_pre_shift : forall decls n vars var0 m,
  @decls_pre decls (S n) (var0, vars) (S m) <=p=> @decls_pre decls n vars m.
Proof.
  induction decls.
  - reflexivity.
  - intros. destruct a. simpl.
    rewrite IHdecls.
    reflexivity.
Qed.

Definition decls_post (decls : list Declaration) {n} (vars : n_tuple n var) : nat -> pred.
  induction decls; intro m.
  - exact emp.
  - destruct a.
    exact ((exists x, nth_var m vars |-> Val wrap_type x) * IHdecls (S m))%pred.
Defined.

Lemma decls_post_shift : forall decls n vars var0 m,
  @decls_post decls (S n) (var0, vars) (S m) <=p=> @decls_post decls n vars m.
Proof.
  induction decls.
  - reflexivity.
  - intros. destruct a. simpl.
    Check pimpl_sep_star.
    rewrite IHdecls.
    reflexivity.
Qed.


Lemma decls_pre_impl_post :
  forall n decls vars m,
    @decls_pre decls n vars m =p=> decls_post decls vars m.
Proof.
  induction decls; intros.
  - auto.
  - destruct a.
    simpl.
    rewrite IHdecls.
    reflexivity.
Qed.

Record WrappedType :=
  {
    WrType : Type;
    Wrapper : GoWrapper WrType;
  }.

Definition with_wrapper T {Wr : GoWrapper T} := {| WrType := T |}.
Arguments with_wrapper T {Wr}.

Instance WrapWrappedType (wt : WrappedType) : GoWrapper wt.(WrType).
destruct wt.
assumption.
Defined.

Fixpoint arg_tuple (args : list WrappedType) : Type :=
  match args with
  | [] => unit
  | arg :: args' => (arg.(WrType) * arg_tuple args')%type
  end.

Fixpoint argval_foralls (args : list WrappedType) :
  forall (B : arg_tuple args -> Prop), Prop :=
  match args return forall (B : arg_tuple args -> Prop), Prop with
  | [] => fun B => B tt
  | arg :: args' => fun B => forall argval : arg.(WrType), argval_foralls args' (fun argvals' => B (argval, argvals'))
  end.

Theorem argval_inst : forall (args : list WrappedType) (B : arg_tuple args -> Prop),
    argval_foralls args B -> forall argvals : arg_tuple args, B argvals.
Proof.
  induction args; simpl; intros.
  - destruct argvals. auto.
  - destruct argvals.
    specialize (IHargs (fun argvals' => B (w, argvals')) (H w)).
    auto.
Qed.

Theorem argval_inst' : forall (args : list WrappedType) (B : arg_tuple args -> Prop),
    (forall argvals : arg_tuple args, B argvals) -> argval_foralls args B.
Proof.
  induction args; simpl; auto.
Qed.

Fixpoint args_pre args : forall (argvars : n_tuple (List.length args) var) (argvals : arg_tuple args), pred :=
  match args return forall (argvars : n_tuple (List.length args) var) (argvals : arg_tuple args), pred with
  | [] => fun _ _ => emp
  | arg :: args' => fun argvars argvals =>
                     let '(argvar, argvars') := argvars in
                     let '(argval, argvals') := argvals in
                     (argvar ~> argval * args_pre args' argvars' argvals')%pred
  end.

Fixpoint args_post args : forall (argvars : n_tuple (List.length args) var) (argvals : arg_tuple args), pred :=
  match args return forall (argvars : n_tuple (List.length args) var) (argvals : arg_tuple args), pred with
  | [] => fun _ _ => emp
  | arg :: args' => fun argvars argvals =>
                     let '(argvar, argvars') := argvars in
                     let '(argval, argvals') := argvals in
                     (argvar |-> moved_value (wrap argval) * args_post args' argvars' argvals')%pred
  end.