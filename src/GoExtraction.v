Require Import Eqdep_dec.
Require Import PeanoNat String List.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import VerdiTactics.
Require Import Word Mem AsyncDisk Pred PredCrash Prog ProgMonad.
Require Import BasicProg.
Require Import Gensym.
Require Import Omega.
Require Import GoSemantics.
Require Import GoFacts GoHoare GoTactics2 GoCompilationLemmas GoSepAuto.

Import ListNotations.

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

Definition extract_code := projT1.


Local Open Scope pred.

Import Go.

Lemma source_stmt_many_declares: forall decls f,
  (forall vars, source_stmt (f vars)) ->
  source_stmt (many_declares decls f).
Proof.
  induction decls; intros.
  - simpl in *; eauto.
  - simpl.
    break_match. econstructor.
    eauto.
Defined.

Ltac source_stmt_step :=
  apply source_stmt_many_declares ||
  econstructor.

Ltac find_val v p :=
  match p with
    | context[?k ~> v] => constr:(Some k)
    (* TODO: more principled thing? *)
    | context[?k |-> Val _ (id v)] => constr:(Some k)
    | _ => constr:(@None var)
  end.

Ltac find_val_fn v p cont :=
  match p with
    | context[?k ~> v] => cont k
    | context[?k |-> Val _ (id v)] => cont k
  end.

Ltac var_mapping_to pred val :=
  lazymatch pred with
    | context[?var ~> val] => var
    | context[?var |-> Val _ (id val)] => var
  end.

Definition mark_ret (T : Type) := T.
Class find_ret {T} (P : pred) := FindRet : T.
Ltac find_ret_tac P :=
  match goal with
    | [ ret : mark_ret ?T |- _ ] => var_mapping_to P ret
  end.
Hint Extern 0 (@find_ret ?T ?P) => (let x := find_ret_tac P in exact x) : typeclass_instances.
Ltac var_mapping_to_ret :=
  lazymatch goal with
    | [ |- EXTRACT _ {{ _ }} _ {{ fun ret : ?T => ?P }} // _ ] =>
      lazymatch constr:(fun ret : mark_ret T => (_:find_ret P)) with
        | (fun ret => ?var) => var
      end
  end.

Ltac do_declare T cont :=
  lazymatch goal with
  | [ |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ ] =>
    let Pre := fresh "Pre" in
    set pre as Pre; simpl in Pre; subst Pre;
    lazymatch goal with
    | [ |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ ] =>
      lazymatch pre with
      | context [decls_pre ?decls ?vars ?m] =>
        let decls' := fresh "decls" in
        evar (decls' : list Declaration);
        unify decls (Decl T :: decls'); subst decls';
        cont (nth_var m vars)
      end
    end
  end.

Ltac do_duplicate x := match goal with
  |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ =>
    match find_val x pre with
    | Some ?svar =>
      eapply CompileBefore; [
        let T := type of x in
        do_declare T ltac:(fun v0 =>
          eapply hoare_weaken; [
            eapply CompileRet with (v := x) (var0 := v0) | cancel_go..];
              eapply hoare_weaken; [eapply CompileDup with (var0 := svar) (var' := v0) | cancel_go..]
        ) |]
    end
  end.

Ltac compile_bind := match goal with
  | [ |- EXTRACT Bind ?p (fun _ => ?q) {{ _ }} _ {{ _ }} // _ ] =>
    eapply CompileSeq
  | [ |- EXTRACT Bind (Ret ?x_) ?p {{ _ }} _ {{ ?post }} // _ ] =>
    match type of x_ with
    | ?T_ =>
      let Wr_ := constr:(ltac:(typeclasses eauto) : GoWrapper T_) in
      do_declare T_ ltac:(fun v_ =>
        eapply hoare_strengthen_pre; [
        | eapply CompileBindRet with (vara := v_) (a := x_)];
        [ cancel_go | ..])
    end
  | [ |- EXTRACT Bind ?p ?q {{ _ }} _ {{ ?post }} // _ ] =>
    match type of p with
    | prog ?T_ =>
      let v := fresh "var" in
      let Wr_ := constr:(ltac:(typeclasses eauto) : GoWrapper T_) in
      do_declare T_ ltac:(fun v_ =>
        simpl decls_pre; simpl decls_post;
        match goal with [ |- EXTRACT _ {{ _ }} _ {{ ?post' }} // _ ] =>
          simpl decls_post; simpl decls_pre;
          eapply hoare_strengthen_pre;
          [| eapply CompileBind with (var0 := v_)];
          [ cancel_go | intros .. ]
        end)
    end
  end.

Ltac compile_const := lazymatch goal with
  | [ |- EXTRACT Ret ?n {{ _ }} _ {{ _ }} // _] =>
    match goal with
    | [ x : _ |- _] =>
      lazymatch n with
      | context [x] => fail 1
      end
      | _ => idtac
    end;
      match var_mapping_to_ret with
      | ?x => eapply hoare_weaken;
        [eapply (@CompileConst _ _ _ _ x) | cancel_go..]
      end
  end.

Ltac is_transformable v :=
  let T := type of v in
  let wr := constr:(_ : WrapByTransforming T) in idtac.

Ltac transform_includes v term :=
  let y := constr:(transform v) in
  let x := ltac:(eval simpl in y) in
  match x with
  | context [term] => idtac
  end.

Ltac compile_ret :=
  match goal with
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; [ cancel_go ]
  | [ |- EXTRACT Ret ?x {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val x pre with
    | Some ?kx =>
      match var_mapping_to_ret with
      | ?kret => (unify kx kret; fail 2) ||
                                        eapply hoare_weaken; [
                  eapply CompileMove with (var0 := kx) (var' := kret)
                | cancel_go.. ]
      end
    end
  end.

Ltac compile_ret_transformable :=
  match goal with
  | [ |- EXTRACT Ret ?x {{ ?pre }} _ {{ _ }} // _ ] =>
    is_transformable x;
    let ret := var_mapping_to_ret in
    eapply hoare_weaken; [
      eapply CompileRet' with (var0 := ret);
      eapply hoare_weaken_post; [
        intros;
        let P := fresh "P" in
        match goal with
        | [ |- ?P_ =p=> _ ] => set P_ as P
        end; rewrite ?transform_pimpl; simpl; subst P;
        let Q := fresh "Q" in
        match goal with
        | [ |- ?e ?x =p=> ?Q_ ] =>
          set Q_ as Q;
          pattern x in Q;
          subst Q;
          reflexivity
        end
      | eapply CompileRet ] | cancel_go | cancel_go ]
  end.

Ltac compile_ret_transform_part :=
  match goal with
  | [ |- EXTRACT Ret ?x {{ ?pre }} _ {{ _ }} // _ ] =>
    match pre with
    | context [ (?k_ ~> ?v)%pred ] =>
      transform_includes v x;
      eapply hoare_strengthen_pre;
        [ rewrite ?transform_pimpl with (k := k_); simpl; reflexivity | ]
    end
  end.
Ltac compile_match := match goal with
  | [ |- EXTRACT match ?o with _ => _ end {{ ?pre }} _ {{ fun ret => ?post }} // _ ] =>
    match type of o with
    | option ?X =>
      match find_val o pre with
      | None =>
        eapply extract_equiv_prog with (pr1 := Bind (Ret o) (fun x => _));
        [ generalize o; intro; rewrite bind_left_id; apply prog_equiv_equivalence |]
      | Some ?x =>
        match var_mapping_to_ret with
        | ?ret =>
          do_declare bool ltac:(fun vara => simpl decls_pre; simpl decls_post;
            do_declare X ltac:(fun varb =>
              eapply hoare_weaken;
              [ eapply CompileMatchOption with
                  (ovar := x) (avar := vara) (bvar := varb) (xvar := ret) | cancel_go.. ];
              intros
            ))
        end
      end
    end
  | [|- EXTRACT (let (a_, b_) := ?p in _) {{ _ }} _ {{ _ }} // _ ] =>
    let H := fresh "H" in
    let a := fresh "p" in
    let b := fresh "p" in
    destruct p as [a  b] eqn:H;
    assert (a = fst p) by (subst p; eauto);
    assert (b = snd p) by (subst p; eauto);
    clear H; subst a b
  end.

Ltac compile_read_write := match goal with
  | [ |- EXTRACT Read ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
    | Some ?k =>
      eapply hoare_strengthen_pre; [| eapply hoare_weaken_post; [ |
        eapply CompileRead with (avar := k) (vvar := retvar) ] ]; [ cancel_go .. ]
    end
  | [ |- EXTRACT Write ?a ?v {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
    | Some ?ka =>
      match find_val v pre with
      | Some ?kv =>
        eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
          eapply CompileWrite with (avar := ka) (vvar := kv) ] ]; [ cancel_go .. ]
      end
    end
  | [ |- EXTRACT Sync {{ ?pre }} _ {{ _ }} // _ ] =>
    eapply CompileSync
  end.

Ltac compile_for := match goal with
  | [ |- EXTRACT ForN_ ?f ?i ?n _ _ ?t0 {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val n pre with
      | None => eapply extract_equiv_prog with (pr1 := Bind (Ret n) (fun x => ForN_ f i x _ _ t0));
          [> rewrite bind_left_id; eapply prog_equiv_equivalence | ]
      | Some ?kn =>
      match find_val i pre with
        | None => eapply extract_equiv_prog with (pr1 := Bind (Ret i) (fun x => ForN_ f x n _ _ t0));
          [> rewrite bind_left_id; eapply prog_equiv_equivalence | ]
        | Some ?ki =>
        match find_val t0 pre with
          | None => eapply extract_equiv_prog with (pr1 := Bind (Ret t0) (fun x => ForN_ f i n _ _ x));
            [> rewrite bind_left_id; eapply prog_equiv_equivalence | ]
          | Some ?kt0 =>
            eapply hoare_strengthen_pre; [>
            | eapply hoare_weaken_post; [>
            | eapply CompileFor with (v := ki) (loopvar := kt0) (vn := kn)] ];
            [> cancel_go | cancel_go | intros ]
        end
      end
    end
  end.

Ltac get_head E :=
  match E with
  | ?P _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ => constr:(P)
  | ?P _ _ _ => constr:(P)
  | ?P _ _ => constr:(P)
  | ?P _ => constr:(P)
  | ?P => constr:(P)
  end.

Ltac ensure_val_present val_ cont :=
  let T := type of val_ in
  lazymatch goal with
  |- EXTRACT _ {{ ?pre_ }} _ {{ _ }} // _ =>
    match find_val val_ pre_ with
    | Some ?k1 => cont k1
    | None => do_declare T ltac:(fun var =>
          eapply hoare_weaken; [
          eapply SetVarBefore with (val := val_) (var0 := var) | cancel_go..]
        )
    end
  end.

Ltac declare_and_get_args' expr argvars cont :=
  lazymatch expr with
  | ?rest ?arg => ensure_val_present arg ltac:(fun var_ => declare_and_get_args' rest (var_, argvars) cont)
  | ?f => cont argvars
  end.
  
Ltac declare_and_get_args expr cont :=
  declare_and_get_args' expr tt cont.

Ltac pattern_prog pat :=
  eapply extract_equiv_prog; [
    match goal with
    | [ |- ProgMonad.prog_equiv _ ?pr ] =>
      let Pr := fresh "Pr" in
      set pr as Pr;
      pattern pat in Pr;
      subst Pr;
      eapply bind_left_id
    end | ].

Ltac compile_call :=
  match goal with
  | [ H : prog_func_call_lemma ?sig ?name ?f ?env |- EXTRACT ?expr {{ ?pre }} _ {{ _ }} // ?env ] =>
    let hd := get_head expr in
    unify f hd;
    let retvar := var_mapping_to_ret in
    declare_and_get_args expr ltac:(
      fun argvars =>
        let F := fresh "F" in
        evar (F : pred);
        let F_ := eval unfold F in F in
            clear F; let H' := fresh "H" in
                     generalize H; intro H';
                     specialize (H' retvar argvars F_);
                     eapply hoare_weaken; [ apply H' | cancel_go.. ] )
  end.

Ltac compile_add := match goal with
  | [ |- EXTRACT Ret (S ?a) {{ ?pre }} _ {{ _ }} // _ ] =>
    rewrite <- (Nat.add_1_r a)
  | [ |- EXTRACT Ret (?a + ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken;
              [ (unify retvar ka; eapply CompileAddInPlace1 with (avar := ka) (bvar := kb)) ||
                (unify retvar kb; eapply CompileAddInPlace2 with (avar := ka) (bvar := kb)) ||
                eapply CompileAdd with (avar := ka) (bvar := kb) (sumvar := retvar) | .. ];
            [ cancel_go .. ]
        end
    end
  end.

Ltac compile_subtract := match goal with
  | [ |- EXTRACT Ret (?a - ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken;
              [ (unify retvar ka; eapply CompileSubtractInPlace1 with (avar := ka) (bvar := kb)) ||
                (unify retvar kb; eapply CompileSubtractInPlace2 with (avar := ka) (bvar := kb)) ||
                eapply CompileSubtract with (avar := ka) (bvar := kb) (sumvar := retvar) | .. ];
            [ cancel_go .. ]
        end
    end
  end.

Ltac compile_multiply := match goal with
  | [ |- EXTRACT Ret (?a * ?b)%nat {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken;
              [ (unify retvar ka; eapply CompileMultiplyInPlace1 with (avar := ka) (bvar := kb)) ||
                (unify retvar kb; eapply CompileMultiplyInPlace2 with (avar := ka) (bvar := kb)) ||
                eapply CompileMultiply with (avar := ka) (bvar := kb) (rvar := retvar) | .. ];
            [ cancel_go .. ]
        end
    end
  end.

Ltac compile_divide := match goal with
  | [ |- EXTRACT Ret (?a / ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken;
              [ (unify retvar ka; eapply CompileDivideInPlace1 with (avar := ka) (bvar := kb)) ||
                (unify retvar kb; eapply CompileDivideInPlace2 with (avar := ka) (bvar := kb)) ||
                eapply CompileDivide with (avar := ka) (bvar := kb) (rvar := retvar) | .. ];
            [ cancel_go .. ]
        end
    end
  end.

Ltac compile_mod := match goal with
  | [ |- EXTRACT Ret (?a mod ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken;
              [ (unify retvar ka; eapply CompileModInPlace1 with (avar := ka) (bvar := kb)) ||
                (unify retvar kb; eapply CompileModInPlace2 with (avar := ka) (bvar := kb)) ||
                eapply CompileMod with (avar := ka) (bvar := kb) (rvar := retvar) | .. ];
            [ cancel_go .. ]
        end
    end
  end.

Ltac compile_listop := match goal with
  | [ |- EXTRACT Ret (?x :: ?xs) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val x pre with
      | Some ?kx =>
        match var_mapping_to_ret with
          | ?kret =>
            match find_val xs pre with
              | Some ?kxs => (* ret var is tail var *)
                unify kret kxs;
                eapply hoare_weaken;
                [ eapply CompileAppend with (lvar := kxs) (vvar := kx)
                | cancel_go..]
              | Some ?kxs => (* ret var is not tail var *)
                eapply CompileBefore; [
                  eapply CompileRet with (v := xs) (var0 := kret);
                    simpl decls_pre |]
            end
        end
    end
  | [ |- EXTRACT (match ?l with
             | [] => _
             | x :: xs => _ end) {{ ?pre }} _ {{ ?post }} // _ ] =>
    match find_val l pre with
    | Some ?varl =>
      let Txs := type of l in
      match type of l with
      | list ?Tx =>
        do_declare bool ltac:(fun varc =>
          do_declare Tx ltac:(fun varx =>
            do_declare Txs ltac:(fun varxs =>
              eapply hoare_weaken; [
              eapply CompileUncons with (lvar := varl) (cvar := varc) (xvar := varx) (xsvar := varxs); intros |
              cancel_go..]
            )
          )
        )
      end
    | None =>
      pattern_prog l
    end
  end.

Ltac compile_map_op := match goal with
  | [ |- EXTRACT Ret (Map.find ?k ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    match find_val k pre with
    | Some ?vark =>
      match find_val m pre with
      | Some ?varm =>
        match var_mapping_to_ret with
        | ?ret =>
          eapply hoare_weaken; [
          eapply CompileMapFind with (mvar := varm) (kvar := vark) (vvar := ret) | cancel_go..]
        end
      end
    end
  | [ |- EXTRACT Ret (Map.cardinal ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    let retv := var_mapping_to_ret in
    match find_val m pre with
    | Some ?varm =>
      eapply hoare_weaken; [
        eapply CompileMapCardinal with (mvar := varm) (var0 := retv)
        | cancel_go..]
    end
  | [ |- EXTRACT Ret (Map.elements ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    let retv := var_mapping_to_ret in
    match find_val m pre with
    | Some ?varm =>
      eapply hoare_weaken; [
        eapply CompileMapElements with (mvar := varm) (var0 := retv)
        | cancel_go..]
    end
  | [ |- EXTRACT Ret (Map.add ?k ?v_ ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    let retv := var_mapping_to_ret in
    match find_val m pre with
    | Some ?varm => unify retv varm; (* same variable *)
      match find_val k pre with
      | Some ?vark =>
        match find_val v_ pre with
        | Some ?varv =>
          eapply hoare_weaken; [
          eapply CompileMapAdd with (kvar := vark) (vvar := varv) (mvar := varm) |
          cancel_go..]
        end
      end
    | Some ?varm => (* not the same variable *)
      (unify retv varm; fail 2) ||
      eapply extract_equiv_prog with (pr1 := Bind (Ret m) (fun m' => Ret (Map.add _ _ m'))); [
        rewrite bind_left_id; reflexivity |];
        eapply hoare_weaken; [
        eapply CompileBindRet with (vara := retv) | cancel_go..]
    end
  | [ |- EXTRACT Ret (Map.remove ?k ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    let retv := var_mapping_to_ret in
    match find_val m pre with
    | Some ?varm => unify retv varm; (* same variable *)
      match find_val k pre with
      | Some ?vark =>
        eapply hoare_weaken; [
        eapply CompileMapRemove with (kvar := vark) (mvar := varm) |
        cancel_go..]
      end
    | Some ?varm => (* not the same variable *)
      (unify retv varm; fail 2) ||
      eapply extract_equiv_prog with (pr1 := Bind (Ret m) (fun m' => Ret (Map.remove _ m'))); [
        rewrite bind_left_id; reflexivity |];
        eapply hoare_weaken; [
        eapply CompileBindRet with (vara := retv) | cancel_go..]
    end
  end.

Ltac in_pair v pair path :=
  match pair with
  | v => constr:(Some path)
  | (?a, ?b) =>
    match in_pair v a (fst path) with
    | Some ?x => constr:(Some x)
    | None =>
      match in_pair v b (snd path) with
      | Some ?x => constr:(Some x)
      | None => constr:(@None unit)
      end
    end
  | _ => constr:(@None unit)
  end.

Ltac find_pair_val v p :=
  match p with
  | context [?k ~> ?v0] =>
    match in_pair v v0 v0 with
    | Some ?x => constr:(Some (k, x))
    end
  | _ => constr:(@None unit)
  end.


Ltac compile_split := match goal with
  | [ |- EXTRACT Ret ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_pair_val a pre with
    | Some (_, ?ppath) =>
      change (Ret a) with (Ret ppath)
    end
  | [ |- EXTRACT Ret (fst ?p) {{ ?pre }} _ {{ _ }} // _ ] =>
    let avar_ := var_mapping_to_ret in
    match find_val p pre with
    | Some ?pvar_ =>
      let A_ := type of (fst p) in
      let B_ := type of (snd p) in
      match B_ with
      | unit => eapply hoare_weaken;
          [ eapply CompileSplitUnit with (avar := avar_) (pvar := pvar_)
          | cancel_go..]
      | _ =>
        do_declare B_ ltac:(fun bvar_ =>
          eapply hoare_weaken;
          [ eapply CompileFst with (A := A_) (B := B_) (avar := avar_) (bvar := bvar_) (pvar := pvar_)
          | cancel_go.. ])
      end
    end
  | [ |- EXTRACT Ret (snd ?p) {{ ?pre }} _ {{ _ }} // _ ] =>
    let bvar_ := var_mapping_to_ret in
    match find_val p pre with
    | Some ?pvar_ =>
      let A_ := type of (fst p) in
      let B_ := type of (snd p) in
      do_declare A_ ltac:(fun avar_ =>
        eapply hoare_weaken;
        [ eapply CompileSnd with (A := A_) (B := B_) (avar := avar_) (bvar := bvar_) (pvar := pvar_)
        | cancel_go.. ])
    end
  end.

Ltac compile_join := match goal with
  | [ |- EXTRACT Ret (?a_, ?b_) {{ ?pre }} _ {{ ?post }} // _ ] =>
    match find_val a_ pre with
    | None =>
      let A_ := type of a_ in
      eapply CompileBefore; [
        do_declare A_ ltac:(fun x_ =>
          eapply CompileRet with (v := a_) (var0 := x_);
          simpl decls_pre) |]
    | Some ?ka =>
      match var_mapping_to_ret with
      | ?kp =>
        let B_ := type of b_ in
        match B_ with
        | unit => eapply hoare_weaken;
          [ eapply CompileJoinUnit with (avar := ka) (pvar := kp)
          | cancel_go..]
        | _ =>
          match find_val b_ pre with
          | None =>
            eapply CompileBefore; [
              do_declare B_ ltac:(fun x_ =>
              eapply CompileRet with (v := b_) (var0 := x_);
              simpl decls_pre) |]
          | Some ?kb =>
              eapply hoare_weaken;
              [ apply CompileJoin with (avar := ka) (bvar := kb) (pvar := kp)
              | cancel_go..]
          end
        end
      end
    end
end.

Ltac compile_decompose := match goal with
  | [ |- EXTRACT Ret (?f ?a) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None => pattern_prog a
    end
   | [ |- EXTRACT Ret (?f ?a ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None => pattern_prog a
    end
   | [ |- EXTRACT Ret (?f ?a ?b ?c) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None => pattern_prog a
    end
  | [ |- EXTRACT ?f ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match f with
      | Ret => fail 2
      | _ => idtac
    end;
    match find_val a pre with
      | None => pattern_prog a
    end
  | [ |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // _ ] =>
    match f with
      | Ret => fail 2
      | _ => idtac
    end;
    match find_val a pre with
    | None => pattern_prog a
    end
  end.

Ltac compile_if :=
  unfold BasicProg.If_;
  match goal with
  | [|- EXTRACT (if Compare_dec.lt_dec ?a_ ?b_ then _ else _) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a_ pre with
    | None =>
      eapply extract_equiv_prog; [
        let arg := fresh "arg" in
        set (arg := if Compare_dec.lt_dec a_ b_ then _ else _);
        pattern a_ in arg; subst arg;
        eapply bind_left_id | ]
    | Some ?ka_ =>
      match find_val b_ pre with
      | None =>
      eapply extract_equiv_prog; [
        let arg := fresh "arg" in
        set (arg := if Compare_dec.lt_dec a_ b_ then _ else _);
        pattern b_ in arg; subst arg;
        eapply bind_left_id | ]
      | Some ?kb_ =>
        eapply hoare_weaken; [eapply CompileIfLt with (vara := ka_) (varb := kb_) |
                              cancel_go..]; simpl
      end
    end
  | [|- EXTRACT (if ?x_ then _ else _) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val x_ pre with
    | None =>
      eapply extract_equiv_prog with (pr1 := Bind (Ret x_) (fun x => if x then _ else _));
      [ rewrite bind_left_id; apply prog_equiv_equivalence |]
    | Some ?kx_ =>
      eapply hoare_weaken; [eapply CompileIfBool with (varb := kx_) || eapply CompileIf with (varb := kx_) |
      cancel_go..]; simpl
    end
  end.

Ltac compile_step :=
  match goal with
  | [ |- @sigT _ _ ] => eexists; intros;
    match goal with
    | [ |- Logic.and (source_stmt _) _ ] => split; [shelve | ]
    | [ |- Logic.and _ (source_stmt _) ] => split; [ | shelve]
    | _ => idtac
    end; intros;
    eapply CompileDeclareMany; intro
  | _ => eapply decls_pre_impl_post
  end
  || compile_bind
  || compile_const
  || compile_ret
  || compile_match
  || compile_read_write
  || compile_if
  || compile_for
  || compile_call
  || compile_add
  || compile_subtract
  || compile_multiply
  || compile_divide
  || compile_mod
  || compile_listop
  || compile_map_op
  || compile_join
  || compile_split
  || compile_ret_transformable
  || compile_ret_transform_part
  || compile_decompose
  .

Ltac compile :=
  unshelve (repeat compile_step);
  try match goal with
  | [|- source_stmt _] =>
    repeat source_stmt_step
  | [|- list _] => exact nil
  | [|- _ =p=> _ ] => cancel_go
  end.

Ltac make_wrapper t := lazymatch t with
  | @wrap_type _ ?H => H
  | Slice ?t =>
    let W := make_wrapper t in
    constr:(@GoWrapper_list _ W)
  | Pair ?a ?b =>
    let Wa := make_wrapper a in
    let Wb := make_wrapper b in
    constr:(@GoWrapper_pair _ _ Wa Wb)
  | ?T =>
    let T' := eval cbn in (type_denote T) in
    constr:(ltac:(typeclasses eauto) : GoWrapper T')
  end.

Ltac extract_step_declare name := match goal with
  | [ Wr : GoWrapper _ |- EXTRACT _ {{ _ }} Declare _ _ {{ _ }} // _ ] =>
    eapply CompileDeclare with (Wr := Wr); intros name
  | [ |- EXTRACT _ {{ _ }} Declare ?T_ _ {{ _ }} // _ ] =>
    let Wr_ := make_wrapper T_ in
    eapply CompileDeclare with (Wr := Wr_); intros name
  end.

Ltac extract_step_modify := match goal with
  | [|- EXTRACT (Ret tt) {{ _ }} Modify (SetConst ?x) ^(?v0) {{ _ }} // _ ] =>
    eapply CompileRet with (v := x) (var0 := v0);
    let T := type of x in
    let Wr_ := constr:(ltac:(typeclasses eauto) : GoWrapper T) in
    eapply hoare_weaken; [eapply CompileConst with (Wr := Wr_) | cancel_go..]
  | [|- EXTRACT (Ret tt) {{ ?pre }} Modify MoveOp ^(?dst, ?src) {{ _ }} // _ ] =>
    match pre with
    | context [(src ~> ?x)%pred] =>
      eapply CompileRet with (var0 := dst) (v := x);
      eapply hoare_weaken; [ eapply CompileMove | cancel_go..]
    end
  | [|- EXTRACT (Ret tt) {{ ?pre }} Modify DuplicateOp ^(?dst, ?src) {{ _ }} // _ ] =>
    match pre with
    | context [(src ~> ?x)%pred] =>
      eapply CompileRet with (var0 := dst) (v := x);
      eapply hoare_weaken; [ eapply CompileDup | cancel_go..]
    end
  | [|- EXTRACT (Ret tt) {{ ?pre }} Modify Uncons ^(?lvar_, ?cvar_, ?xvar_, ?lvar'_) {{ _ }} // _ ] =>
    match pre with
    | context [(lvar_ ~> @nil ?T_)%pred] =>
      eapply hoare_weaken; [
        eapply CompileUnconsNil with (T := T_) |
        cancel_go..
      ]
    | context [(lvar_ ~> (?a :: ?l))%pred] =>
      eapply hoare_weaken; [
        let T_ := type of a in
        eapply CompileUnconsCons with (T := T_) (x := a) (xs := l) |
        cancel_go..
      ]
    end
  end.

Ltac extract_step_flow := match goal with
  | [|- EXTRACT (Ret tt) {{ ?pre }} While (Var ?v) _ {{ _ }} // _ ] =>
    match pre with
    | context [(v ~> true)%pred] =>
      eapply hoare_weaken; [ eapply CompileWhileVarTrueOnce | cancel_go..]
    | context [(v ~> false)%pred] =>
      eapply hoare_weaken; [ eapply CompileWhileVarFalseNoOp | cancel_go..]
    end
  | [|- EXTRACT (Ret tt) {{ ?pre }} While ?ex _ {{ _ }} // _ ] =>
    match goal with
    | [ |- _] =>
      assert (forall l : locals, l ≲ pre -> is_true l ex) by (intros; eval_expr);
      eapply hoare_weaken; [ eapply CompileWhileTrueOnce | cancel_go..]; [ solve [intros; eval_expr] | ..]
    | [ |- _] =>
      assert (forall l : locals, l ≲ pre -> is_false l ex) by (intros; eval_expr);
      eapply hoare_weaken; [ eapply CompileWhileFalseNoOp | cancel_go..]; [ solve [intros; eval_expr] | ..]
    end
  | [|- EXTRACT (Ret tt) {{ ?pre }} If (Var ?v) Then _ Else _ EndIf {{ _ }} // _ ] =>
    match pre with
    | context [(v ~> true)%pred] =>
      eapply hoare_weaken; [ eapply CompileIfTrue | cancel_go..]
    | context [(v ~> false)%pred] =>
      eapply hoare_weaken; [ eapply CompileIfFalse | cancel_go..]
    end
  | [|- EXTRACT (Ret tt) {{ _ }} Skip {{ _ }} // _ ] =>
    eapply CompileSkip
  end.

Ltac extract_step :=
  extract_step_modify    ||
  extract_step_flow      ||
  match goal with
  | [|- EXTRACT _ {{ _ }} Seq _ _ {{ _ }} // _ ] =>
    eapply CompileBefore
  end.

(* this is effectively an inlined subroutine; the actual value only matters during extraction *)
Lemma CompileRetSome : forall T {WT : GoWrapper T} xvar rvar,
  sigT (fun xp => Logic.and (source_stmt xp) (
  forall A (x : T) env,
  EXTRACT Ret (Some x)
    {{ xvar ~> x * rvar ~>? (option T) * A }}
      xp
    {{ fun ret => rvar ~> ret * xvar ~>? T * A }} // env)).
Proof.
  intros.
  repeat compile_step.
  do_declare bool ltac:(fun x => set (avar := x)).
  eapply CompileBefore.
  eapply CompileRet with (v := true) (var0 := avar).
  subst_definitions.
  compile_step.
  eapply hoare_weaken.
  eapply CompileRetOptionSome with (pvar := rvar) (avar := avar) (bvar := xvar).
  all : subst_definitions; cancel_go.
  Unshelve. all: compile.
Defined.

Lemma CompileRetNone : forall T {W : GoWrapper T} rvar,
  sigT (fun xp => Logic.and (source_stmt xp) (
  forall A env,
  EXTRACT Ret (@None T)
    {{ rvar ~>? (option T) * A }}
      xp
    {{ fun ret => rvar ~> ret * A }} // env)).
Proof.
  intros.
  eexists. split. shelve. intros.
  eapply CompileDeclare with (T := bool).
  intros avar.
  eapply hoare_weaken; [ eapply CompileRetOptionNone with (pvar := rvar) (avar := avar)
    | cancel_go..].
  Unshelve. compile.
Defined.

Lemma CompileForWithBreak : forall (L G : Type) (L' : GoWrapper L)
   P Q (isFinished : forall t, {P t} + {Q t}) fRet loopvar ivar nvar contv pb xpb xFinished F env,
  (forall x, fRet x = x) ->
  (forall (t : L) (i vn vterm : W) onev termv,
    EXTRACT (BasicProg.If_ (isFinished t) (Ret false) (Ret true))
    {{ loopvar ~> t * ivar ~> i * nvar ~> vn * contv ~> true * onev ~> 1 * termv ~> vterm * F }}
       xFinished onev termv
    {{ fun ret => loopvar ~> t * ivar ~> i * nvar ~> vn * contv ~> ret * onev ~> 1 * termv ~> vterm * F }} // env) ->
  (forall (t : L) (i vn vterm : W) onev termv, (exists q, isFinished t = right q) ->
    EXTRACT pb i t
    {{ loopvar ~> t * ivar ~> i * nvar ~> vn * contv ~> true * onev ~> 1 * termv ~> vterm * F }}
       xpb onev termv
    {{ fun ret : L => loopvar ~> ret * ivar ~> i * nvar ~> vn * contv ~> true * onev ~> 1 * termv ~> vterm * F }} // env) ->
  forall n i t0
   (nocrash : G -> W -> L -> hashmap -> PredCrash.rawpred)
   (oncrash : G -> hashmap -> PredCrash.rawpred),
  EXTRACT BasicProg.ForN_ (fun i t => BasicProg.If_ (isFinished t) (Ret (fRet t)) (pb i t)) i n nocrash oncrash t0
  {{ loopvar ~> t0 * ivar ~> i * nvar ~> n * contv ~> (if isFinished t0 then false else true) * F }}
    Declare Num (fun one => (
    Declare Num (fun termv => (
    Modify (@SetConst Num 1) ^(one);
    Modify DuplicateOp ^(termv, ivar);
    Modify (ModifyNumOp Plus) ^(termv, termv, nvar);
    While (Go.TestE And (Var contv) (Var ivar < Var termv)) (
      xpb one termv;
      xFinished one termv;
      Modify (ModifyNumOp Plus) ^(ivar, ivar, one)
    )))))
  {{ fun ret => loopvar ~> ret * nvar ~> n * ivar ~>? W * contv ~>? bool * F }} // env.
Proof.
  intros.
  extract_step_declare one.
  extract_step_declare term.
  eapply hoare_strengthen_pre with (A1 := (term ~>? W * one ~>? W * _)%pred).
  cancel_go.
  repeat extract_step.
  eapply CompileRet with (var0 := term) (v := i + n).
  eapply hoare_weaken; [ eapply CompileAddInPlace1 | cancel_go..].
  generalize dependent i. revert t0.
  generalize n at 3 4.
  generalize dependent n.
  induction n; cbn; intros.
  + eapply hoare_weaken; [ eapply CompileRet' with (var0 := loopvar) | cancel_go..].
    extract_step.
  + destruct isFinished eqn:Hf.
    - unfold BasicProg.If_.
      eapply extract_equiv_prog with (pr1 := Ret t0).
      rewrite ProgMonad.bind_left_id.
      {
        denote (fRet _ = _) as Hfr.
        repeat match goal with Hfr : forall x : L, fRet x = x, H: _ |- _ => lazymatch type of H with
          | context [t0] => fail
          | _ => clear H
        end end.
        rewrite Hfr.
        revert i. induction n; cbn; intros;
        rewrite ?Hf, ?Hfr, ?ProgMonad.bind_left_id; eauto.
        reflexivity.
      }
      eapply hoare_weaken; [ eapply CompileRet' with (var0 := loopvar) | cancel_go..].
      extract_step.
    - eapply hoare_weaken; [ eapply CompileWhileTrueOnce | cancel_go..].
      intros. eval_expr.
      unfold BasicProg.If_ at 1.
      eapply hoare_weaken; [ eapply CompileBind' | cancel_go..].
      eapply hoare_weaken; [ eapply CompileAfter; eauto | cancel_go..].
      intros. cbn.
      eapply CompileBefore.
      eapply CompileRet with (v := if isFinished r then false else true) (var0 := contv).
      eapply extract_equiv_prog with (pr1 := BasicProg.If_ (isFinished r) (Ret false) (Ret true)).
      cbv; break_match; auto.
      eapply hoare_weaken; [ eauto | cancel_go..].
      eapply hoare_weaken; [ eapply CompileRet with (var0 := ivar) (v := i + 1) | cancel_go..].
      eapply hoare_weaken; [ eapply CompileAddInPlace1 | cancel_go..].
      intros.
      eapply hoare_weaken; eauto.
      repeat rewrite ?PeanoNat.Nat.add_succ_r, <- ?plus_n_O.
      cancel_go.
  Unshelve. all: eauto.
Qed.

Opaque CompileRetSome.
Opaque CompileRetNone.