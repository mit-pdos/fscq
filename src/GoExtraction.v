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

Ltac find_val v p :=
  match p with
    | context[?k ~> v] => constr:(Some k)
    | _ => constr:(@None var)
  end.

Ltac find_val_fn v p cont :=
  match p with
    | context[?k ~> v] => cont k
  end.

Ltac var_mapping_to pred val :=
  lazymatch pred with
    | context[?var ~> val] => var
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
        cont (pair_vec_nthl 0 m vars)
      end
    end
  end.

Ltac compile_bind := match goal with
  | [ |- EXTRACT Bind ?p (fun _ => ?q) {{ _ }} _ {{ _ }} // _ ] =>
    eapply CompileSeq
  | [ |- EXTRACT Bind (Ret ?x_) ?p {{ _ }} _ {{ ?post }} // _ ] =>
    match type of x_ with
    | ?T_ =>
      let Wr_ := constr:(ltac:(eauto with typeclass_instances) : GoWrapper T_) in
      do_declare T_ ltac:(fun v_ =>
        eapply hoare_strengthen_pre; [
        | eapply CompileBindRet with (vara := v_) (a := x_)];
        [ cancel_go | ..])
    end
  | [ |- EXTRACT Bind ?p ?q {{ _ }} _ {{ ?post }} // _ ] =>
    match type of p with
    | prog ?T_ =>
      let v := fresh "var" in
      let Wr_ := constr:(ltac:(eauto with typeclass_instances) : GoWrapper T_) in
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

Ltac transform_pre :=
  match goal with
  | [ |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ ] =>
    match pre with
    | context[?k ~> ?v] =>
      is_transformable v;
      eapply hoare_strengthen_pre; [
        rewrite ?transform_pimpl; simpl; reflexivity | ]
    end
  end.

Ltac compile_ret := match goal with
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; [ cancel_go ]
  | [ |- EXTRACT Ret ?x {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val x pre with
    | Some ?kx =>
      match var_mapping_to_ret with
      | ?kret => (unify kx kret; fail 2) ||
        eapply hoare_weaken; [
        eapply CompileDup with (var0 := kx) (var' := kret)
        | cancel_go.. ]
      end
    end
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

Ltac compile_call := match goal with
  | [ H : voidfunc2 ?name ?f ?env |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // ?env ] =>
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken; [ eapply H with (avar := ka) (bvar := kb) | cancel_go .. ]
        end
    end
  | [ H : func2_val_ref ?name ?f ?env |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // ?env ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
        | Some ?kb =>
          unify kb retvar; (* same variable *)
          (* first, copy the first argument *)
          match type of a with
          | ?TA =>
            do_declare TA ltac:(fun ka' =>
                                  eapply CompileBefore; [ 
                                    eapply CompileRet with (v := a) (var0 := ka');
                                    eapply hoare_weaken; [
                                      eapply CompileDup with (var0 := ka) (var' := ka') | cancel_go .. ] | ]);
            eapply hoare_weaken; [ eapply H with (avar := ka) (bvar := kb) | cancel_go .. ]
          end
        | Some ?kb =>
          (unify kb retvar; fail 2)
          || (* different variables *)
          eapply CompileBefore; [
            eapply CompileRet with (v := b) (var0 := retvar);
            simpl decls_pre |]
        end
    end
  | [ H : func1_ref ?name ?f ?env |- EXTRACT ?f ?a {{ ?pre }} _ {{ _ }} // ?env ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
    | Some ?ka =>
      unify ka retvar; (* same variable *)
      eapply hoare_weaken; [ eapply H with (avar := ka) | cancel_go .. ]
    | Some ?ka =>
      (unify ka retvar; fail 2)
      || (* different variables *)
      eapply CompileBefore; [
        eapply CompileRet with (v := a) (var0 := retvar);
        simpl decls_pre |]
    end
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
      do_declare B_ ltac:(fun bvar_ =>
        eapply hoare_weaken;
        [ eapply CompileFst with (A := A_) (B := B_) (avar := avar_) (bvar := bvar_) (pvar := pvar_)
        | cancel_go.. ])
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
      match find_val b_ pre with
      | None =>
        let B_ := type of b_ in
        eapply CompileBefore; [
          do_declare B_ ltac:(fun x_ =>
          eapply CompileRet with (v := b_) (var0 := x_);
          simpl decls_pre) |]
      | Some ?kb =>
        match var_mapping_to_ret with
        | ?kp =>
          eapply hoare_weaken;
          [ apply CompileJoin with (avar := ka) (bvar := kb) (pvar := kp)
          | cancel_go..]
        end
      end
    end
end.

Ltac compile_decompose := match goal with
  | [ |- EXTRACT Ret (?f ?a) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None =>
        eapply extract_equiv_prog; [
            let arg := fresh "arg" in
            set (arg := Ret (f a));
            pattern a in arg; subst arg;
            eapply bind_left_id | ]
    end
   | [ |- EXTRACT Ret (?f ?a ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None => 
        eapply extract_equiv_prog; [
            let arg := fresh "arg" in
            set (arg := Ret (f a b));
            pattern a in arg; subst arg;
            eapply bind_left_id | ]
    end
   | [ |- EXTRACT Ret (?f ?a ?b ?c) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None =>
        eapply extract_equiv_prog; [
            let arg := fresh "arg" in
            set (arg := Ret (f a b c));
            pattern a in arg; subst arg;
            eapply bind_left_id | ]
    end
  | [ |- EXTRACT ?f ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match f with
      | Ret => fail 2
      | _ => idtac
    end;
    match find_val a pre with
      | None =>
        eapply extract_equiv_prog; [ eapply bind_left_id | ]
    end
  | [ |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
    | None =>
      eapply extract_equiv_prog; [
        let arg := fresh "arg" in
        set (arg := f a b);
        pattern a in arg; subst arg;
        eapply bind_left_id | ]
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
      eapply hoare_weaken; [eapply CompileIf with (varb := kx_) |
      cancel_go..]; simpl
    end
  end.

Ltac compile_step :=
  match goal with
  | [ |- @sigT _ _ ] => eexists; intros; eapply CompileDeclareMany; intro
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
  || compile_listop
  || compile_map_op
  || compile_join
  || compile_split
  || compile_decompose
  || transform_pre (* TODO: only do this when it should be useful *)
  .

Ltac compile :=
  unshelve (repeat compile_step); try exact nil.
