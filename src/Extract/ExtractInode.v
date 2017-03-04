Require Import Eqdep.
Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations EqNotations.

Import Go.

Require Import Inode.

Local Open Scope string_scope.

Set Implicit Arguments.

Instance z : GoWrapper (Rec.Rec.data INODE.IRecSig.itemtype).
  simpl.
  change word with immut_word.
  typeclasses eauto.
Defined.

(*
Example compile_getattrs : sigT (fun p => source_stmt p /\
  forall env lxp ixp inum ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "irec_get" Inode.INODE.IRec.get env ->
  EXTRACT INODE.getattrs lxp ixp inum ms
  {{ 0 ~>? (Log.LOG.memstate * ((Rec.Rec.data INODE.iattrtype) * unit)) *
     1 ~> lxp *
     2 ~> ixp *
     3 ~> inum *
     4 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? FSLayout.inode_xparams *
     3 ~>? nat *
     4 ~>? Log.LOG.memstate }} // env).
Proof.
  unfold INODE.getattrs, INODE.IRec.get_array, pair_args_helper.
  compile_step.
  compile_step.
  eapply extract_equiv_prog.
  rewrite ProgMonad.bind_right_id.
  reflexivity.
  compile_step.
  Import Rec.
  cbv [INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype INODE.irec INODE.IRec.Defs.item
       Rec.data Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
      sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in *.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  Ltac do_declare T cont ::=
  lazymatch goal with
  | |- EXTRACT _
       {{ ?pre }}
          _
       {{ _ }} // _ =>
         lazymatch goal with
         | |- EXTRACT _
              {{ ?pre }}
                 _
              {{ _ }} // _ =>
           (* no simpl *)
               lazymatch pre with
               | context [ decls_pre ?decls ?vars ?m ] =>
                   let decls' := fresh "decls" in
                   evar ( decls' : list Declaration ); unify decls (Decl T :: decls'); subst decls';
                    cont (nth_var m vars)
               end
         end
  end.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  Unshelve.
  all: try match goal with
           | [|- source_stmt _] =>
             repeat source_stmt_step
           | [|- list _] => exact nil
           | [|- _ =p=> _ ] => cancel_go
           end.
Qed.
*)

Ltac real_val_in v :=
  lazymatch v with
  | rew ?H in ?v' => real_val_in v'
  | _ => v
  end.

Ltac find_val' v p :=
  match p with
  | context[(?k ~> v)%pred] =>
    constr:(Some k)
  | context[ (?k |-> Val _ (id v))%pred ] =>
    constr:(Some k)
  | _ => constr:(@None var)
  end.

Ltac find_val v p ::=
     let v' := real_val_in v in
     find_val' v' p.

Ltac ensure_value_exists v_ pre cont :=
  let v' := real_val_in v_ in
  idtac v_ "actually" v';
  match find_val v_ pre with
  | Some ?var => idtac var "ptsto" v_; cont var
  | None =>
    let T := type of v' in
    do_declare T ltac:(fun var => eapply CompileBefore; [
                                 eapply CompileRet with (var0 := var) (v := v'); repeat compile_step |
                                 cont var ])
  end.

Import Rec.

Ltac compile_middle :=
  lazymatch goal with
  | [ |- EXTRACT Ret (middle_immut ?low ?mid ?high ?buf) {{ ?pre }} _ {{ _ }} // ?env ] =>
    let retvar := var_mapping_to_ret in
    ensure_value_exists low pre ltac:(fun kfrom =>
                                        ensure_value_exists (low + mid) pre ltac:(fun kto =>
                                                                                    ensure_value_exists buf pre ltac:(fun kbuf =>
                                                                                                                        eapply hoare_weaken;
                                                                                                                        [ eapply (@CompileMiddle low mid high buf env retvar kbuf kfrom kto); try divisibility | intros; cbv beta; try rewrite okToCancel_eq_rect_immut_word; cancel_go..])))
  end.

Require Import PeanoNat.

Example compile_irec_get : sigT (fun p => source_stmt p /\
  forall env lxp ixp inum ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "log_read" Log.LOG.read env ->
  EXTRACT INODE.IRec.get lxp ixp inum ms
  {{ 0 ~>? (Log.LOG.mstate * Cache.cachestate * (Rec.data INODE.IRecSig.itemtype * unit)) *
     1 ~> lxp *
     2 ~> ixp *
     3 ~> inum *
     4 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? FSLayout.inode_xparams *
     3 ~>? nat *
     4 ~>? Log.LOG.memstate }} // env).
Proof.
  unfold Inode.INODE.IRec.get, INODE.IRecSig.RAStart, Log.LOG.read_array, pair_args_helper.
  compile_step.
  eapply extract_equiv_prog.
  rewrite ProgMonad.bind_assoc.
  reflexivity.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_split.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  unfold INODE.IRec.Defs.selN_val2block.
  match goal with
  | |- context[@Rec.word_selN' ?ft ?l ?i ?w] => pattern_prog (@Rec.word_selN' ft l i w)
  end.
  (*
  cbv [Rec.of_word Rec.len INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype INODE.NDirect
             Rec.len Rec.data Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
             plus minus mult
             addrlen hashlen wtl whd
             sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in *.
*)
  Ltac do_declare T cont ::=
  lazymatch goal with
  | |- EXTRACT _
       {{ ?pre }}
          _
       {{ _ }} // _ =>
         lazymatch goal with
         | |- EXTRACT _
              {{ ?pre }}
                 _
              {{ _ }} // _ =>
           (* no simpl *)
               lazymatch pre with
               | context [ decls_pre ?decls ?vars ?m ] =>
                   let decls' := fresh "decls" in
                   evar ( decls' : list Declaration ); unify decls (Decl T :: decls'); subst decls';
                    cont (nth_var m vars)
               end
         end
  end.
  do_declare (immut_word 1024) ltac:(fun var => idtac var).
  eapply hoare_weaken; [ eapply CompileBindRet with (HA := GoWrapper_immut_word 1024) (vara := nth_var 20 vars) | cancel_go.. ].
  unfold Rec.word_selN'.
  rewrite <- Rec.word_selN_shift_equiv.
  unfold Rec.word_selN.
  eapply extract_equiv_prog.
  Lemma f_into_match : forall A B C D (e : {A} + {B}) (L : A -> C) (R : B -> C) (f : C -> D),
      f (match e with | left l0 => L l0 | right r0 => R r0 end) =
      match e with | left l0 => f (L l0) | right r0 => f (R r0) end.
  Proof.
    intros.
    destruct e; reflexivity.
  Qed.
  rewrite f_into_match with (f := Ret).
  reflexivity.
  Ltac make_value_exist v_ :=
    let T := type of v_ in
    eapply CompileBefore; [
      do_declare T ltac:(fun var => idtac var v_;
                           eapply CompileRet with (var0 := var) (v := v_)); repeat compile_step | ].
  make_value_exist INODE.IRecSig.items_per_val.
  make_value_exist (PeanoNat.Nat.modulo inum INODE.IRecSig.items_per_val).
  eapply hoare_weaken; [ eapply (@CompileIfLt' _ (nth_var 22 vars) (nth_var 21 vars)); intros | cancel_go..].
  Focus 2.

  simpl.
  eapply hoare_weaken.
  eapply CompileConst with (v := nth_var 20 vars) (Wr := GoWrapper_immut_word 1024).
  rewrite okToCancel_ptsto_typed_any_typed with (var0 := nth_var 16 vars).
  cancel_go.
  cancel_go.
  
  cbv [Rec.len plus mult]. fold Nat.add Nat.mul Rec.len.
  Ltac cancel_go ::= cancel_go_fast.
  lazymatch goal with
  | [ |- EXTRACT (Ret (?f ?a ?b ?c ?d)) {{ _ }} _ {{ _ }} // _ ] =>
    make_value_exist a
  end.
  simpl. (* We actually don't really want to [simpl], but since other things do it we've gotta do it here *)
  lazymatch goal with
  | [ |- EXTRACT (Ret (?f ?a ?b ?c ?d)) {{ _ }} _ {{ _ }} // _ ] =>
    make_value_exist (a + b)
  end.
  
  (* Freeze the buffer *)
  pattern_prog (fst (snd a)).
  do_declare (immut_word valulen) ltac:(fun var => idtac var).
  eapply hoare_weaken.
  eapply CompileBindRet with (A := immut_word valulen) (vara := nth_var 25 vars) (a := fst (snd a)).
  3: cancel_go.
  3: cancel_go.

  eapply hoare_weaken.
  apply CompileFreeze with (svar := nth_var 16 vars) (dvar := nth_var 25 vars).
  divisibility.
  cancel_go.
  cancel_go.
  eapply hoare_weaken.
  eapply (@CompileMiddle _ _ _ _ env (nth_var 20 vars) (nth_var 25 vars) (nth_var 23 vars) (nth_var 24 vars)).
  divisibility.
  divisibility.
  divisibility.
Ltac cancel_go ::=
  solve [GoSepAuto.cancel_go_refl] ||
  solve [GoSepAuto.cancel_go_fast] ||
  unfold var, default_value; GoSepAuto.cancel; try apply pimpl_refl.
  cancel_go.
  norm.
  do 28 delay_one.
  eapply cancel_one.
  eapply PickFirst.
  match goal with
  | |- okToCancel (nth_var _ vars |-> ?a) (nth_var _ vars |-> ?b) => let H := fresh in assert (a = b) as H; [ | rewrite H ]
  end.
  cbv [wrap wrap' wrap_type GoWrapper_immut_word].
  f_equal.
  unfold INODE.IRec.Defs.val2word.
  unfold eq_rec.
  rewrite eq_rect_double.
  match goal with
  | |- context[rew ?He in _] => let H := fresh in let Te := type of He in assert Te as H; [ | generalize He; rewrite <- H ]
  end.
  rewrite INODE.IRecSig.blocksz_ok; simpl.
  rewrite (Rec.word_selN_helper 1024 l0) at 1.
  reflexivity.
  intros.
  f_equal.
  rewrite UIP_refl with (p := e).
  reflexivity.
  cancel'.
  intros.
  unfold INODE.IRec.Defs.val2word.
  unfold eq_rec.
  rewrite eq_rect_double.
  match goal with
  | |- context[wrap (rew ?He in ?x)] => replace (wrap (rew He in x)) with (wrap (fst (snd a) : immut_word _))
  end.
  cancel_go.
  cbv [wrap wrap' wrap_type GoWrapper_immut_word].
  simpl.
  match goal with
  | |- context[rew ?He in _] => let H := fresh in let Te := type of He in assert Te as H; [ | generalize He; rewrite <- H ]
  end.
  rewrite INODE.IRecSig.blocksz_ok; simpl.
  rewrite (Rec.word_selN_helper 1024 l0) at 1.
  reflexivity.
  intros.
  f_equal.
  rewrite UIP_refl with (p := e).
  reflexivity.
  unfold stars; simpl.
  reflexivity.
  cancel_go.
  Require Import PeanoNat.
  apply Nat.mod_upper_bound.
  apply INODE.IRec.Defs.items_per_val_not_0.

  eapply hoare_weaken.
  eapply compile_of_word with (vsrc := nth_var 20 vars) (vdst := nth_var 14 vars).
  repeat (simpl; unfold addrlen; (constructor || divisibility)).
  cancel_go.
  cancel_go.

  (* TODO: [cancel_go_refl] and [cancel_go_fasts] take forever here because they [simpl]. *)
  Ltac cancel_go ::= intros **; cbv beta; repeat (try apply pimpl_refl; cancel_one_fast).
  compile_join.
  cancel_go_fast.

  change (fst ^(fst a, fst (snd a))) with (fst a).
  Hint Extern 0 (okToCancel (exists val', ?var |-> Val _ val')%pred (exists val', ?var |-> Val _ val')%pred) =>
  reflexivity : okToCancel.
  compile_join.

  (* TODO: reflexive cancellation doesn't work here because computing [cancel_some] takes forever *)
  simpl decls_post.
  cbv beta.
  norml; normr; cbv [app].
  eapply cancel_one.
  do 19 eapply PickLater; eapply PickFirst.
  apply pimpl_exists_r; simpl; eauto.
  eapply cancel_one.
  do 13 eapply PickLater; eapply PickFirst.
  apply pimpl_exists_r. (* [simpl] takes forever here *)
  cbv [moved_value wrap wrap_type GoWrapper_pair GoWrapper_rec GoWrapper_immut_word Rec.type_rect_nest
      GoWrapper_unit INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype list_rect].
  eexists. reflexivity.

  cancel_one.

  eapply cancel_one.
  eapply PickFirst.
  apply pimpl_exists_r. (* [simpl] takes forever here *)
  cbv [moved_value wrap wrap_type GoWrapper_pair GoWrapper_rec GoWrapper_immut_word Rec.type_rect_nest
      GoWrapper_unit INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype list_rect].
  eexists. reflexivity.

  repeat cancel_one.

  eapply cancel_one.
  eapply PickFirst.
  apply pimpl_exists_r. (* [simpl] takes forever here *)
  cbv [moved_value wrap wrap_type GoWrapper_pair GoWrapper_rec GoWrapper_immut_word Rec.type_rect_nest
      GoWrapper_unit INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype list_rect].
  eexists. reflexivity.

  unfold stars. cancel.

  Unshelve.
  eauto.
  

  apply source_stmt_many_declares; intro.
  repeat econstructor.

  exact [].

Defined. (* Anomaly: Uncaught exception Not_found. *)



Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  (* TODO add more programs here *)
  exact env.
Defined.