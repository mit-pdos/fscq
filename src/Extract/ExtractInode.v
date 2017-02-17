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

Instance z : GoWrapper (Rec.Rec.data INODE.IRecSig.itemtype).
  simpl.
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
  Import Rec.
  cbv [Rec.of_word Rec.len INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype INODE.NDirect
             Rec.len Rec.data Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
             plus minus mult
             addrlen hashlen wtl whd
             sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in *.
  match goal with
  | |- context[@Rec.word_selN' ?ft ?l ?i ?w] => pattern_prog (@Rec.word_selN' ft l i w)
  end.
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
  
  cbv [Rec.len plus mult]. fold Nat.add Nat.mul.
  lazymatch goal with
  | [ |- EXTRACT (Ret (?f ?a ?b ?c ?d)) {{ _ }} _ {{ _ }} // _ ] =>
    make_value_exist a
  end.
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
  cancel_go.
  norm.
  do 28 delay_one.
  eapply cancel_one.
  eapply PickFirst.
  match goal with
  | |- okToCancel (nth_var _ vars |-> ?a) (nth_var _ vars |-> ?b) => let H := fresh in assert (a = b) as H; [ | rewrite H; reflexivity ]
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
  Require Import PeanoNat.
  apply Nat.mod_upper_bound.
  apply INODE.IRec.Defs.items_per_val_not_0.

  eapply extract_equiv_prog.
  erewrite ?split2_iter.
  repeat change (match ?He in (_ = N) return (word N) with | eq_refl => ?x end) with (rew He in x).
  rewrite ?eq_rect_double.
  rewrite ?eq_rect_split1.
  rewrite ?eq_rect_split2.
  erewrite ?split2_split1.
  erewrite ?split1_iter.
  repeat change (match ?He in (_ = N) return (word N) with | eq_refl => ?x end) with (rew He in x).
  progress rewrite ?eq_rect_split2.
  erewrite ?split2_iter.
  repeat change (match ?He in (_ = N) return (word N) with | eq_refl => ?x end) with (rew He in x).
  rewrite ?eq_rect_double.
  Lemma fold_Rec_middle : forall low mid high w,
      split1 mid high (split2 low (mid + high) w) = Rec.middle low mid high w.
  Proof.
    reflexivity.
  Qed.
  rewrite ?fold_Rec_middle.
  reflexivity.


Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  (* TODO add more programs here *)
  exact env.
Defined.
