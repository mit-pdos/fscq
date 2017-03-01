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

Definition eq_leibniz A B (f : A -> B) x y (e : x = y) : f x = f y.
  destruct e.
  reflexivity.
Defined.

Lemma eq_rect_leibniz : forall A B (f : A -> B) x y (e : x = y) P p,
    rew [fun x0 => P (f x0)] e in p = rew [P] (eq_leibniz f e) in p.
Proof.
  intros.
  destruct e.
  reflexivity.
Defined.

Lemma okToCancel_eq_rect_immut_word : forall x y p (e : x = y) var,
    ((var ~> rew [immut_word] e in p) : pred) <=p=> (var ~> p).
Proof.
  intros.
  replace (wrap (rew [immut_word] e in p)) with (wrap p).
  reflexivity.
  revert p.
  rewrite e.
  intros.
  cbv [wrap wrap' GoWrapper_immut_word].
  reflexivity.
Qed.
Hint Extern 0 (okToCancel (?var ~> ?p) (?var ~> rew [immut_word] ?e in ?p)) =>
  apply okToCancel_eq_rect_immut_word.
Hint Extern 0 (okToCancel (?var ~> rew [immut_word] ?e in ?p) (?var ~> ?p)) =>
  apply okToCancel_eq_rect_immut_word.

Ltac real_val_in v :=
  lazymatch v with
  | rew ?H in ?v' => real_val_in v'
  | _ => v
  end.

Ltac find_val' v p :=
  match p with
  | (?l * ?r)%pred =>
    match find_val' v l with
    | Some ?k => constr:(Some k)
    | None => find_val' v r
    end
  | (?k ~> ?v_)%pred =>
    let eq := constr:(eq_refl v_ : v_ = v) in
    constr:(Some k)
  | context [ (?k |-> Val _ (id ?v_))%pred ] =>
    let eq := constr:(eq_refl v_ : v_ = v) in
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
Definition middle_immut : forall low mid high w, immut_word mid := Rec.middle.

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

Example compile_irec_of_word : sigT (fun p => source_stmt p /\
  forall env (buf : immut_word (Rec.len INODE.IRecSig.itemtype)),
    EXTRACT Ret (@Rec.of_word INODE.IRecSig.itemtype buf)
    {{ 0 ~>? Rec.Rec.data INODE.IRecSig.itemtype *
       1 ~> buf }}
      p
    {{ fun ret => 0 ~> ret * 1 ~> buf }} // env).
Proof.                                             
  compile_step.
  erewrite Rec.of_word_middle_eq.
  cbv [Rec.of_word_middle Rec.len INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype INODE.NDirect
             Rec.len Rec.data Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
             plus minus mult
             addrlen hashlen wtl whd
             sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_sym eq_ind_r eq_ind] in *.
  fold INODE.iattrtype.
  change Rec.middle with middle_immut.
  change word with immut_word.
  change (fun n => immut_word n) with immut_word.
  Ltac replace_parts p cont :=
    idtac;
    match p with
    | (?a, ?b) =>
      replace_parts a ltac:(replace_parts b cont)
    | ?a :: ?b =>
      replace_parts a ltac:(replace_parts b cont)
    | ?a =>
      (is_evar a; fail 1) ||
                          let ta := type of a in
                          let Ha := fresh in
                          evar (Ha : ta);
                          let Ha' := eval unfold Ha in Ha in
                              clear Ha; replace a with Ha'; [ cont | ]
    end.
  eapply extract_equiv_prog.
  match goal with
  | |- ProgMonad.prog_equiv _ (Ret ?p) => replace_parts p ltac:(idtac "done")
  end.
  reflexivity.
  reflexivity.
  reflexivity.



  Ltac simpl_rew :=
    repeat match goal with
           | |- context[rew [?P_] ?e_ in ?p_] =>
             (unify P_ word; fail 1)
             ||
             rewrite eq_rect_leibniz with (P := immut_word) (e := e_)
           end;
    rewrite ?eq_rect_double;
    match goal with
    | |- context[rew [?P_] ?e_ in ?p_] =>
      let te := type of e_ in
      let He := fresh in
      evar (He : te);
      let He' := eval unfold He in He in
          clear He; replace e_ with He'; [ | shelve ]
    end.

  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
  simpl_rew; reflexivity.
    
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.
  compile_middle || compile_step.

Admitted.

(*
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

  cbv [Rec.of_word Rec.len INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype INODE.NDirect
             Rec.len Rec.data Rec.recdata Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
             plus minus mult
             addrlen hashlen wtl whd
             sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in *.
  eapply extract_equiv_prog.
  (* Split up the rewrites into separate goals to reduce proof term size *)

  Ltac replace_parts p cont :=
    idtac;
    match p with
    | (?a, ?b) =>
      replace_parts a ltac:(replace_parts b cont)
    | ?a :: ?b =>
      replace_parts a ltac:(replace_parts b cont)
    | ?a =>
      (is_evar a; fail 1) ||
                          let ta := type of a in
                          let Ha := fresh in
                          evar (Ha : ta);
                          let Ha' := eval unfold Ha in Ha in
                              clear Ha; replace a with Ha'; [ cont | ]
    end.
  match goal with
  | |- ProgMonad.prog_equiv _ (Ret ?p) => replace_parts p ltac:(idtac "done")
  end.
  reflexivity.
  reflexivity.
  reflexivity.

  Lemma fold_Rec_middle : forall low mid high w,
      split1 mid high (split2 low (mid + high) w) = Rec.middle low mid high w.
  Proof.
    reflexivity.
  Qed.

  Definition split1_iter' :
    forall n1 n2 n3 Heq w,
      split1 n1 n2 (split1 (n1 + n2) n3 w) =
      split1 n1 (n2 + n3) (rew Heq in w) := split1_iter.
  Definition split2_iter' :
    forall n1 n2 n3 Heq w,
      split2 n2 n3 (split2 n1 (n2 + n3) w) =
      split2 (n1 + n2) n3 (rew Heq in w) := split2_iter.
  Definition split2_split1' :
    forall n1 n2 n3 Heq w,
      split2 n1 n2 (split1 (n1 + n2) n3 w) =
      split1 n2 n3
             (split2 n1 (n2 + n3) (rew Heq in w)) := split2_split1.
  Ltac rewrite_splits :=
    repeat (repeat erewrite ?split2_iter', ?eq_rect_split2, ?eq_rect_double;
            repeat erewrite ?split1_iter', ?eq_rect_split1, ?eq_rect_double;
            repeat erewrite ?split2_split1', ?eq_rect_split1, ?eq_rect_split2, ?eq_rect_double); rewrite ?fold_Rec_middle.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.
  rewrite_splits; reflexivity.

  match goal with
  | |- context[@Rec.word_selN' ?ft ?l ?i ?w] =>
    set (@Rec.word_selN' ft l i w)
  end.
  cbv [Rec.of_word Rec.len INODE.IRecSig.itemtype INODE.irectype INODE.iattrtype INODE.NDirect
             Rec.len Rec.data Rec.recdata Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
             plus minus mult
             addrlen hashlen wtl whd
             sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_sym eq_ind_r eq_ind] in *.
  subst_definitions.
  compile_step.
  repeat change (decls_pre (@Decl ?T ?Wr :: ?decls') ?vars ?n)
         with ((exists val_, nth_var n vars |-> Val (@wrap_type _ Wr) val_) * decls_pre decls' vars (S n))%pred.
  compile_step.
  compile_step.
  (* TODO: could just [compile_step] here except that it would declare Buffer rather than ImmutableBuffer *)
  match goal with
  | |- EXTRACT Ret (?a_, ?b_)
       {{ ?pre }}
          _
       {{ ?post }} // _ =>
        match find_val a_ pre with
        | None =>
            let A_ := type of (a_ : immut_word _) in
            eapply CompileBefore;
             [ do_declare A_
                ltac:((fun x_ => eapply CompileRet with (v := a_ : immut_word _) (var0 := x_); simpl decls_pre))
             |  ]
        | Some ?ka =>
            match var_mapping_to_ret with
            | ?kp =>
                let B_ := type of (b_ : immut_word _) in
                match B_ with
                | unit =>
                    eapply hoare_weaken;
                     [ eapply CompileJoinUnit with (avar := ka) (pvar := kp) | cancel_go.. ]
                | _ =>
                    match find_val b_ pre with
                    | None =>
                        eapply CompileBefore;
                         [ do_declare B_
                            ltac:((fun x_ =>
                                     eapply CompileRet with (v := b_ : immut_word) (var0 := x_); simpl decls_pre))
                         |  ]
                    | Some ?kb =>
                        eapply hoare_weaken;
                         [ apply CompileJoin with (avar := ka) (bvar := kb) (pvar := kp)
                         | cancel_go.. ]
                    end
                end
            end
        end
  end.
  change (fst (snd ^(fst a, fst (snd a)))) with (fst (snd a)).
  Time compile_middle. (* 216 s *)
  divisibility.
  divisibility.
  divisibility.
  Focus 1.
  match goal with
  | |- context[wrap (rew ?He in ?x)] => replace (wrap (rew He in x)) with (wrap (x : immut_word _))
  end.
  cancel_go.

  cbv [wrap wrap' wrap_type GoWrapper_immut_word].
  simpl.
  repeat f_equal.
  match goal with
  | |- context[rew ?He in _] => rewrite UIP_refl with (p := He)
  end.
  reflexivity.

  (* One down, eight to go! :) *)

Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  (* TODO add more programs here *)
  exact env.
Defined.

*)