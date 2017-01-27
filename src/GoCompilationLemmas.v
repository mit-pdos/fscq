Require Import Eqdep.
Require Import Morphisms Relation_Operators.
Require Import PeanoNat Plus String List.
Require Import Word Bytes AsyncDisk Prog ProgMonad BasicProg Pred.
Require Import StringMap.
Require Import GoSemantics GoFacts GoHoare GoSepAuto.
Require Import GoTactics2.

Import ListNotations.

Set Implicit Arguments.


Hint Constructors step fail_step crash_step exec.

Hint Extern 1 (Go.eval _ _ = _) =>
unfold Go.eval.

Hint Extern 1 (Go.step _ (_, Go.Assign _ _) _) =>
  eapply Go.StepAssign.
Hint Constructors Go.step.



Lemma CompileSkip : forall env A,
  EXTRACT Ret tt
  {{ A }}
    Go.Skip
  {{ fun _ => A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
Qed.


Lemma CompileConst : forall T {Wr: GoWrapper T} env A (v : Go.var) (val : T),
  EXTRACT Ret val
  {{ v ~>? T * A }}
    v <~const (wrap' val)
  {{ fun ret => v ~> ret * A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  eval_expr.
  do 2 eexists.
  intuition eauto.
  pred_solve.

  eval_expr.
  contradiction H1.
  repeat econstructor; [eval_expr; eauto..].
Qed.


Lemma CompileRet : forall T {H: GoWrapper T} env A B var (v : T) p,
  EXTRACT Ret v
  {{ A }}
    p
  {{ fun ret => var ~> ret * B }} // env ->
  EXTRACT Ret tt
  {{ A }}
    p
  {{ fun _ => var ~> v * B }} // env.
Proof.
  unfold ProgOk; intros.
  forward_solve;
    repeat match goal with
    | [H : exec _ _ (Ret _) _ |- _] =>
        invc H;
        repeat find_apply_lem_hyp inj_pair2; repeat subst; eauto
    | [H : _ |- _ ] => solve [invc H]
    end.
  Unshelve.
  all: auto.
Qed.

Lemma CompileRet' : forall T {H: GoWrapper T} env A B var (v : T) p,
  EXTRACT Ret tt
  {{ A }}
    p
  {{ fun _ => var ~> v * B }} // env ->
  EXTRACT Ret v
  {{ A }}
    p
  {{ fun ret => var ~> ret * B }} // env.
Proof.
  unfold ProgOk; intros.
  forward_solve;
    repeat match goal with
    | [H : exec _ _ (Ret _) _ |- _] =>
        invc H;
        repeat find_apply_lem_hyp inj_pair2; repeat subst; eauto
    | [H : _ |- _ ] => solve [invc H]
    end.
  Unshelve.
  all: auto.
Qed.

Lemma CompileConst' : forall T {Wr: GoWrapper T} env A var (v : T),
  EXTRACT Ret tt
  {{ var ~>? T * A }}
    var <~const (wrap' v)
  {{ fun _ => var ~> v * A }} // env.
Proof.
  eauto using CompileRet, CompileConst.
Qed.

Import Go.

Inductive Declaration :=
| Decl (T : Type) {Wr: GoWrapper T} {D : DefaultValue T}.

Arguments Decl T {Wr} {D}.

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
    exact ((nth_var m vars |-> wrap zeroval * IHdecls (S m))%pred).
Defined.

Lemma decls_pre_shift : forall decls n vars var0 m,
  @decls_pre decls (S n) (var0, vars) (S m) <=p=> @decls_pre decls n vars m.
Proof.
  induction decls.
  - reflexivity.
  - intros. destruct a. simpl.
    split; cancel;
    apply IHdecls.
Qed.

Definition decls_post (decls : list Declaration) {n} (vars : n_tuple n var) : nat -> pred.
  induction decls; intro m.
  - exact emp.
  - exact ((nth_var m vars |->? * IHdecls (S m))%pred).
Defined.

Lemma decls_post_shift : forall decls n vars var0 m,
  @decls_post decls (S n) (var0, vars) (S m) <=p=> @decls_post decls n vars m.
Proof.
  induction decls.
  - reflexivity.
  - intros. destruct a. simpl.
    split; cancel;
    apply IHdecls.
Qed.


Lemma decls_pre_impl_post :
  forall n decls vars m,
    @decls_pre decls n vars m =p=> decls_post decls vars m.
Proof.
  induction decls; intros.
  - auto.
  - destruct a.
    cancel. auto.
Qed.
Hint Resolve decls_pre_impl_post : cancel_go_finish.

Hint Extern 0 (okToCancel (decls_pre ?decls ?vars ?m) (decls_post ?decls ?vars ?m)) =>
  apply decls_pre_impl_post.

Local Open Scope map_scope.

Lemma Declare_fail :
  forall env d s t xp,
    Go.exec env (d, s, Go.Declare t xp) Go.Failed ->
    exists var, Go.exec env (d, var ->> Go.default_value t; s,
      (xp var; Go.Undeclare var)%go) Go.Failed /\ VarMap.find var s = None.
Proof.
  intros.
  invc H.
  + invc H0; eauto.
  + exfalso; eauto using can_always_declare.
Qed.

Lemma Undeclare_fail :
  forall env st var,
    Go.exec env (st, Go.Undeclare var) Go.Failed -> False.
Proof.
  intros.
  invc H.
  + repeat inv_exec; auto.
  + contradiction H0. destruct st. repeat econstructor.
Qed.

Lemma CompileDeclare :
  forall env R T {Wr : GoWrapper T} {WrD : DefaultValue T} A B (p : prog R) xp,
    (forall var,
       EXTRACT p
       {{ var ~> zeroval * A }}
         xp var
       {{ fun ret => var |->? * B ret }} // env) ->
    EXTRACT p
    {{ A }}
      Go.Declare wrap_type xp
    {{ fun ret => B ret }} // env.
Proof.
  unfold ProgOk; intros.
  repeat destruct_pair.
  destruct out; intuition try discriminate; simpl in *.
  - find_apply_lem_hyp Declare_fail; repeat deex.

    specialize (H x (r, x ->> Go.default_value wrap_type; l) hm).
    forward H.
    {
      simpl. pred_solve.
    }
    intuition idtac.
    find_apply_lem_hyp Go.ExecFailed_Steps.
    forward_solve.
    find_apply_lem_hyp Go.Steps_Seq.
    forward_solve.

    + find_apply_lem_hyp Go.Steps_ExecFailed; eauto.
      forward_solve.
      cbv [snd Go.is_final]. intuition (subst; eauto).
      forward_solve.

    + exfalso; eauto using Undeclare_fail, Go.Steps_ExecFailed.

  - do 2 inv_exec.
    specialize (H var0 (r, var0 ->> Go.default_value wrap_type; l) hm).
    forward H.
    {
      simpl. pred_solve.
    }
    destruct_pair.
    find_inversion_safe.
    find_eapply_lem_hyp Go.ExecFinished_Steps.
    find_eapply_lem_hyp Go.Steps_Seq.
    forward_solve.
    repeat find_eapply_lem_hyp Go.Steps_ExecFinished.
    invc H4. invc H. invc H5. invc H.
    forward_solve.
    simpl in *.
    repeat eexists; eauto.
    pred_solve.

  - do 2 inv_exec.
    specialize (H var0 (r, var0 ->> Go.default_value wrap_type; l) hm).
    forward H.
    {
      simpl. pred_solve.
    }
    find_inversion_safe.
    find_eapply_lem_hyp Go.ExecCrashed_Steps.
    repeat deex; try discriminate.
    find_eapply_lem_hyp Go.Steps_Seq.
    intuition idtac.
    + repeat deex.
      invc H4.
      eapply Go.Steps_ExecCrashed in H2; eauto.
      simpl in *.
      forward_solve.
    + deex.
      invc H5; [ invc H4 | invc H ].
      invc H6; [ invc H4 | invc H ].
Qed.

Definition many_declares (decls : list Declaration) (xp : n_tuple (length decls) var -> stmt) : stmt.
  induction decls; simpl in *.
  - exact (xp tt).
  - destruct a.
    eapply (Declare wrap_type); intro var.
    apply IHdecls; intro.
    apply xp.
    exact (var, X).
Defined.

Lemma CompileDeclareMany :
  forall env T (decls : list Declaration) xp A B (p : prog T),
    (forall vars : n_tuple (length decls) var,
       EXTRACT p
       {{ decls_pre decls vars 0 * A }}
         xp vars
       {{ fun ret => decls_post decls vars 0 * B ret }} // env) ->
    EXTRACT p
    {{ A }}
      many_declares decls xp
    {{ fun ret => B ret }} // env.
Proof.
  induction decls; simpl; intros.
  - eapply hoare_weaken; [ apply H | cancel_go.. ].
  - destruct a. eapply CompileDeclare; eauto. intros.
    eapply IHdecls. intros.
    eapply hoare_weaken; [ apply H | cancel_go.. ].
    rewrite <- decls_pre_shift.
    reflexivity.
    rewrite decls_post_shift.
    cancel.
Qed.

Lemma CompileVar : forall env A var T (v : T) {H : GoWrapper T},
  EXTRACT Ret v
  {{ var ~> v * A }}
    Go.Skip
  {{ fun ret => var ~> ret * A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
Qed.

Lemma CompileBind : forall T T' {H: GoWrapper T} env A B (C : T' -> _) v0 p f xp xf var,
  EXTRACT p
  {{ var ~> v0 * A }}
    xp
  {{ fun ret => var ~> ret * B }} // env ->
  (forall (a : T),
    EXTRACT f a
    {{ var ~> a * B }}
      xf
    {{ C }} // env) ->
  EXTRACT Bind p f
  {{ var ~> v0 * A }}
    xp; xf
  {{ C }} // env.
Proof.
  unfold ProgOk.
  intuition subst.

  - find_eapply_lem_hyp Go.ExecFinished_Steps. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecFinished.
    forward_solve.

  - find_eapply_lem_hyp Go.ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex.
    + invc H5. find_eapply_lem_hyp Go.Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct_pair. find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecCrashed; eauto.
      forward_solve.

  - find_eapply_lem_hyp Go.ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex.
    + eapply Go.Steps_ExecFailed in H5; eauto.
      * forward_solve.
      * unfold Go.is_final; simpl; intuition (subst; eauto).
      * intuition. repeat deex.
        intuition eauto.
    + destruct_pair. find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecFailed; eauto.
      forward_solve.
Qed.

Ltac exec_solve_step :=
  lazymatch goal with
  | [ H : ~Go.is_final _ |- _] =>
    exfalso; solve [apply H; forward_solve]
  | [ H : context [ProgOk _ ?p ?xp],
      H': exec _ (pair _ ?p) _,
      H'': context [Prog.exec _ _ ?xp] |- _ ] =>
    fail
  | [ H : context [ProgOk _ ?p],
      H': exec _ (_, ?p) _ |- _ ] =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      edestruct H as [H1 [H2 H3] ]; [ | exact H' |..];
      [simpl; solve [pred_solve] |..];
      forward_solve
  | _ => (inv_exec; eval_expr) ||
         (eval_expr;
         solve [
           repeat eexists; rewrite ?Bytes.valu2bytes2valu; eauto; pred_solve |
           repeat econstructor; pred_solve
         ])
  end.

Lemma CompileSeq : forall T T' env A B (C : T -> _) p1 p2 x1 x2,
  EXTRACT p1
  {{ A }}
    x1
  {{ fun _ => B }} // env ->
  EXTRACT p2
  {{ B }}
    x2
  {{ C }} // env ->
  EXTRACT Bind p1 (fun _ : T' => p2)
  {{ A }}
    x1; x2
  {{ C }} // env.
Proof.
  unfold ProgOk.
  intuition subst.

  - find_eapply_lem_hyp ExecFinished_Steps. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFinished.
    forward_solve.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H4. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct_pair. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.

  - find_eapply_lem_hyp ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + eapply Steps_ExecFailed in H4; eauto.
      * forward_solve.
      * unfold is_final; simpl; intuition (subst; eauto).
      * intuition. repeat deex.
        intuition eauto.
    + destruct_pair. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forward_solve.

  Unshelve.
  all: auto.
Qed.

Lemma CompileBindDiscard : forall T T' env A (B : T' -> _)
  (p : prog T) (f : prog T') xp xf,
  EXTRACT p
  {{ A }}
    xp
  {{ fun _ => A }} // env ->
  EXTRACT f
  {{ A }}
    xf
  {{ B }} // env ->
  EXTRACT Bind p (fun (_ : T) => f)
  {{ A }}
    xp; xf
  {{ B }} // env.
Proof.
  intros.
  eapply CompileSeq; eauto.
Qed.

Lemma CompileBefore : forall T env A B (C : T -> _) p x1 x2,
  EXTRACT Ret tt
  {{ A }}
    x1
  {{ fun _ => B }} // env ->
  EXTRACT p
  {{ B }}
    x2
  {{ C }} // env ->
  EXTRACT p
  {{ A }}
    x1; x2
  {{ C }} // env.
Proof.
  intros.
  eapply extract_equiv_prog with (pr1 := Ret tt;; p).
  eapply bind_left_id.
  eapply CompileSeq; eauto.
Qed.

Lemma CompileAfter : forall T env A B (C : T -> _) p x1 x2,
  EXTRACT p
  {{ A }}
    x1
  {{ B }} // env ->
  (forall r : T,
      EXTRACT Ret tt
      {{ B r }}
        x2
      {{ fun _ => C r }} // env) ->
  EXTRACT p
  {{ A }}
    x1; x2
  {{ C }} // env.
Proof.
  unfold ProgOk.
  intuition subst.

  - find_eapply_lem_hyp ExecFinished_Steps. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFinished.
    forward_solve.
    invc H8; repeat (find_apply_lem_hyp inj_pair2; subst); [ | solve_by_inversion ]; eauto.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H4. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct_pair. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
      invc H0; repeat (find_apply_lem_hyp inj_pair2; subst); solve_by_inversion.

  - find_eapply_lem_hyp ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + eapply Steps_ExecFailed in H4; eauto.
      * forward_solve.
      * unfold is_final; simpl; intuition (subst; eauto).
      * intuition. repeat deex.
        intuition eauto.
    + destruct_pair. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forward_solve.
      invc H10; repeat (find_apply_lem_hyp inj_pair2; subst); solve_by_inversion.

  Unshelve.
  all: auto.
Qed.

Lemma CompileBindRet : forall A B (HA : GoWrapper A)
  vara (a : A) (p : A -> prog B) xp xret X Y Z env,
  EXTRACT (Ret a)
  {{ vara ~>? A * X }}
    xret
  {{ fun ret => vara ~> ret * Y }} // env ->
  EXTRACT (p a)
  {{ vara ~> a * Y }}
    xp
  {{ Z }} // env ->
  EXTRACT (Bind (Ret a) p)
  {{ vara ~>? A * X }}
    xret; xp
  {{ Z }} // env.
Proof.
  intros.
  eapply CompileBefore in H0.
  rewrite bind_left_id.
  eapply H0.
  eapply CompileRet. eapply H.
Qed.

Lemma SetVarBefore : forall T V {Wr : GoWrapper V} env P P' Q var val (p : prog T) x1 x2,
    EXTRACT Ret val
    {{ var ~>? V * P }}
      x1
    {{ fun ret => var ~> ret * P' }} // env ->
    EXTRACT p
    {{ var ~> val * P' }}
      x2
    {{ Q }} // env ->
    EXTRACT p
    {{ var ~>? V * P }}
      x1; x2
    {{ Q }} // env.
Proof.
  intros.
  eapply hoare_weaken.
  eapply CompileBefore.
  eapply CompileRet with (v := val) (var0 := var0).
  eassumption.
  eassumption.
  cancel_go.
  cancel_go.
Qed.

Lemma CompileFreeze : forall n (a : bytes n) env dvar svar F,
    EXTRACT Ret a
    {{ (exists a0, dvar |-> Val (ImmutableBuffer n) a0) * svar ~> a * F }}
      Modify FreezeBuffer ^(dvar, svar)
    {{ fun ret => dvar |-> Val (ImmutableBuffer n) ret * svar ~>? bytes n * F }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  all: contradiction H1; repeat eexists; eauto. econstructor; [ eval_expr; eauto .. ].
Qed.

Lemma CompileSplit1 : forall sz1 sz2 bsz1 bsz2 (e1 : bsz1 * 8 = sz1) (e2 : bsz2 * 8 = sz2) 
                        (buf : immut_word (sz1 + sz2)) env dvar svar F,
    EXTRACT Ret (split1 sz1 sz2 buf : immut_word _)
    {{ dvar ~>? immut_word sz1 * svar ~> buf * F }}
      Modify (SliceBuffer 0 bsz1) ^(dvar, svar)
    {{ fun ret => dvar ~> ret * svar ~> buf * F }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok.
  repeat match goal with
  | [ |- context[@GoWrapper_immut_word ?nbits ?nbytes ?e] ] =>
    ((is_var e; fail 1) || idtac); set (e) in *
  end.
    exec_solve_step.
    exec_solve_step.
    exec_solve_step.
    exec_solve_step.
    repeat eexists.
    econstructor.
    pred_solve.
    match goal with
    | [ |- context[(dvar ~> ?a)%pred] ] => set (val1 := a)
    end.
    match goal with
    | [ |- context[(Mem.upd _ dvar (Val _ ?a))%pred] ] => set (val2 := a)
    end.
    Import EqNotations.
    assert (val1 = rew (Nat.sub_0_r _) in val2).
Admitted.

Lemma CompileIf : forall V varb (b : bool)
  (ptrue pfalse : prog V) xptrue xpfalse F G env,
  EXTRACT ptrue
  {{ varb ~> true * F }}
    xptrue
  {{ fun ret => G ret * varb ~>? bool }} // env ->
  EXTRACT pfalse
  {{ varb ~> false * F }}
    xpfalse
  {{ fun ret => G ret * varb ~>? bool }} // env ->
  EXTRACT (if b then ptrue else pfalse)
  {{ varb ~> b * F }}
    If (Var varb) Then xptrue Else xpfalse EndIf
  {{ fun ret => G ret * varb ~>? bool }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  all : contradiction H3;
    repeat eexists; solve [
    eapply StepIfTrue; eval_expr |
    eapply StepIfFalse; eval_expr].
Qed.

Lemma CompileIfLt :
  forall V vara varb (a b : nat)
    (ptrue pfalse : prog V) xptrue xpfalse F G env,
    EXTRACT ptrue
    {{ vara ~> a * varb ~> b * F }}
      xptrue
    {{ fun ret => G ret }} // env ->
    EXTRACT pfalse
    {{ vara ~> a * varb ~> b * F }}
      xpfalse
    {{ fun ret => G ret }} // env ->
    EXTRACT (if Compare_dec.lt_dec a b then ptrue else pfalse)
    {{ vara ~> a * varb ~> b * F }}
      If (TestE Lt (Var vara) (Var varb)) Then xptrue Else xpfalse EndIf
    {{ fun ret => G ret }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  all : contradiction H3;
    repeat eexists; solve [
    eapply StepIfTrue; eval_expr |
    eapply StepIfFalse; eval_expr].
Qed.

Lemma CompileRead :
  forall env F avar vvar (v0 : valu) a,
    EXTRACT Read a
    {{ vvar ~> v0 * avar ~> a * F }}
      DiskRead vvar avar
    {{ fun ret => vvar ~> ret * avar ~> a * F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok;
    repeat exec_solve_step.
Qed.

Lemma CompileWrite : forall env F avar vvar a v,
  EXTRACT Write a v
  {{ avar ~> a * vvar ~> v * F }}
    DiskWrite avar vvar
  {{ fun _ => avar ~> a * vvar ~> v * F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok;
    repeat exec_solve_step.
Qed.

Lemma CompileSync : forall env F,
  EXTRACT Sync
  {{ F }}
    DiskSync
  {{ fun _ => F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  contradiction H1.
  repeat eexists; eauto.
  econstructor; eauto.
Qed.



Lemma CompileAdd :
  forall env F sumvar avar bvar (a b : nat),
    EXTRACT Ret (a + b)
    {{ sumvar ~>? W * avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Plus) ^(sumvar, avar, bvar)
    {{ fun ret => sumvar ~> ret * avar ~> a * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

Lemma CompileAddInPlace1 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a + b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Plus) ^(avar, avar, bvar)
    {{ fun ret => avar ~> ret * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

(* TODO: make it unnecessary to have all these separate lemmas *)
Lemma CompileAddInPlace2 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a + b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Plus) ^(bvar, avar, bvar)
    {{ fun ret => bvar ~> ret * avar ~> a * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

Lemma CompileAppend :
  forall env F T {Wr: GoWrapper T} (lvar vvar : var) (x : T) xs,
  EXTRACT Ret (x :: xs)
  {{ vvar ~> x * lvar ~> xs * F }}
    Modify AppendOp ^(lvar, vvar)
  {{ fun ret => vvar |-> moved_value (wrap x) * lvar ~> ret * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

Lemma CompileUncons :
  forall env T F G V {Wr: GoWrapper V} (lvar cvar xvar xsvar : var) (l : list V)
    (pnil : prog T) pcons xpnil xpcons,
    EXTRACT pnil
    {{ lvar ~>? (list V) * cvar ~> false * xvar ~>? V * xsvar ~>? (list V) * F }}
      xpnil
    {{ G }} // env ->
    (forall x xs, EXTRACT pcons x xs
             {{ lvar ~>? (list V) * cvar ~> true * xvar ~> x * xsvar ~> xs * F }}
               xpcons
             {{ G }} // env) ->
    EXTRACT match l with
            | [] => pnil
            | x :: xs => pcons x xs
            end
    {{ lvar ~> l * cvar ~>? bool * xvar ~>? V * xsvar ~>? (list V) * F }}
      Modify Uncons ^(lvar, cvar, xvar, xsvar);
      If Var cvar Then xpcons Else xpnil EndIf
    {{ G }} // env.
Proof.
  intros.
  unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  all : match goal with
  | [H : context[step] |- _] =>
    contradiction H;
    repeat eexists;
    solve [
      eapply StepIfTrue; eval_expr |
      eapply StepIfFalse; eval_expr |
      repeat econstructor; [eval_expr; reflexivity..]
    ]
  end.
Qed.

Lemma map_add_okToCancel : forall AT AEQ {T} {Wr : GoWrapper T} var m k (v : T),
  (@piff AT AEQ value (var ~> Map.add k v m)
  (var |-> (Val (AddrMap wrap_type) (Here (Map.add k (wrap' v) (Map.map wrap' m))))))%pred.
Proof.
  intros. split;
  unfold wrap; simpl;
  match goal with
  | [ |- ?P =p=> ?Q ] => replace Q with P; try reflexivity
  end;
  repeat f_equal;
  eauto using MapUtils.addrmap_equal_eq,
    MoreAddrMapFacts.map_add_comm,
    MapUtils.AddrMap.MapFacts.Equal_refl, eq_sym.
Qed.

Hint Extern 1 (okToCancel (?var ~> Map.add ?k ?v ?m)
  (?var |-> (Val (AddrMap wrap_type) (Here (Map.add ?k (wrap' ?v) (Map.map wrap' ?m))))))
  => apply map_add_okToCancel.

Hint Extern 1 (okToCancel 
                 (?var |-> (Val (AddrMap wrap_type) (Here (Map.add ?k (wrap' ?v) (Map.map wrap' ?m)))))
                 (?var ~> Map.add ?k ?v ?m))
  => apply map_add_okToCancel.

Lemma map_remove_okToCancel : forall AT AEQ {T} {Wr : GoWrapper T} var m k,
  (@piff AT AEQ value (var ~> Map.remove k m)
  (var |-> (Val (AddrMap wrap_type) (Here (Map.remove k (Map.map wrap' m))))))%pred.
Proof.
  intros. unfold wrap; simpl; split;
  match goal with
  | [ |- ?P =p=> ?Q ] => replace Q with P; try reflexivity
  end;
  repeat f_equal;
  eauto using MapUtils.addrmap_equal_eq,
    MoreAddrMapFacts.map_remove_comm,
    MapUtils.AddrMap.MapFacts.Equal_refl, eq_sym.
Qed.

Local Hint Extern 1 (okToCancel (?var ~> Map.remove ?k ?m)
  (?var |-> (Val (AddrMap wrap_type) (Here (Map.remove ?k (Map.map wrap' ?m))))))
  => apply map_remove_okToCancel.

Local Hint Extern 1 (okToCancel
                       (?var |-> (Val (AddrMap wrap_type) (Here (Map.remove ?k (Map.map wrap' ?m)))))
                       (?var ~> Map.remove ?k ?m))
  => apply map_remove_okToCancel.


Lemma map_find_some_okToCancel : forall AT AEQ {T} {Wr : GoWrapper T} var m k v,
  Map.find k (Map.map wrap' m) = Some v ->
  (@piff AT AEQ value (var ~> Map.find k m)
  (var |-> Val (Pair Bool wrap_type) (true, v))).
Proof.
  intros. unfold wrap; simpl; split;
  rewrite MapUtils.AddrMap.MapFacts.map_o in H;
  destruct Map.find; simpl in *; congruence.
Qed.

Local Hint Extern 1 (okToCancel (?var ~> Map.find ?k ?m)
  (?var |-> (Val (Pair Bool wrap_type) (true, ?v))))
  => eapply map_find_some_okToCancel.

Local Hint Extern 1 (okToCancel (?var |-> (Val (Pair Bool wrap_type) (true, ?v)))
                                (?var ~> Map.find ?k ?m))
  => eapply map_find_some_okToCancel.


Lemma map_find_none_okToCancel : forall AT AEQ {T} {Wr : GoWrapper T} var m k,
  Map.find k (Map.map wrap' m) = None ->
  (@piff AT AEQ value (var ~> Map.find k m)
  (var |-> Val (Pair Bool wrap_type) (false, default_value' wrap_type))).
Proof.
  intros. unfold wrap; simpl; split;
  rewrite MapUtils.AddrMap.MapFacts.map_o in H;
  destruct Map.find; simpl in *; congruence.
Qed.

Local Hint Extern 1 (okToCancel (?var ~> Map.find ?k ?m)
  (?var |-> (Val (Pair Bool wrap_type) (false, ?v))))
  => eapply map_find_none_okToCancel.

Local Hint Extern 1 (okToCancel (?var |-> (Val (Pair Bool wrap_type) (false, ?v)))
                                (?var ~> Map.find ?k ?m))
  => eapply map_find_none_okToCancel.


Lemma CompileMapAdd : forall env F T {Wr : GoWrapper T} mvar kvar vvar m k (v : T),
  EXTRACT Ret (Go.Map.add k v m)
  {{ mvar ~> m * kvar ~> k * vvar ~> v * F }}
    Go.Modify Go.MapAdd ^(mvar, kvar, vvar)
  {{ fun ret => mvar ~> ret * kvar ~> k * vvar |-> moved_value (wrap v) * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H1.
  repeat econstructor; eauto;
  [ eval_expr; eauto ..].
Qed.


Lemma CompileMapRemove : forall env F T {Wr : GoWrapper T} mvar kvar m k,
  EXTRACT Ret (Go.Map.remove k m)
  {{ mvar ~> m * kvar ~> k * F }}
    Go.Modify Go.MapRemove ^(mvar, kvar)
  {{ fun ret => mvar ~> ret * kvar ~> k * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H1.
  repeat econstructor; eauto;
  [ eval_expr; eauto ..].
Qed.

Lemma CompileMapFind : forall env F T {Wr : GoWrapper T} mvar kvar vvar m k,
  EXTRACT Ret (Go.Map.find k m)
  {{ mvar ~> m * kvar ~> k * vvar ~>? (option T) * F }}
    Go.Modify Go.MapFind ^(mvar, kvar, vvar)
  {{ fun ret => vvar ~> ret * mvar ~> m * kvar ~> k * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok.
  exec_solve_step.
  eval_expr.
  repeat (contradiction H1;
  repeat econstructor;
  [ eval_expr; eauto..]).
Qed.

Lemma map_cardinal_okToCancel : forall AT AEQ {T} {Wr : GoWrapper T} var m,
  (@piff AT AEQ value (var ~> Map.cardinal m)
  (var |-> (Val Num (Map.cardinal (Map.map wrap' m)))))%pred.
Proof.
  intros. unfold okToCancel.
  unfold wrap. simpl.
  match goal with
  | [ |- ?P <=p=> ?Q ] => replace Q with P; try reflexivity
  end.
  repeat f_equal. unfold id.
  eauto using MapUtils.AddrMap.map_cardinal_map_eq.
Qed.

Local Hint Extern 1 (okToCancel (?var ~> Map.cardinal ?m)
  (?var |-> (Val Num (Here (Map.cardinal (Map.map wrap' ?m))))))
  => apply map_cardinal_okToCancel.
Local Hint Extern 1 (okToCancel (?var |-> (Val Num (Map.cardinal (Map.map wrap' ?m))))
                                (?var ~> Map.cardinal ?m))
  => apply map_cardinal_okToCancel.

Lemma CompileMapCardinal : forall env F T {Wr : GoWrapper T} mvar m var,
  EXTRACT Ret (Go.Map.cardinal m)
  {{ var ~>? nat * mvar ~> m * F }}
    Go.Modify Go.MapCardinality ^(mvar, var)
  {{ fun ret => var ~> ret * mvar ~> m * F }} // env.
Proof.
  unfold ProgOk.
  repeat inv_exec_progok.
  - eval_expr.
    repeat eexists; eauto. pred_solve.
  - contradiction H1.
    eval_expr.
    repeat econstructor; [ eval_expr; eauto..].
Qed.

Lemma map_elements_okToCancel : forall AT AEQ {T} {Wr : GoWrapper T} var m,
  @piff AT AEQ value (var ~> Map.elements m)
  (var |-> Val (Slice (Pair Num wrap_type))
         (Here (Map.elements (Map.map wrap' m)))).
Proof.
  intros.
  unfold okToCancel.
  unfold wrap; simpl wrap; simpl wrap'.
  match goal with
  | [ |- ?P <=p=> ?Q ] => replace Q with P; try reflexivity
  end.
  repeat f_equal.
  rewrite MapUtils.AddrMap.map_elements_map_eq.
  reflexivity.
Qed.

Local Hint Extern 1 (okToCancel (?var ~> Map.elements ?k ?m)
                                (?var |-> (Val _ (Here (Map.elements _)))))
  => eapply map_elements_okToCancel : okToCancel.
Local Hint Extern 1 (okToCancel (?var |-> (Val _ (Here (Map.elements _))))
                                (?var ~> Map.elements ?k ?m))
  => eapply map_elements_okToCancel : okToCancel.

Local Hint Extern 1 (okToCancel (?var ~> Map.elements _)
  (?var |-> Val _ (Here
   (MapUtils.AddrMap_List.Raw.map wrap' (MapUtils.AddrMap_List.this _)))))
  => eapply map_elements_okToCancel : okToCancel.
Local Hint Extern 1 (okToCancel (?var |-> Val _ (Here
    (MapUtils.AddrMap_List.Raw.map wrap' (MapUtils.AddrMap_List.this _))))
                                (?var ~> Map.elements _))
  => eapply map_elements_okToCancel : okToCancel.

Lemma CompileMapElements : forall env F T {Wr : GoWrapper T} mvar m var,
  EXTRACT Ret (Go.Map.elements m)
  {{ var ~>? (list (W * T)) * mvar ~> m * F }}
    Go.Modify Go.MapElements ^(mvar, var)
  {{ fun ret => var ~> ret * mvar ~> m * F }} // env.
Proof.
  unfold ProgOk.
  repeat inv_exec_progok.
  - eval_expr.
    repeat eexists; eauto. pred_solve.
  - eval_expr.
    contradiction H1. repeat econstructor.
    eval_expr. eauto.
    eval_expr. eauto.
    eval_expr. eauto.
Qed.

Lemma CompileForLoopBasic : forall L G (L' : GoWrapper L) v loopvar F
                          (n i : W)
                          t0 term
                          env (pb : W -> L -> prog L) xpb nocrash oncrash,
    (forall t x,
        EXTRACT (pb x t)
  {{ loopvar ~> t * v ~> x * term ~> (i + n) * F }}
    xpb
  {{ fun ret => loopvar ~> ret * v ~> S x * term ~> (i + n) * F }} // env)
  ->
  EXTRACT (@ForN_ L G pb i n nocrash oncrash t0)
  {{ loopvar ~> t0 * v ~> i * term ~> (i + n) * F }}
    Go.While (TestE Lt (Var v) (Var term))
      (xpb)
  {{ fun ret => loopvar ~> ret * v ~> (i + n) * term ~> (i + n) * F }} // env.
Proof.
  induction n; intros; simpl.
  - unfold ProgOk. intros.
    rewrite <- plus_n_O in *.
    repeat destruct_pair.
    inv_exec.
    + inv_exec.
      eval_expr.
      inv_exec_progok.
    + inv_exec_progok.
      contradiction H2.
      repeat eexists.
      eapply StepWhileFalse.
      eval_expr.
    + inv_exec_progok.
  - unfold ProgOk. intros.
    destruct_pairs.
    destruct out.
    + (* failure case *)
      intuition try congruence.
      inv_exec.
      {
        inv_exec; eval_expr.
        find_eapply_lem_hyp ExecFailed_Steps. repeat deex.
        find_eapply_lem_hyp Steps_Seq.
        intuition subst; repeat deex.
        { (* failure in body *)
          eapply Prog.XBindFail.
          repeat destruct_pair.
          edestruct H; eauto.
          2 : eapply Steps_ExecFailed; [> | | eauto].
          pred_solve.
          unfold is_final; simpl; intro; subst; eauto.
          edestruct ExecFailed_Steps.
          eapply Steps_ExecFailed; eauto.
          eapply steps_sequence. eauto.
          repeat deex; eauto.
          intuition eauto.
        }
        { (* failure in loop *)
          find_eapply_lem_hyp Steps_ExecFinished.
          edestruct H; eauto. pred_cancel.
          edestruct H3; eauto. simpl in *; repeat deex.
          destruct_pair; simpl in *.
          edestruct (IHn (S i));
            [> | | eapply Steps_ExecFailed; eauto |];
            rewrite ?plus_Snm_nSm; eauto.
          intuition eauto.
        }
      }
      {
        contradiction H3.
        repeat eexists.
        eapply StepWhileTrue.
        eval_expr.
      }
    + (* finished case *)
      inv_exec. inv_exec; eval_expr. subst_definitions.
      intuition try congruence. repeat find_inversion_safe.
      repeat match goal with
      | [H : context[Init.Nat.add _ (S _)] |- _] =>
          (rewrite <- plus_Snm_nSm in H || setoid_rewrite <- plus_Snm_nSm in H)
      end.
      setoid_rewrite <- plus_Snm_nSm.
      destruct_pairs.
      find_eapply_lem_hyp ExecFinished_Steps.
      find_eapply_lem_hyp Steps_Seq.
      intuition; repeat deex; try discriminate.
      repeat find_eapply_lem_hyp Steps_ExecFinished.
      edestruct H; eauto; eauto.
      forward_solve.
      edestruct (IHn (S i)); eauto.
      forward_solve.
    + (* crashed case *)
      intuition try congruence. find_inversion.
      inv_exec; [> | solve [inversion H3] ].
      inv_exec; eval_expr.
      find_eapply_lem_hyp ExecCrashed_Steps.
      intuition; repeat deex.
      find_eapply_lem_hyp Steps_Seq.
      intuition auto; repeat deex.
      {
        invc H4.
        find_eapply_lem_hyp Steps_ExecCrashed; eauto.
        edestruct H; forward_solve. auto.
      }
      {
        find_eapply_lem_hyp Steps_ExecFinished.
        find_eapply_lem_hyp Steps_ExecCrashed; eauto.
        edestruct H; eauto. pred_cancel.
        repeat match goal with
        | [H : context[Init.Nat.add _ (S _)] |- _] =>
            (rewrite <- plus_Snm_nSm in H || setoid_rewrite <- plus_Snm_nSm in H)
        end.
        edestruct H2; eauto.
        forward_solve.
        repeat deex.
        edestruct IHn; eauto.
        forward_solve.
      }
Qed.


Lemma SetConstBefore : forall T {WrT : GoWrapper T} T' {WrT' : GoWrapper T'} (p : prog T) env xp v v0 A B,
  EXTRACT p {{ v ~> v0 * A }} xp {{ B }} // env ->
  EXTRACT p
    {{ v ~>? T' * A }}
      v <~const (wrap' v0); xp
    {{ B }} // env.
Proof.
  eauto using CompileBefore, CompileConst'.
Qed.

Lemma CompileDup : forall env X (Wr : GoWrapper X) F (var var' : var) x,
  EXTRACT Ret x
  {{ var ~> x * var' ~>? X * F }}
    var' <~dup var
  {{ fun ret => var ~> x * var' ~> ret * F }} // env.
Proof.
  unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H1. eval_expr.
  repeat econstructor;
    [ eval_expr; eauto .. ].
Qed.

Lemma DuplicateBefore : forall T (T' : GoWrapper T) X (X' : GoWrapper X)
  (p : prog T) xp env v v' (x x' : X) A B,
  EXTRACT p {{ v ~> x * v' ~> x * A }} xp {{ B }} // env ->
  EXTRACT p
    {{ v ~> x' * v' ~> x * A }}
      v <~dup v'; xp
    {{ B }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H2.
  repeat eexists; eauto.
  do 2 econstructor; solve [eval_expr; eauto].
Qed.

Lemma AddInPlaceLeftBefore : forall T (T' : GoWrapper T) (p : prog T) B xp env
  va a v x F,
  EXTRACT p {{ v ~> (x + a) * va ~> a * F }} xp {{ B }} // env ->
  EXTRACT p
  {{ v ~> x * va ~> a * F }}
    Go.Modify (Go.ModifyNumOp Plus) ^(v, v, va); xp
  {{ B }} // env.
Proof.
  intros.
  eapply CompileBefore; eauto.
  eapply hoare_weaken.
  eapply CompileRet with (T := nat) (var0 := v).
  eapply hoare_weaken_post; [ | eapply CompileAddInPlace1 with (avar := v) (bvar := va) ]; cancel_go.
  all: cancel_go.
Qed.

Lemma AddInPlaceLeftAfter : forall T (T' : GoWrapper T) (p : prog T) A xp env
  va a v x F,
  EXTRACT p {{ A }} xp {{ fun ret => F ret * v ~> x * va ~> a }} // env ->
  EXTRACT p
  {{ A }}
    xp; Go.Modify (Go.ModifyNumOp Plus) ^(v, v, va)
  {{ fun ret => F ret * v ~> (x + a) * va ~> a }} // env.
Proof.
  intros.
  eapply CompileAfter; eauto.
  intros.
  eapply hoare_weaken_post; [ | eapply CompileRet with (var0 := v) (v := x + a) ].
  cancel_go.
  eapply hoare_weaken.
  eapply CompileAddInPlace1 with (avar := v) (bvar := va).
  all: cancel_go.
Qed.

Lemma CompileFor : forall L G (L' : GoWrapper L) loopvar F
                          v vn (n i : W)
                          t0 env (pb : W -> L -> prog L) xpb nocrash oncrash,
    (forall t x v term one,
        EXTRACT (pb x t)
  {{ loopvar ~> t * v ~> x * term ~> (i + n) * one ~> 1 * vn ~> n * F }}
    xpb v term one
  {{ fun ret => loopvar ~> ret * v ~> x * term ~> (i + n) * one ~> 1 * vn ~> n * F }} // env)
  ->
  EXTRACT (@ForN_ L G pb i n nocrash oncrash t0)
  {{ loopvar ~> t0 * v ~> i * vn ~> n * F }}
    Declare Num (fun one => (
      one <~const (wrap' 1);
      Declare Num (fun term => (
        Go.Modify (Go.DuplicateOp) ^(term, v);
        Go.Modify (Go.ModifyNumOp Go.Plus) ^(term, term, vn);
        Go.While (TestE Lt (Var v) (Var term)) (
          xpb v term one;
          Go.Modify (Go.ModifyNumOp Go.Plus) ^(v, v, one)
        )
      ))
    ))
  {{ fun ret => loopvar ~> ret * v |->? * vn |->? * F }} // env.
Proof.
  intros.
  eapply CompileDeclare with (Wr := GoWrapper_Num). intro one.
  eapply hoare_strengthen_pre; [>
  | eapply SetConstBefore; eauto ].
  cancel_go.
  eapply CompileDeclare with (Wr := GoWrapper_Num). intro term.
  eapply hoare_strengthen_pre; [>
  | eapply DuplicateBefore with (x' := 0) (x := i); eauto].
  cancel_go.
  eapply hoare_strengthen_pre; [>
  | eapply AddInPlaceLeftBefore with (a := n) (x := i); eauto ].
  cancel_go.
  eapply hoare_weaken; [>
    eapply CompileForLoopBasic with (t0 := t0) (loopvar := loopvar)
  | cancel_go..].
  intros.
  eapply hoare_weaken_post; [>
  | eapply AddInPlaceLeftAfter with (a := 1) (x := x); eauto].
  rewrite Nat.add_1_r.
  cancel_go.
  eapply hoare_weaken; [>
    eapply H | cancel_go..].
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

(* TODO: support passing arguments by reference *)
Record ProgFunctionSig :=
  {
    FRet : WrappedType;
    FArgs : list WrappedType;
  }.

Fixpoint arg_func_type (args : list WrappedType) T :=
  match args with
  | [] => T
  | arg :: args' => arg.(WrType) -> arg_func_type args' T
  end.

Definition prog_function_type (sig : ProgFunctionSig) :=
  arg_func_type sig.(FArgs) (prog sig.(FRet).(WrType)).

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

Fixpoint do_call {args ret} : arg_func_type args ret -> arg_tuple args -> ret :=
  match args return arg_func_type args ret -> arg_tuple args -> ret with
  | [] => fun f _ => f
  | arg :: args' => fun f argvals =>
                     let '(argval, argvals') := argvals in
                     @do_call args' ret (f argval) argvals'
  end.

Fixpoint args_pre args : forall (argvars : n_tuple (length args) var) (argvals : arg_tuple args), pred :=
  match args return forall (argvars : n_tuple (length args) var) (argvals : arg_tuple args), pred with
  | [] => fun _ _ => emp
  | arg :: args' => fun argvars argvals =>
                     let '(argvar, argvars') := argvars in
                     let '(argval, argvals') := argvals in
                     (argvar ~> argval * args_pre args' argvars' argvals')%pred
  end.

Fixpoint args_post args : forall (argvars : n_tuple (length args) var), pred :=
  match args return forall (argvars : n_tuple (length args) var), pred with
  | [] => fun _ => emp
  | arg :: args' => fun argvars =>
                     let '(argvar, argvars') := argvars in
                     (argvar ~>? arg.(WrType) * args_post args' argvars')%pred
  end.

Fixpoint params_pre args n : forall (argvals : arg_tuple args), pred :=
  match args return forall (argvals : arg_tuple args), pred with
  | [] => fun _ => emp
  | arg :: args' => fun argvals =>
                     let '(argval, argvals') := argvals in
                     (n ~> argval * params_pre args' (S n) argvals')%pred
  end.

Fixpoint params_post args n : pred :=
  match args with
  | [] => emp
  | arg :: args' => (n ~>? arg.(WrType) * params_post args' (S n))%pred
  end.


Polymorphic Definition prog_func_call_lemma (sig : ProgFunctionSig) (name : String.string) (src : prog_function_type sig) env :=
  forall retvar (argvars : n_tuple (length sig.(FArgs)) var) F,
    argval_foralls
      sig.(FArgs)
      (fun argvals => EXTRACT do_call src argvals
       {{ retvar ~>? sig.(FRet).(WrType) * args_pre sig.(FArgs) argvars argvals * F }}
         Call (S (length sig.(FArgs))) name (retvar, argvars)
       {{ fun retval => retvar ~> retval * args_post sig.(FArgs) argvars * F }} // env).

Fixpoint to_list {T n} : n_tuple n T -> list T :=
  match n with
  | 0 => fun _ => []
  | S n' => fun ts =>
             let '(t, ts') := ts in
             t :: to_list ts'
  end.

Fixpoint wrap_all args : arg_tuple args -> n_tuple (length args) value :=
  match args return arg_tuple args -> n_tuple (length args) value with
  | [] => fun _ => tt
  | arg :: args' => fun argvals =>
                     let '(argval, argvals') := argvals in
                     (wrap argval, wrap_all args' argvals')
  end.

(* Somehow, all of the following proofs should have made much more use of separation logic *)

Lemma args_pre_notin :
  forall args argvars argvals F s v0,
    (v0 |->? * args_pre args argvars argvals * F)%pred (mem_of s) ->
    ~ In v0 (to_list argvars).
Proof.
  induction args; intuition.
  destruct argvars, argvals.
  simpl in *.
  destruct H0; subst.
  - eapply pimpl_apply in H.
    eapply ptsto_conflict_F with (a := v0) in H; auto.
    cancel_go.
  - eapply pimpl_apply in H.
    eapply IHargs with (argvals := a0); eauto.
    cancel_go.
Qed.

Lemma args_pre_nodup :
  forall args argvars argvals F s,
    (args_pre args argvars argvals * F)%pred (mem_of s) ->
    NoDup (to_list argvars).
Proof.
  induction args; intros.
  - constructor.
  - destruct argvars, argvals. simpl in *. constructor.
    + eapply args_pre_notin; eauto.
      pred_cancel.
    + eapply IHargs.
      eapply pimpl_apply in H.
      eapply ptsto_delete with (a := v) in H.
      rewrite <- remove_delete in H.
      2: cancel_go.
      eauto.
Qed.

Lemma collect_notin_remove :
  forall n (v0 : var) (vars : n_tuple n var) (vals : n_tuple n value) (s : locals),
    ~ In v0 (to_list vars) ->
    collect (map_nt (fun k : VarMap.key => VarMap.find (elt:=value) k s) vars) = Some vals ->
    collect (map_nt (fun k : VarMap.key => VarMap.find (elt:=value) k (VarMap.remove (elt:=value) v0 s)) vars)
    = Some vals.
Proof.
  induction n; intros.
  - eval_expr.
  - eval_expr_step.
    eval_expr_step.
    eval_expr_step.
    eapply IHn with (v0 := v0) in H2; eauto.
    rewrite VarMapFacts.remove_neq_o in * by intuition.
    eval_expr.
Qed.

Lemma collect_args_pre:
  forall args (argvars : n_tuple (Datatypes.length args) var) (argvals : arg_tuple args)
    (argvals' : n_tuple (Datatypes.length args) value) F s, 
    (args_pre args argvars argvals * F)%pred (mem_of s) ->
    collect (map_nt (fun k : VarMap.key => VarMap.find (elt:=value) k s) argvars) = Some argvals' ->
    argvals' = wrap_all args argvals.
Proof.
  induction args; intros.
  - destruct argvals'. reflexivity.
  - eval_expr.
    extract_var_val.
    eval_expr.
    f_equal.
    generalize H; intros.
    eapply pimpl_apply in H0.
    eapply args_pre_notin with (v0 := v0) in H0.
    2: cancel_go.
    eapply pimpl_apply in H.
    eapply ptsto_delete with (a := v0) in H.
    2: cancel_go.
    rewrite <- remove_delete in H.
    eapply IHargs; eauto.

    eapply collect_notin_remove; eauto.
Qed.

Lemma update_args:
  forall args (argvars : n_tuple (Datatypes.length args) var)
    (argvals : arg_tuple args)
    (argvals' : n_tuple (Datatypes.length args) value)
    (F : Pred.pred) (s : VarMap.t value)
    (t : VarMap.t value),
    update_many argvars (wrap_all args argvals) (map_nt SetTo argvals') s = Some t ->
    (args_pre args argvars argvals ✶ F)%pred (mem_of s) ->
    (args_post args argvars ✶ F)%pred (mem_of t).
Proof.
  induction args; intros.
  - eval_expr.
  - eval_expr.
    pred_solve.
    eapply pimpl_apply in H0.
    eapply ptsto_delete with (a := v) in H0. rewrite <- remove_delete in H0.
    2: cancel_go.
    eapply IHargs in H0; eauto.
    (* TODO *)
Admitted.

Ltac fold_pred_apply :=
  repeat match goal with
         | [ |- ?P ?m ] => change (pred_apply m P)
         | [ H : ?P ?m |- _ ] => change (pred_apply m P) in H
         end.

Polymorphic Lemma extract_prog_func_call :
  forall sig name src env,
    forall body ss,
      (argval_foralls sig.(FArgs)
                      (fun argvals =>
                         EXTRACT do_call src argvals
                         {{ 0 ~>? sig.(FRet).(WrType) * params_pre sig.(FArgs) 1 argvals }}
                           body
                         {{ fun ret => 0 ~> ret * params_post sig.(FArgs) 1 }} // env)) ->
      StringMap.find name env = Some {|
                                    NumParamVars := S (length sig.(FArgs));
                                    ParamVars := (@wrap_type _ sig.(FRet).(Wrapper),
                                                  map_nt (fun WT => @wrap_type _ (Wrapper WT)) (tupled sig.(FArgs)));
                                    Body := body;
                                    body_source := ss;
                                  |} ->
      prog_func_call_lemma sig name src env.
Proof.
  unfold prog_func_call_lemma.
  intros sig name src env body ss Hex Henv retvar argvars F.
  apply argval_inst'; intros.
  apply argval_inst with (argvals := argvals) in Hex.
  intro.
  intros.
  intuition subst.
  - find_eapply_lem_hyp ExecFinished_Steps.
    find_eapply_lem_hyp Steps_runsto; [ | econstructor ].
    invc H0.
    find_eapply_lem_hyp runsto_Steps.
    find_eapply_lem_hyp Steps_ExecFinished.
    find_rewrite.
    find_inversion_safe.
    subst_definitions. unfold sel in *. simpl in *. unfold ProgOk in *.
    repeat eforward Hex.
    forward Hex.
    shelve.
    forward_solve.
    simpl in *.
    do 2 eexists.
    intuition eauto.
    eval_expr.
    find_apply_lem_hyp inj_pair2.
    eval_expr.
    pred_solve.
    fold_pred_apply.
    rewrite sep_star_comm.
    apply sep_star_assoc.
    rewrite sep_star_comm in H.
    apply sep_star_assoc in H.
    apply sep_star_comm in H.
    eapply update_args; eauto.
    assert (n0 = wrap_all (FArgs sig) argvals) by (eapply collect_args_pre; eauto); subst.
    eassumption.

  - find_eapply_lem_hyp ExecCrashed_Steps.
    repeat deex.
    invc H1; [ solve [ invc H2 ] | ].
    invc H0.
    find_rewrite.
    eval_expr.
    find_apply_lem_hyp inj_pair2.
    eval_expr.
    assert (exists bp', (Go.step env)^* (d, callee_s, body) (final_disk, x, bp') /\ x0 = InCall s (S (length sig.(FArgs))) (retvar, argvars) bp').
    {
      remember callee_s.
      clear callee_s Heqt.
      generalize H3 H2. clear. intros.
      prep_induction H3; induction H3; intros; subst.
      - find_inversion.
        eauto using rt1n_refl.
      - invc H0; repeat (find_eapply_lem_hyp inj_pair2; subst).
        + destruct st'.
          forwardauto IHclos_refl_trans_1n; deex.
          eauto using rt1n_front.
        + invc H3. invc H2. invc H.
    }
    deex.
    eapply Steps_ExecCrashed in H5.
    unfold ProgOk in *.
    repeat eforward Hex.
    forward Hex.
    shelve.
    forward_solve.
    invc H2. trivial.
  - find_eapply_lem_hyp ExecFailed_Steps.
    repeat deex.
    invc H1.
    + contradiction H3.
      destruct x. repeat eexists.
      match goal with
      | [ H : _ = Some ?spec |- _ ] => set spec in *
      end.
      eapply StepStartCall with (spec := f); eauto.
      (*
      eval_expr; reflexivity.
      eval_expr.

      Unshelve.
      eval_expr; pred_solve; auto.
      subst_definitions.
      eval_expr; pred_solve; auto.

    + invc H2.
      rewrite Henv in H8.
      eval_expr.
      assert (exists bp', (Go.step env)^* (d, callee_s, body) (r, l, bp') /\ x0 = InCall s 2 ^(avar, bvar) bp').
      {
        remember callee_s.
        clear callee_s Heqt.
        generalize H4 H0 H3. clear. intros.
        prep_induction H4; induction H4; intros; subst.
        - find_inversion.
          eauto using rt1n_refl.
        - invc H0; repeat (find_eapply_lem_hyp inj_pair2; subst).
          + destruct st'.
            forwardauto IHclos_refl_trans_1n; deex.
            eauto using rt1n_front.
          + invc H4. contradiction H1. auto. invc H.
      }
      deex.
      eapply Steps_ExecFailed in H6.
      unfold ProgOk in *.
      repeat eforward Hex.
      forward Hex. shelve.
      solve [forward_solve].

      intro.
      unfold is_final in *; simpl in *; subst.
      contradiction H3.
      subst_definitions.
      apply Steps_ExecFinished in H6.
      unfold ProgOk in *.
      repeat eforward Hex.
      forward Hex. shelve.
      forward_solve.
      eval_expr.
      repeat eexists. eapply StepEndCall; simpl; eauto.
      eval_expr; reflexivity.
      eval_expr; reflexivity.
      eval_expr; reflexivity.

      intuition.
      contradiction H3.
      repeat deex. repeat econstructor; eauto.
      eapply StepInCall with (np := 2); eassumption.

  Unshelve.
  * subst_definitions. eval_expr. pred_solve. auto.
  * exact hm.
  * eval_expr. pred_solve. auto.
*)
Admitted.

Lemma CompileSplit :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (p : A * B),
    EXTRACT Ret tt
    {{ avar ~>? A * bvar ~>? B * pvar ~> p * F }}
      Modify SplitPair ^(pvar, avar, bvar)
    {{ fun _ => avar ~> fst p * bvar ~> snd p * pvar |-> moved_value (wrap p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H1.
  repeat econstructor;
  [ eval_expr; eauto ..].
Qed.

Lemma CompileFst :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (p : A * B),
    EXTRACT Ret (fst p)
    {{ avar ~>? A * bvar ~>? B * pvar ~> p * F }}
      Modify SplitPair ^(pvar, avar, bvar)
    {{ fun ret => avar ~> ret * bvar ~> snd p * pvar |-> moved_value (wrap p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  eval_expr.
  contradiction H1.
  repeat econstructor;
  [ eval_expr; eauto ..].
Qed.

Lemma CompileSnd :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (p : A * B),
    EXTRACT Ret (snd p)
    {{ avar ~>? A * bvar ~>? B * pvar ~> p * F }}
      Modify SplitPair ^(pvar, avar, bvar)
    {{ fun ret => avar ~> fst p * bvar ~> ret * pvar |-> moved_value (wrap p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  eval_expr.
  contradiction H1.
  repeat econstructor;
  [ eval_expr; eauto ..].
Qed.

Lemma CompileJoin :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar (a : A) (b : B) F,
    EXTRACT Ret (a, b)
    {{ avar ~> a * bvar ~> b * pvar ~>? (A * B)%type * F }}
      Modify JoinPair ^(pvar, avar, bvar)
    {{ fun ret => avar |-> moved_value (wrap a) * bvar |-> moved_value (wrap b) * pvar ~> ret * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  eval_expr.
  contradiction H1.
  repeat econstructor;
  [eval_expr; eauto..].
Qed.

Hint Constructors source_stmt.

Lemma CompileRetOptionSome : forall env B {HB: GoWrapper B} {D : DefaultValue B}
  avar bvar pvar (b : B) (p : bool * B) F,
  EXTRACT Ret (Some b)
  {{ avar ~> true * bvar ~> b * pvar ~> p * F }}
    Modify JoinPair ^(pvar, avar, bvar)
  {{ fun ret => pvar ~> ret *
                avar |-> moved_value (wrap true) *
                bvar |-> moved_value (wrap b) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  eval_expr.
  contradiction H1.
  repeat econstructor;
  [eval_expr; eauto..].
Qed.

Lemma option_none_okToCancel : forall AT AEQ {T} {HT : GoWrapper T} {D : DefaultValue T} var,
  @piff AT AEQ value (var ~> None) (var |-> Val (Pair Bool wrap_type) (false, wrap' zeroval)).
Proof.
  intros.
  unfold wrap. simpl.
  rewrite default_zero' by apply default_zero.
  reflexivity.
Qed.

Local Hint Extern 1 (okToCancel (?var ~> None)
  (?var |-> Val (Pair Bool wrap_type) (false, wrap' zeroval)))
  => apply option_none_okToCancel.
Local Hint Extern 1 (okToCancel (?var |-> Val (Pair Bool wrap_type) (false, wrap' zeroval))
                                (?var ~> None))
  => apply option_none_okToCancel.

Lemma CompileRetOptionNone : forall env B {HB: GoWrapper B} {D : DefaultValue B}
  avar pvar (p : bool * B) F,
  EXTRACT Ret None
  {{ avar ~> false * pvar ~> p * F }}
    Declare wrap_type (fun bvar =>
      Modify JoinPair ^(pvar, avar, bvar)
    )
  {{ fun ret => pvar ~> ret *
                avar |-> moved_value (wrap false) * F }} // env.
Proof.
  intros.
  eapply CompileDeclare. intros.
  unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  eval_expr.
  contradiction H1.
  repeat econstructor;
  [eval_expr; eauto..].
Qed.

Lemma CompileMatchOption : forall env B {HB : GoWrapper B} X {HX : GoWrapper X} {D : DefaultValue B}
  ovar avar bvar xvar (o : option B)
  (pnone : prog X) xpnone (psome : B -> prog X) xpsome (F : pred) C,
  (forall (b : B),
  EXTRACT (psome b)
  {{ avar ~> true * bvar ~> b * ovar |-> moved_value (wrap o) * F }}
    xpsome
  {{ fun ret => xvar ~> ret * avar ~>? bool * bvar ~>? B * ovar ~>? option B * C }} // env) ->
  EXTRACT pnone
  {{ avar ~> false * bvar ~> zeroval * ovar |-> moved_value (wrap o) * F }}
    xpnone
  {{ fun ret => xvar ~> ret * avar ~>? bool * bvar ~>? B * ovar ~>? option B * C }} // env ->
  EXTRACT (match o with
           | None => pnone
           | Some b => psome b
           end)
  {{ ovar ~> o * avar ~>? bool * bvar ~>? B * F }}
    Modify SplitPair ^(ovar, avar, bvar) ;
    If Var avar Then xpsome Else xpnone EndIf
  {{ fun ret => xvar ~> ret * avar ~>? bool * bvar ~>? B * ovar ~>? option B * C }} // env.
Proof.
  intros.
  eapply extract_equiv_prog with (pr1 := Bind (Ret tt) (fun _ => _)).
  rewrite bind_left_id. apply prog_equiv_equivalence.
  eapply CompileSeq.
  {
    eapply hoare_strengthen_pre;
    [ | eapply CompileSplit with (p := match o with
                                       | None => (false, zeroval)
                                       | Some b => (true, b)
                                       end)].
    eval_expr; unfold wrap; cancel_go.
    erewrite <- default_zero' by apply default_zero. reflexivity.
  }
  destruct o; simpl in *.
  + unfold ProgOk.
    inv_exec_progok;
      repeat exec_solve_step.
    contradiction H3.
    repeat eexists. apply StepIfTrue. eval_expr.
  + erewrite <- default_zero' in * by apply default_zero.
    unfold ProgOk.
    inv_exec_progok; repeat exec_solve_step.
    contradiction H3.
    repeat eexists. apply StepIfFalse. eval_expr.
Qed.

Arguments nth_var : simpl never.
