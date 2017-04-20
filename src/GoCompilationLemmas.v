Require Import Eqdep.
Require Import ProofIrrelevance Omega.
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

Lemma CompileInitSliceWithCapacity : forall T {Wr: GoWrapper T} env A (v : Go.var) n,
  EXTRACT Ret []
  {{ v ~>? list T * A }}
    Go.Modify (Go.InitSliceWithCapacity n) ^(v)
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

Lemma bind_f : forall A B C (a : A) (f : A -> B) (g : B -> prog C),
    prog_equiv (x <- Ret (f a); g x) (x' <- Ret a; g (f x')).
Proof.
  intros.
  rewrite ?bind_left_id.
  reflexivity.
Qed.

Instance GoWrapper_eq_rect A (x : A) P y (e : x = y) {Wr : GoWrapper (P y)} : GoWrapper (P x) := {}.
  - exact wrap_type.
  - intros.
    rewrite e in X.
    apply wrap'; assumption.
  - simpl; intros.
    find_apply_lem_hyp wrap_inj.
    find_apply_lem_hyp eq_rect_inj.
    assumption.
Defined.

Lemma CompileEqRect : forall A x P p y {Wr : GoWrapper (P y)} e rvar F xp env,
    EXTRACT Ret p
    {{ (exists v, rvar |-> Val (@wrap_type _ (GoWrapper_eq_rect A x P y e)) v) * F }}
      xp
    {{ fun ret => rvar |-> @wrap _ (GoWrapper_eq_rect A x P y e) ret * F }} // env ->
    EXTRACT Ret (@eq_rect A x P p y e)
    {{ rvar ~>? P y * F }}
      xp
    {{ fun ret => rvar ~> ret * F }} // env.
Proof.
  intros.
  eapply CompileRet'.
  eapply CompileRet in H.
  eapply hoare_weaken.
  apply H.
  rewrite e.
  reflexivity.
  cancel_go.
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
  forall env R T {Wr : GoWrapper T} A B (p : prog R) xp,
    (forall var,
       EXTRACT p
       {{ var |-> Val _ (default_value' wrap_type) * A }}
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

Lemma CompileDeclareWrapDefault :
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
    eapply hoare_weaken; [ apply H | unfold default_value; cancel_go.. ].
    rewrite <- decls_pre_shift.
    reflexivity.
    rewrite decls_post_shift.
    cancel.
Qed.

Lemma source_stmt_many_declares : forall decls cont,
    (forall vars, source_stmt (cont vars)) ->
    source_stmt (many_declares decls cont).
Proof.
  induction decls; eauto; intros.
  destruct a; econstructor; eauto.
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

Lemma CompileBind : forall T T' {H: GoWrapper T} env A B (C : T' -> _) p f xp xf var,
  EXTRACT p
  {{ var ~>? T * A }}
    xp
  {{ fun ret => var ~> ret * B }} // env ->
  (forall (a : T),
    EXTRACT f a
    {{ var ~> a * B }}
      xf
    {{ C }} // env) ->
  EXTRACT Bind p f
  {{ var ~>? T * A }}
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

Lemma CompileBind' : forall T T' env A B (C : T' -> _) p f xp xf,
  EXTRACT p
  {{ A }}
    xp
  {{ B }} // env ->
  (forall (a : T),
    EXTRACT f a
    {{ B a }}
      xf
    {{ C }} // env) ->
  EXTRACT Bind p f
  {{ A }}
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
    + inv_exec. find_eapply_lem_hyp Go.Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct_pair. find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecCrashed; eauto.
      forward_solve.

  - find_eapply_lem_hyp Go.ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex.
    + eapply Go.Steps_ExecFailed in H4; eauto.
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

Lemma CompileDeserializeNum : forall bvar rvar F env (b : immut_word 64),
    EXTRACT Ret (wordToNat b)
    {{ rvar ~>? nat * bvar ~> b * F }}
      Modify DeserializeNum ^(rvar, bvar)
    {{ fun ret => rvar ~> ret * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.
  all : match goal with
        | [H : context[step] |- _] =>
          contradiction H; eval_expr;
            repeat econstructor; [ eval_expr; reflexivity .. ]
        end.
Qed.

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

Lemma CompileFreeze : forall n (a : word n) env dvar svar F,
    Nat.divide 8 n ->
    EXTRACT Ret a
    {{ (exists a0, dvar |-> Val ImmutableBuffer a0) * svar ~> a * F }}
      Modify FreezeBuffer ^(dvar, svar)
    {{ fun ret : immut_word n => dvar ~> ret * svar ~>? word n * F }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  all: contradiction H2; repeat eexists; eauto. econstructor; [ eval_expr; eauto .. ].
Qed.

Import EqNotations.
Lemma rew_fun : forall A (x : A) (P : A -> Type) (Q : A -> Type) (y : A) (e : x = y) (f : Q x -> P x) (p : Q y),
    (rew [fun x => Q x -> P x] e in f) p = rew e in f (rew <- e in p).
Proof.
  intros.
  destruct e.
  simpl.
  f_equal.
Qed.

Lemma rew_fun' : forall A (x : A) (P : Type) (Q : A -> Type) (y : A) (e : x = y) (f : Q x -> P) (p : Q y),
    (rew [fun x => Q x -> P] e in f) p = f (rew <- e in p).
Proof.
  intros.
  destruct e.
  simpl.
  f_equal.
Qed.

Require Import Rec.

Lemma slice_buffer_existT_eq:
  forall (low mid high : W) (buf : immut_word (low + (mid + high))) (l0 : low <= low + mid)
    (l1 : low + mid <= low + (mid + high)),
    existT (fun n : W => word n) (low + mid - low)
           (Rec.middle low (low + mid - low) (low + (mid + high) - (low + mid))
                       (eq_rec (low + (mid + high)) (fun ns : W => word ns) buf
                               (low + (low + mid - low + (low + (mid + high) - (low + mid)))) (slice_buffer_impl_subproof l0 l1))) =
    existT (fun n : W => word n) mid (Rec.middle low mid high buf).
Proof.
  intros low mid high buf l0 l1.
  generalize (slice_buffer_impl_subproof l0 l1).
  unfold eq_rec.
  rewrite ?minus_plus.
  replace (low + (mid + high) - (low + mid)) with high by omega.
  intros.
  repeat f_equal.
  rewrite UIP_refl with (p := e).
  reflexivity.
Qed.

Lemma CompileMiddle : forall low mid high (buf : immut_word (low + (mid + high))) env dvar svar lvar tvar F,
    Nat.divide 8 low -> Nat.divide 8 mid -> Nat.divide 8 high ->
    EXTRACT Ret (Rec.middle low mid high buf : immut_word _)
    {{ dvar ~>? immut_word mid * svar ~> buf * lvar ~> low * tvar ~> (low + mid) * F }}
       Modify SliceBuffer ^(dvar, svar, lvar, tvar)
    {{ fun ret => dvar ~> ret * svar ~> buf * lvar ~> low * tvar ~> (low + mid) * F }} // env.
Proof.
  intros. unfold ProgOk.
  inv_exec_progok.
  - repeat exec_solve_step.
    repeat econstructor.
    pred_solve.
    eapply pimpl_apply with (p := (dvar |-> _ * _)%pred).
    2: apply ptsto_typed_any_upd with (Wr := GoWrapper_immut_word mid); pred_apply; cancel_go.
    cancel_go.
    unfold wrap, wrap_type, wrap', GoWrapper_immut_word.
    match goal with
    | |- _ |-> Val ?t ?a =p=> _ |-> Val ?t ?b =>
      let H := fresh in assert (Val t a = Val t b) as H; [ | rewrite H; reflexivity ]
    end.
    f_equal.
    apply slice_buffer_existT_eq.
  - repeat exec_solve_step.
  - repeat exec_solve_step.
    all : match goal with
          | [H : context[step] |- _] =>
            contradiction H; eval_expr; repeat econstructor
          end.
    eval_expr; reflexivity.
    eval_expr. rewrite slice_buffer_existT_eq. reflexivity.
    contradiction n; eauto using Nat.divide_add_r.
    contradiction n; eauto using Nat.divide_add_r.
    eval_expr; reflexivity.
Qed.

Lemma middle_split1 : forall sz1 sz2 (w : word (sz1 + sz2)),
    split1 sz1 sz2 w = Rec.middle 0 sz1 sz2 w.
Proof.
  reflexivity.
Qed.

Ltac comp_apply H := eapply hoare_weaken; [ eapply H; intros | cancel_go.. ].

Create HintDb divide discriminated.

Import PeanoNat.
Hint Extern 2 (Nat.divide 8 (S (S ?n2))) =>
(exists ((S (S n2)) / 8); reflexivity) : divide.
Hint Resolve Nat.divide_sub_r : divide.
Lemma valulen_divide_8 : Nat.divide 8 valulen.
Proof.
  rewrite valulen_is. exists (valulen_real / 8). reflexivity.
Qed.
Hint Resolve valulen_divide_8 : divide.

Hint Resolve Nat.divide_0_r Nat.divide_add_r Nat.divide_mul_r Nat.divide_refl : divide.

Ltac divisibility := eauto with divide.

Lemma CompileSplit1 : forall sz1 sz2 (buf : immut_word (sz1 + sz2)) env dvar svar F,
    Nat.divide 8 sz1 -> Nat.divide 8 sz2 ->
    EXTRACT Ret (split1 sz1 sz2 buf : immut_word _)
    {{ dvar ~>? immut_word sz1 * svar ~> buf * F }}
      Declare Num (fun vzero =>
        Declare Num (fun vsz1 =>
          (vsz1 <~const (wrap' sz1);
           Modify SliceBuffer ^(dvar, svar, vzero, vsz1))))
    {{ fun ret => dvar ~> ret * svar ~> buf * F }} // env.
Proof.
  intros.
  do 2 (eapply hoare_weaken; [ eapply CompileDeclare with (Wr := GoWrapper_Num); intros | cancel_go..]).
  comp_apply CompileBefore.
  eapply CompileRet with (var0 := var1) (v := sz1).
  comp_apply CompileConst.
  rewrite middle_split1.
  comp_apply CompileMiddle; divisibility.
Qed.

Lemma CompileIf : forall P Q V varb (b : {P} + {Q})
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

Lemma CompileIfBool : forall V varb (b : bool)
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
  intros.
  unfold ProgOk;
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

Lemma CompileIfLt' :
  forall V vara varb (a b : nat)
    (ptrue : _ -> prog V) (pfalse : _ -> prog V) xptrue xpfalse F G env,
    (forall l0, EXTRACT ptrue l0
      {{ vara ~> a * varb ~> b * F }}
        xptrue
      {{ fun ret => G ret }} // env) ->
    (forall r0, EXTRACT pfalse r0
      {{ vara ~> a * varb ~> b * F }}
        xpfalse
      {{ fun ret => G ret }} // env) ->
    EXTRACT (match Compare_dec.lt_dec a b with | left l0 => ptrue l0 | right r0 => pfalse r0 end)
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
  forall env F avar vvar a,
    EXTRACT Read a
    {{ (exists buf, vvar |-> Val Buffer (Here buf)) * avar ~> a * F }}
      DiskRead vvar avar
    {{ fun ret => vvar ~> ret * avar ~> a * F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok;
    repeat exec_solve_step.
  extract_pred_apply_exists.
  repeat econstructor. destruct (r a) eqn:Hm; auto.
  contradiction H1; eval_expr; repeat econstructor; eauto.
Qed.


Lemma okToCancel_bufval : forall bvar n (bval : word n),
  (bvar ~> bval : pred) =p=> (exists bval0, bvar |-> Val Buffer (Here bval0)).
Proof.
  intros.
  apply pimpl_exists_r.
  eexists; intro; intros; apply H.
Qed.

Hint Extern 0 (okToCancel (?bvar ~> ?bval) (exists bval0, ?bvar |-> Val Buffer (Here bval0)))%pred =>
  apply okToCancel_bufval.

Lemma CompileWrite : forall env F avar vvar a (v : immut_word valulen),
  EXTRACT Write a v
  {{ avar ~> a * vvar ~> v * F }}
    DiskWrite avar vvar
  {{ fun _ => avar ~> a * vvar ~> v * F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok;
    repeat exec_solve_step.
  eval_expr.
  repeat extract_var_val.
  eval_expr.
  find_apply_lem_hyp inj_pair2.
  eval_expr.
  exec_solve_step.
  destruct (r a) eqn:Ha.
  contradiction H1. eval_expr; repeat econstructor.
  cbv [wrap wrap' GoWrapper_word] in He0.
  eassumption.
  eassumption.
  cbn. eassumption.
  eauto.
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


Lemma CompileSubtract :
  forall env F sumvar avar bvar (a b : nat),
    EXTRACT Ret (a - b)
    {{ sumvar ~>? W * avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Minus) ^(sumvar, avar, bvar)
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

Lemma CompileSubtractInPlace1 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a - b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Minus) ^(avar, avar, bvar)
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

Lemma CompileSubtractInPlace2 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a - b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Minus) ^(bvar, avar, bvar)
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

Lemma CompileMultiply :
  forall env F rvar avar bvar (a b : nat),
    EXTRACT Ret (a * b)
    {{ rvar ~>? W * avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Times) ^(rvar, avar, bvar)
    {{ fun ret => rvar ~> ret * avar ~> a * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

Lemma CompileMultiplyInPlace1 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a * b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Times) ^(avar, avar, bvar)
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

Lemma CompileMultiplyInPlace2 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a * b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Times) ^(bvar, avar, bvar)
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


Lemma CompileDivide :
  forall env F rvar avar bvar (a b : nat),
    EXTRACT Ret (a / b)
    {{ rvar ~>? W * avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Divide) ^(rvar, avar, bvar)
    {{ fun ret => rvar ~> ret * avar ~> a * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

Lemma CompileDivideInPlace1 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a / b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Divide) ^(avar, avar, bvar)
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

Lemma CompileDivideInPlace2 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a / b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Divide) ^(bvar, avar, bvar)
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


Lemma CompileMod :
  forall env F rvar avar bvar (a b : nat),
    EXTRACT Ret (a mod b)
    {{ rvar ~>? W * avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Modulo) ^(rvar, avar, bvar)
    {{ fun ret => rvar ~> ret * avar ~> a * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  inv_exec_progok;
    repeat exec_solve_step.

  contradiction H1.
  eval_expr.
  repeat econstructor.
  all: eval_expr; [reflexivity].
Qed.

Lemma CompileModInPlace1 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a mod b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Modulo) ^(avar, avar, bvar)
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

Lemma CompileModInPlace2 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a mod b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Modulo) ^(bvar, avar, bvar)
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

Lemma CompileMove : forall env X (Wr : GoWrapper X) F (var var' : var) x,
  EXTRACT Ret x
  {{ var ~> x * var' ~>? X * F }}
    var' <~move var
  {{ fun ret => var |-> moved_value (wrap x) * var' ~> ret * F }} // env.
Proof.
  unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H1. eval_expr.
  repeat econstructor;
    [ eval_expr; eauto .. ].
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
    {{ v ~>? X * v' ~> x * A }}
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
  {{ fun ret => loopvar ~> ret * v ~>? W * vn ~>? W * F }} // env.
Proof.
  intros.
  eapply CompileDeclare with (Wr := GoWrapper_Num). intro one.
  eapply hoare_strengthen_pre; [>
  | eapply SetConstBefore; eauto ].
  cancel_go.
  eapply CompileDeclare with (Wr := GoWrapper_Num). intro term.
  eapply hoare_strengthen_pre; [>
  | eapply DuplicateBefore with (x := i); eauto].
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

Fixpoint do_call {args ret} : arg_func_type args ret -> arg_tuple args -> ret :=
  match args return arg_func_type args ret -> arg_tuple args -> ret with
  | [] => fun f _ => f
  | arg :: args' => fun f argvals =>
                     let '(argval, argvals') := argvals in
                     @do_call args' ret (f argval) argvals'
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
       {{ fun retval => retvar ~> retval * args_post sig.(FArgs) argvars argvals * F }} // env).

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
    (args_post args argvars argvals ✶ F)%pred (mem_of t).
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

Lemma CompileSplit' :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (a : type_denote (@wrap_type _ HA)) (b : type_denote (@wrap_type _ HB)),
    EXTRACT Ret tt
    {{ avar ~>? A * bvar ~>? B * pvar |-> Val (Pair _ _) (a, b) * F }}
      Modify SplitPair ^(pvar, avar, bvar)
    {{ fun _ => avar |-> Val _ a * bvar |-> Val _ b * pvar |-> moved_value (Val (Pair _ _) (a, b)) * F }} // env.
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

Lemma CompileFst' :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar pvar F (p : A * B),
    EXTRACT Ret (fst p)
    {{ avar ~>? A * pvar ~> p * F }}
      Modify PairFst ^(pvar, avar)
    {{ fun ret => avar ~> ret * pvar ~> (@moved_value' _ (wrap' (fst p)), snd p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok.

  (* This seems messy because of the re-wrapping of [fst p].. *)
Admitted.

Lemma CompileSnd' :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} bvar pvar F (p : A * B),
    EXTRACT Ret (snd p)
    {{ bvar ~>? B * pvar ~> p * F }}
      Modify PairSnd ^(pvar, bvar)
    {{ fun ret => bvar ~> ret * pvar ~> (fst p, @moved_value' _ (wrap' (snd p))) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok.

  (* This seems messy because of the re-wrapping of [snd p].. *)
Admitted.

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

Lemma CompileSplitUnit :
  forall env A {HA : GoWrapper A} avar pvar (a : A * unit) F,
    EXTRACT Ret (fst a)
    {{ avar ~>? A * pvar ~> a * F }}
      Declare (@wrap_type _ GoWrapper_unit) (fun uvar =>
        Modify SplitPair ^(pvar, avar, uvar)
      )
    {{ fun ret => avar ~> ret * pvar ~>? (A * unit) * F }} // env.
Proof.
  intros.
  eapply CompileDeclare. intros.
  eapply hoare_weaken.
  eapply CompileFst.
  all : cancel_go.
Qed.

Lemma CompileJoinUnit :
  forall env A {HA : GoWrapper A} avar pvar (a : A) F,
    EXTRACT Ret ^(a)
    {{ avar ~> a * pvar ~>? (A * unit) * F }}
      Declare (@wrap_type _ GoWrapper_unit) (fun uvar =>
        Modify JoinPair ^(pvar, avar, uvar)
      )
    {{ fun ret => avar |-> moved_value (wrap a) * pvar ~> ret * F }} // env.
Proof.
  intros.
  eapply CompileDeclare. intros.
  eapply hoare_weaken.
  eapply CompileJoin.
  all : cancel_go.
Qed.

Hint Constructors source_stmt.

Lemma CompileRetOptionSome : forall env B {HB: GoWrapper B}
  avar bvar pvar (b : B) F,
  EXTRACT Ret (Some b)
  {{ avar ~> true * bvar ~> b * pvar ~>? (bool * B) * F }}
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

Lemma CompileRetOptionNone : forall env B {HB: GoWrapper B}
  avar pvar F,
  EXTRACT Ret None
  {{ avar ~> false * pvar ~>? (bool * B) * F }}
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
  contradiction H1.
  repeat econstructor;
  [eval_expr; eauto..].
Qed.

Lemma CompileIsSome : forall T {W : GoWrapper T} ovar (o : option T) varr F env,
  EXTRACT (Ret (is_some o))
  {{ ovar ~> o * varr ~>? bool * F }}
    Modify PairFst ^(ovar, varr)
  {{ fun ret => varr ~> ret * ovar ~> o * F }} // env.
Proof.
  intros.
  unfold ProgOk.
  inv_exec_progok;
    repeat exec_solve_step.
  contradiction H1.
  repeat econstructor;
    [ eval_expr; eauto.. ].
  contradiction H1.
  repeat econstructor;
    [ eval_expr; eauto.. ].
Qed.

Lemma CompileMatchOption : forall env B {HB : GoWrapper B} X {HX : GoWrapper X}
  ovar avar bvar xvar (o : option B)
  (pnone : prog X) xpnone (psome : B -> prog X) xpsome (F : pred) C,
  (forall (b : B),
  EXTRACT (psome b)
  {{ avar ~> true * bvar ~> b * ovar |-> moved_value (wrap o) * F }}
    xpsome
  {{ fun ret => xvar ~> ret * avar ~>? bool * bvar ~>? B * ovar ~>? option B * C ret }} // env) ->
  EXTRACT pnone
  {{ avar ~> false * bvar |-> default_value (@wrap_type _ HB) * ovar |-> moved_value (wrap o) * F }}
    xpnone
  {{ fun ret => xvar ~> ret * avar ~>? bool * bvar ~>? B * ovar ~>? option B * C ret }} // env ->
  EXTRACT (match o with
           | None => pnone
           | Some b => psome b
           end)
  {{ ovar ~> o * avar ~>? bool * bvar ~>? B * F }}
    Modify SplitPair ^(ovar, avar, bvar) ;
    If Var avar Then xpsome Else xpnone EndIf
  {{ fun ret => xvar ~> ret * avar ~>? bool * bvar ~>? B * ovar ~>? option B * C ret }} // env.
Proof.
  intros.
  eapply extract_equiv_prog with (pr1 := Bind (Ret tt) (fun _ => _)).
  rewrite bind_left_id. apply prog_equiv_equivalence.
  eapply CompileSeq.
  {
    eapply hoare_strengthen_pre;
      [ | eapply CompileSplit' with (HA := GoWrapper_Bool) (B := B)
                                    (a := match o with
                                          | None => false
                                          | Some b => true
                                          end)
                                    (b := match o with
                                          | None => default_value' (@wrap_type _ HB)
                                          | Some b => wrap' b
                                          end) ].
    eval_expr; cancel_go.
  }
  destruct o; simpl in *.
  + unfold ProgOk.
    inv_exec_progok;
      repeat exec_solve_step.
    contradiction H3.
    repeat eexists. apply StepIfTrue. eval_expr.
  + unfold ProgOk.
    inv_exec_progok; repeat exec_solve_step.
    contradiction H3.
    repeat eexists. apply StepIfFalse. eval_expr.
Qed.

Section Concrete.
  (* Compilation lemmas for where variables have concrete values *)

  Fact is_true_false_conflict : forall l ex, is_true l ex -> is_false l ex -> False.
  Proof.
    cbv [is_true is_false].
    intros; congruence.
  Qed.

  Lemma CompileWhileTrueOnce : forall T (p : prog T) A B xp ex env,
    (forall l, l ≲ A -> is_true l ex) ->
    EXTRACT p
    {{ A }}
      xp;
      Go.While ex xp
    {{ B }} // env ->
    EXTRACT p
    {{ A }}
      Go.While ex xp
    {{ B }} // env.
  Proof.
    intros. unfold ProgOk.
    inv_exec_progok.
    inv_exec.
    inv_exec.
    edestruct H0; forward_solve; eauto.
    exfalso; eauto using is_true_false_conflict.
    inv_exec; inv_exec.
    edestruct H0; forward_solve; eauto.
    exfalso; eauto using is_true_false_conflict.
    repeat inv_exec.
    inv_exec. inv_exec.
    edestruct H0; forward_solve; eauto.
    exfalso; eauto using is_true_false_conflict.
    edestruct H0; forward_solve.
    Unshelve. all : eauto.
  Qed.

  Lemma CompileWhileFalseNoOp : forall A xp ex env,
    (forall l, l ≲ A -> is_false l ex) ->
    EXTRACT (Ret tt)
    {{ A }}
      Go.While ex xp
    {{ fun _ => A }} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    repeat (inv_exec; try solve [exfalso; eauto using is_true_false_conflict | repeat eexists; eauto]).
    repeat (inv_exec; try solve [exfalso; eauto using is_true_false_conflict | repeat eexists; eauto]).
    repeat (inv_exec; try solve [exfalso; eauto using is_true_false_conflict | repeat eexists; eauto]).
    contradiction H2.
    repeat eexists.
    eapply StepWhileFalse.
    eauto.
  Qed.

  Lemma CompileWhileVarFalseNoOp : forall A var0 xbody env,
    EXTRACT (Ret tt)
    {{ var0 ~> false * A }}
      Go.While (Var var0) xbody
    {{ fun ret => var0 ~> false * A }} // env.
  Proof.
    intros.
    eapply CompileWhileFalseNoOp.
    intros. eval_expr.
  Qed.

  Lemma CompileWhileVarTrueOnce : forall A B var0 xp env,
    EXTRACT (Ret tt)
    {{ var0 ~> true * A }}
      xp;
      Go.While (Var var0) xp
    {{ fun _ => B }} // env ->
    EXTRACT (Ret tt)
    {{ var0 ~> true * A }}
      Go.While (Var var0) xp
    {{ fun _ => B }} // env.
  Proof.
    intros.
    eapply CompileWhileTrueOnce; eauto.
    intros.
    eval_expr.
  Qed.

  Lemma CompileUnconsNil : forall T (W : GoWrapper T) A lvar cvar xvar xsvar env,
    EXTRACT (Ret tt)
    {{ lvar ~> @nil T * cvar ~>? bool * xvar ~>? T * xsvar ~>? list T * A }}
      Modify Uncons ^(lvar, cvar, xvar, xsvar)
    {{ fun _ => lvar |-> Val (Slice wrap_type) Moved * cvar ~> false * xvar ~>? T * xsvar ~> @nil T * A}} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    repeat exec_solve_step.
    repeat exec_solve_step.
    repeat exec_solve_step.
    contradiction H1.
    repeat eexists.
    eapply StepModify;
    [eval_expr; eauto..].
  Qed.

  Lemma CompileUnconsCons : forall T (W : GoWrapper T) A lvar cvar xvar xsvar (x : T) xs env,
    EXTRACT (Ret tt)
    {{ lvar ~> (x :: xs) * cvar ~>? bool * xvar ~>? T * xsvar ~>? list T * A }}
      Modify Uncons ^(lvar, cvar, xvar, xsvar)
    {{ fun _ => lvar |-> Val (Slice wrap_type) Moved * cvar ~> true * xvar ~> x * xsvar ~> xs * A}} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    repeat exec_solve_step.
    repeat exec_solve_step.
    repeat exec_solve_step.
    contradiction H1.
    repeat eexists.
    eapply StepModify;
    [eval_expr; eauto..].
  Qed.

  Lemma CompileIfFalse : forall T A B (p : prog T) px qx var0 env,
    EXTRACT p {{ var0 ~> false * A }} px {{ B }} // env ->
    EXTRACT p
    {{ var0 ~> false * A }}
      If (Var var0) Then qx Else px EndIf
    {{ B }} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; forward_solve; eauto.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; forward_solve; eauto.
    inv_exec.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; forward_solve; eauto.
    contradiction H2.
    repeat eexists.
    eapply StepIfFalse.
    eval_expr.
  Qed.

  Lemma CompileIfTrue : forall T A B (p : prog T) px qx var0 env,
    EXTRACT p {{ var0 ~> true * A }} px {{ B }} // env ->
    EXTRACT p
    {{ var0 ~> true * A }}
      If (Var var0) Then px Else qx EndIf
    {{ B }} // env.
  Proof.
    unfold ProgOk.
    inv_exec_progok.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; forward_solve; eauto.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; forward_solve; eauto.
    inv_exec.
    inv_exec.
    inv_exec; eval_expr.
    edestruct H; forward_solve; eauto.
    contradiction H2.
    repeat eexists.
    eapply StepIfTrue.
    eval_expr.
  Qed.

End Concrete.

Definition middle_immut : forall low mid high w, immut_word mid := Rec.middle.

Arguments nth_var : simpl never.
