Require Import PeanoNat String List.
Require Import Word Rec Prog ProgMonad Pred.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoTactics2 GoSepAuto.

Import ListNotations.
Import Go.

Set Implicit Arguments.

Fixpoint go_rec_type (t : Rec.type) : type :=
  match t with
  | Rec.WordF n => ImmutableBuffer
  | Rec.ArrayF t' n => Slice (go_rec_type t')
  | Rec.RecF fs =>
    (fix rec_type fs :=
       match fs with
       | [] => Struct []
       | (_, f) :: fs' => Pair (go_rec_type f) (rec_type fs')
       end) fs
  end.

Instance GoWrapper_rec t : GoWrapper (Rec.data t).
  einduction t using Rec.type_rect_nest; simpl.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply IHt0.
  - simpl; typeclasses eauto.
  - simpl in *; typeclasses eauto.
Defined.

Instance GoWrapper_mut_rec t : GoWrapper (Rec.mut_data t).
  einduction t using Rec.type_rect_nest; simpl.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply IHt0.
  - simpl; typeclasses eauto.
  - simpl in *; typeclasses eauto.
Defined.

Lemma GoWrapper_rec_go_rec_type : forall t, @wrap_type _ (GoWrapper_rec t) = go_rec_type t.
Proof.
  einduction t using Rec.type_rect_nest; simpl; auto.
  - rewrite <- IHt0; reflexivity.
  - apply IHt0.
  - reflexivity.
  - simpl in *.
    rewrite <- IHt0.
    rewrite <- IHt1.
    reflexivity.
Qed.

Fixpoint go_of_word (t : Rec.type) (vdst vsrc : var) (from : nat) : stmt :=
  match t with
  | Rec.WordF n =>
    Declare Num (fun vfrom =>
      Declare Num (fun vto =>
        (Modify (@SetConst Num from) ^(vfrom); Modify (@SetConst Num (from + n)) ^(vto);
         Modify SliceBuffer ^(vdst, vsrc, vfrom, vto))))
  | Rec.ArrayF t' n0 =>
    (fix array_of_word n from :=
       match n with
       | O => Modify (InitSliceWithCapacity n0) ^(vdst)
       | S n' =>
         Declare (go_rec_type t') (fun vt' =>
           (array_of_word n' (from + Rec.len t');
            go_of_word t' vt' vsrc from;
            Modify AppendOp ^(vdst, vt')))
       end) n0 from
  | Rec.RecF fs =>
    (fix rec_of_word fs vdst from :=
       match fs with
       | [] => Modify (@SetConst (Struct []) tt) ^(vdst)
       | (_, f) :: fs' =>
         Declare (go_rec_type f) (fun vf =>
           Declare (go_rec_type (Rec.RecF fs')) (fun vfs' =>
             (go_of_word f vf vsrc from;
              rec_of_word fs' vfs' (from + Rec.len f);
              Modify JoinPair ^(vdst, vf, vfs')
              )))
       end) fs vdst from
  end%go.

Hint Constructors source_stmt. 
Lemma source_stmt_go_of_word : forall t vsrc vdst from,
    source_stmt (go_of_word t vdst vsrc from).
Proof.
  intros t vsrc.
  induction t using Rec.type_rect_nest
  with (Q := fun rt =>
               forall vdst from, source_stmt ((fix rec_of_word fs vdst from :=
       match fs with
       | [] => Modify (@SetConst (Struct []) tt) ^(vdst)
       | (_, f) :: fs' =>
         Declare (go_rec_type f) (fun vf =>
           Declare (go_rec_type (Rec.RecF fs')) (fun vfs' =>
             (go_of_word f vf vsrc from;
              rec_of_word fs' vfs' (from + Rec.len f);
              Modify JoinPair ^(vdst, vf, vfs')
              )))%go
       end) rt vdst from)); simpl; intros.
  - eauto.
  - set (n' := n).
    change (InitSliceWithCapacity n') with (InitSliceWithCapacity n).
    generalize n.
    subst n'.
    revert vdst from. induction n; eauto.
    intros. econstructor; intro. econstructor. eapply (IHn vdst (from + Rec.len t) n0).
    eauto.
  - eapply IHt.
  - eauto.
  - eauto.
Qed.

Require Import PeanoNat.

Fixpoint byte_aligned (t : Rec.type) : Prop :=
  match t with
  | Rec.WordF n => Nat.divide 8 n
  | Rec.ArrayF t' n => byte_aligned t'
  | Rec.RecF fs =>
    (fix fields_aligned fs :=
       match fs with
       | [] => True
       | (_, f) :: fs' =>
         byte_aligned f /\ fields_aligned fs'
       end) fs
  end%go.

Lemma byte_aligned_divide : forall t,
    byte_aligned t -> Nat.divide 8 (Rec.len t).
Proof.
  einduction t using Rec.type_rect_nest; simpl; intros; divisibility.
  - revert H. apply IHt0.
  - simpl. divisibility.
  - simpl in *. intuition.
Qed.
Hint Resolve byte_aligned_divide : divide.

Import EqNotations.
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


Lemma compile_of_word' : forall (t : Rec.type) (vdst vsrc : var) before after (buf : immut_word (before + (Rec.len t + after))) env F,
    byte_aligned t ->
    Nat.divide 8 before ->
    Nat.divide 8 after ->
    EXTRACT Ret (@Rec.of_word_middle t before after buf)
    {{ vdst ~>? Rec.data t * vsrc ~> buf * F }}
      go_of_word t vdst vsrc before
    {{ fun ret => vdst ~> ret * vsrc ~> buf * F }} // env.
Proof.
  einduction t using Rec.type_rect_nest; simpl; intros.
  - pose proof (@CompileDeclare env (word n) nat _) as Hc.
    eapply Hc; intros.
    eapply Hc; intros.
    eapply hoare_weaken.
    eapply CompileBefore.
    eapply hoare_weaken; [ let H' := fresh in pose proof (@CompileConst' nat _ env) as H'; eapply H' | cancel_go.. ].
    2: cancel_go.
    2: cancel_go.
    eapply CompileBefore.
    eapply hoare_weaken; [ let H' := fresh in pose proof (@CompileConst' nat _ env) as H'; eapply H' | cancel_go.. ].
    fold plus.
    eapply hoare_weaken; [ eapply CompileMiddle; eauto | cancel_go.. ].
  - revert vdst before after buf H0 H1 H F.
    set (n' := n).
    change (InitSliceWithCapacity n') with (InitSliceWithCapacity n).
    generalize n.
    subst n'.
    induction n; simpl; intros.
    + eapply hoare_weaken.
      evar (F' : pred).
      pose proof (@CompileInitSliceWithCapacity (Rec.data t0) _ env F' vdst n).
      subst F'.
      simpl in H2.
      rewrite GoWrapper_rec_go_rec_type in H2.
      apply H2.
      rewrite GoWrapper_rec_go_rec_type. cancel_go.
      cancel_go.
    + eapply hoare_weaken. rewrite <- GoWrapper_rec_go_rec_type.
      eapply CompileDeclare; intros.
      2: cancel_go.
      2: cancel_go.
      eapply extract_equiv_prog.
      match goal with
      | [ |- ProgMonad.prog_equiv _ ?pr ] =>
        let Pr := fresh "Pr" in
        set pr as Pr;
          match goal with
          | [ Pr := context[?f ?before after n ?e] |- _ ] =>
            pattern (f before after n e) in Pr
          end
      end.
      subst Pr.
      eapply bind_left_id.
      eapply hoare_weaken; [ eapply CompileBindRet with (vara := vdst) | cancel_go.. ].
      eapply hoare_weaken.
      rewrite GoWrapper_rec_go_rec_type.
      specialize (IHn n0 vdst (before + Rec.len t0)).
      eapply IHn; eauto.
      divisibility.

      norm.
      eapply cancel_one.
      eapply PickFirst.
      reflexivity.
      cbv [stars app pred_fold_left fold_left].
      cancel_go.
      rewrite okToCancel_eq_rect_immut_word.
      cancel_go.
      cancel_go.

      eapply extract_equiv_prog.
      match goal with
      | [ |- ProgMonad.prog_equiv _ ?pr ] =>
        let Pr := fresh "Pr" in
        set pr as Pr;
          match goal with
          | [ Pr := context[@Rec.of_word_middle ?a ?b ?c ?d] |- _ ] =>
            pattern (@Rec.of_word_middle a b c d) in Pr
          end
      end.
      subst Pr.
      eapply bind_left_id.
      eapply hoare_weaken; [ eapply CompileBindRet with (vara := var0) | cancel_go.. ].
      eapply hoare_weaken.
      eapply IHt0; eauto.
      divisibility.
      rewrite eq_rect_leibniz with (e := Rec.of_word_middle_subproof t0 after n).
      rewrite ?okToCancel_eq_rect_immut_word.
      cancel_go.
      cancel_go.

      eapply hoare_weaken.
      eapply CompileAppend.
      cancel_go.
      intros.
      rewrite eq_rect_leibniz with (e := Rec.of_word_middle_subproof t0 after n).
      rewrite okToCancel_eq_rect_immut_word.
      cancel_go.

  - revert vdst vsrc before after buf env F H H0 H1. eapply IHt0.
  - simpl; intros.
    eapply hoare_weaken; [ eapply CompileConst with (Wr := GoWrapper_unit) | cancel_go.. ].
  - simpl; intros.
    
    eapply hoare_weaken. rewrite <- GoWrapper_rec_go_rec_type.
    eapply CompileDeclare; intros.
    2: cancel_go.
    2: cancel_go.

    eapply hoare_weaken.
    match goal with
    | |- context[Declare (?f rt)] => change (f rt) with (go_rec_type (Rec.RecF rt))
    end.
    rewrite <- GoWrapper_rec_go_rec_type.
    eapply CompileDeclare; intros.
    2: cancel_go.
    2: cancel_go.

    eapply extract_equiv_prog.
    match goal with
    | [ |- ProgMonad.prog_equiv _ ?pr ] =>
      let Pr := fresh "Pr" in
      set pr as Pr;
        match goal with
        | [ Pr := context[@Rec.of_word_middle ?a ?b ?c ?d] |- _ ] =>
          pattern (@Rec.of_word_middle a b c d) in Pr
        end
    end.
    subst Pr.
    eapply bind_left_id.
    eapply hoare_weaken; [ eapply CompileBindRet with (vara := var0) | cancel_go.. ].
    eapply hoare_weaken.
    eapply IHt0; intuition eauto.
    apply Nat.divide_add_r; divisibility.
    revert H2 H3.
    clear.
    induction rt; [ intros; divisibility | intros; destruct a; intuition divisibility ].
    rewrite eq_rect_leibniz with (e := Rec.of_word_middle_subproof1 after rt n t0).
    rewrite ?okToCancel_eq_rect_immut_word.
    cancel_go.
    cancel_go.

    eapply extract_equiv_prog.
    match goal with
    | [ |- ProgMonad.prog_equiv _ ?pr ] =>
      let Pr := fresh "Pr" in
      set pr as Pr;
        match goal with
        | [ Pr := context[?f ?before after rt ?e] |- _ ] =>
          pattern (f before after rt e) in Pr
        end
    end.
    subst Pr.
    eapply bind_left_id.
    eapply hoare_weaken; [ eapply CompileBindRet with (vara := var1) | cancel_go.. ].
    eapply hoare_weaken.
    cbv beta in IHt1.
    specialize (IHt1 var1 vsrc).
    eapply IHt1; intuition eauto.
    divisibility.

    norm.
    eapply cancel_one.
    eapply PickFirst.
    reflexivity.
    cbv [stars app pred_fold_left fold_left].
    rewrite eq_rect_leibniz with (e := Rec.of_word_middle_subproof1 after rt n t0).
    rewrite ?okToCancel_eq_rect_immut_word.
    cancel_go.
    cancel_go.


    eapply hoare_weaken.
    eapply CompileJoin.
    rewrite eq_rect_leibniz with (e := Rec.of_word_middle_subproof1 after rt n t0).
    cancel_go.
    cancel_go.
    rewrite ?okToCancel_eq_rect_immut_word.
    reflexivity.
Qed.

Lemma compile_of_word : forall (t : Rec.type) (vdst vsrc : var) (buf : immut_word (Rec.len t)) env F,
    byte_aligned t ->
    EXTRACT Ret (@Rec.of_word t buf)
    {{ vdst ~>? Rec.data t * vsrc ~> buf * F }}
      go_of_word t vdst vsrc 0
    {{ fun ret => vdst ~> ret * vsrc ~> buf * F }} // env.
Proof.
  intros.
  erewrite Rec.of_word_middle_eq.
  eapply hoare_weaken.
  eapply compile_of_word'; try divisibility.
  rewrite okToCancel_eq_rect_immut_word.
  reflexivity.
  intros; cbv beta.
  rewrite okToCancel_eq_rect_immut_word.
  reflexivity.
  Unshelve.
  eapply plus_n_O.
Qed.