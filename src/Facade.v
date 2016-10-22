Require Import ProofIrrelevance.
Require Import Eqdep_dec.
Require Import PeanoNat String List FMapAVL Structures.OrderedTypeEx.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import VerdiTactics.
Require Import StringMap MoreMapFacts.
Require Import Mem AsyncDisk PredCrash Prog ProgMonad SepAuto.
Require Import BasicProg.
Require Import Gensym.
Require Import Word.
Require Import Omega.
Require Import Go.
Require Import Pred GoSep.

Import ListNotations.

(* TODO: Split into more files *)

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

Hint Constructors step fail_step crash_step exec.

Notation "k -s> v ;  m" := (StringMap.add k v m) (at level 21, right associativity) : map_scope.
Delimit Scope map_scope with map.

Notation "k ->> v ;  m" := (VarMap.add k v m) (at level 21, right associativity) : map_scope.

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

Ltac GoWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | [ H : _ * _ |- _ ] => destruct H
                   | [ H : unit |- _ ] => destruct H
                   | [ H : _ = _ |- _ ] => inversion H; solve [eauto using inj_pair2 with gowrapper]
                   | _ => solve [eauto using inj_pair2 with gowrapper]
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

Instance GoWrapper_valu : GoWrapper valu.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.DiskBlock |}; GoWrapper_t.
Defined.

Instance GoWrapper_unit : GoWrapper unit.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.EmptyStruct |}; GoWrapper_t.
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
  refine {| wrap' := map wrap';
            wrap_type := Go.Slice wrap_type |}; GoWrapper_t.
Defined.


Instance GoWrapper_dec {P Q} : GoWrapper ({P} + {Q}).
Proof.
  refine {| wrap' := fun (v : {P} + {Q}) => if v then true else false;
            wrap_type := Go.Bool |}.
  intros.
  destruct a1, a2; f_equal; try discriminate; apply proof_irrelevance.
Qed.

Definition extract_code := projT1.

Local Open Scope string_scope.

Local Open Scope map_scope.

Ltac find_cases var st := case_eq (VarMap.find var st); [
  let v := fresh "v" in
  let He := fresh "He" in
  intros v He; rewrite ?He in *
| let Hne := fresh "Hne" in
  intro Hne; rewrite Hne in *; exfalso; solve [ discriminate || intuition idtac ] ].


Ltac inv_exec :=
  match goal with
  | [ H : Go.step _ _ _ |- _ ] => invc H
  | [ H : Go.exec _ _ _ |- _ ] => invc H
  | [ H : Go.crash_step _ |- _ ] => invc H
  end; try discriminate.

Example micro_noop : sigT (fun p =>
  EXTRACT Ret tt
  {{ any }}
    p
  {{ fun _ => any }} // StringMap.empty _).
Proof.
  eexists.
  intro.
  instantiate (1 := Go.Skip).
  intros.
  repeat inv_exec;
    repeat split; intros; subst; try discriminate.
  contradiction H2.
  econstructor; eauto.
  find_inversion. eauto.
Defined.

(*
Theorem extract_finish_equiv : forall A {H: GoWrapper A} scope cscope pr p,
  (forall d0,
    {{ SItemDisk (NTSome "disk") d0 (ret tt) :: scope }}
      p
    {{ [ SItemDisk (NTSome "disk") d0 pr; SItemRet (NTSome "out") d0 pr ] }} {{ cscope }} // disk_env) ->
  forall st st' d0,
    st ## ( SItemDisk (NTSome "disk") d0 (ret tt) :: scope) ->
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
    st ## (SItemDisk (NTSome "disk") d0 (ret tt) :: scope) ->
    (Go.step disk_env)^* (p, st) (p', st') ->
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

Hint Immediate possible_sync_refl.

Ltac set_hyp_evars :=
  repeat match goal with
  | [ H : context[?e] |- _ ] =>
    is_evar e;
    let H := fresh in
    set (H := e) in *
  end.

Module VarMapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(VarMap).
Module Import MoreVarMapFacts := MoreFacts_fun(Nat_as_OT)(VarMap).

Lemma read_fails_not_present:
  forall env vvar avar (a : W) (v0 : valu) d s,
    VarMap.find avar s = Some (wrap a) ->
    VarMap.find vvar s = Some (wrap v0) ->
    ~ (exists st' p', Go.step env (d, s, Go.DiskRead vvar (Go.Var avar)) (st', p')) ->
    d a = None.
Proof.
  intros.
  assert (~exists v0, d a = Some v0).
  intuition.
  deex.
  contradiction H1.
  destruct v1. repeat eexists. econstructor; eauto.
  destruct (d a); eauto. contradiction H2. eauto.
Qed.
Hint Resolve read_fails_not_present.

Lemma write_fails_not_present:
  forall env vvar avar (a : W) (v : valu) d s,
    VarMap.find vvar s = Some (wrap v) ->
    VarMap.find avar s = Some (wrap a) ->
    ~ (exists st' p', Go.step env (d, s, Go.DiskWrite (Go.Var avar) (Go.Var vvar)) (st', p')) ->
    d a = None.
Proof.
  intros.
  assert (~exists v0, d a = Some v0).
  intuition.
  deex.
  contradiction H1.
  destruct v0. repeat eexists. econstructor; eauto.
  destruct (d a); eauto. contradiction H2. eauto.
Qed.
Hint Resolve write_fails_not_present.

Lemma skip_is_final :
  forall d s, Go.is_final (d, s, Go.Skip).
Proof.
  unfold Go.is_final; trivial.
Qed.

Hint Resolve skip_is_final.

Ltac match_finds :=
  match goal with
    | [ H1: VarMap.find ?a ?s = ?v1, H2: VarMap.find ?a ?s = ?v2 |- _ ] => rewrite H1 in H2; try invc H2
  end.

Ltac invert_trivial H :=
  match type of H with
    | ?con ?a = ?con ?b =>
      let H' := fresh in
      assert (a = b) as H' by exact (match H with eq_refl => eq_refl end); clear H; rename H' into H
  end.

Ltac find_inversion_safe :=
  match goal with
    | [ H : ?X ?a = ?X ?b |- _ ] =>
      (unify a b; fail 1) ||
      let He := fresh in
      assert (a = b) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; subst
    | [ H : ?X ?a1 ?a2 = ?X ?b1 ?b2 |- _ ] =>
      (unify a1 b1; fail 1) ||
      (unify a2 b2; fail 1) ||
      let He := fresh in
      assert (a1 = b1 /\ a2 = b2) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; destruct He as [? ?]; subst
  end.

Ltac destruct_pair :=
  match goal with
    | [ H : _ * _ |- _ ] => destruct H
    | [ H : Go.state |- _ ] => destruct H
  end.

Ltac inv_exec_progok :=
  repeat destruct_pair; repeat inv_exec; unfold Go.sel in *; simpl in *;
  intuition (subst; try discriminate;
             repeat find_inversion_safe; repeat match_finds; repeat find_inversion_safe;  simpl in *;
               try solve [ exfalso; intuition eauto 10 ]; eauto 10).
(*
Example micro_write : sigT (fun p => forall a v,
  EXTRACT Write a v
  {{ 0 ~> a * 1 ~> v }}
    p
  {{ fun _ => emp }} // StringMap.empty _).
Proof.
  eexists.
  intros.
  instantiate (1 := (Go.DiskWrite (Go.Var 0) (Go.Var 1))%go).
  intro. intros.
  inv_exec_progok.
Defined.
*)

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

Hint Extern 1 (Go.eval _ _ = _) =>
unfold Go.eval.

Hint Extern 1 (Go.step _ (_, Go.Assign _ _) _) =>
eapply Go.StepAssign.
Hint Constructors Go.step.

Fact sep_star_ptsto_some_find : forall l var val A,
  l ≲ (var |-> val * A) -> VarMap.find var l = Some val.
Proof.
  intros.
  find_eapply_lem_hyp sep_star_assoc_1.
  find_eapply_lem_hyp sep_star_ptsto_some.
  eauto.
Qed.

Hint Resolve sep_star_ptsto_some_find.

Ltac extract_var_val :=
  lazymatch goal with
  | [ H: ?s ≲ ?P |- _ ] =>
    match P with
    | context[(?a |-> ?v)%pred] =>
      match goal with
      | [ H: VarMap.find a s = Some v |- _ ] => fail 1
      | _ => idtac
      end;
      let He := fresh "He" in
      assert (VarMap.find a s = Some v) as He; [
        eapply pred_apply_pimpl_proper in H; [
        | reflexivity |
        lazymatch goal with
        | [ |- _ =p=> ?Q ] =>
          let F := fresh "F" in
          evar (F : pred);
          unify Q (a |-> v * F)%pred;
          cancel
        end ];
        eapply ptsto_valid in H; eassumption
      | try rewrite He in * ]
    end
  end.

Theorem eq_dec_eq :
  forall A (dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) a,
    dec a a = left eq_refl.
Proof.
  intros.
  destruct (dec a a); try congruence.
  f_equal.
  apply UIP_dec; assumption.
Qed.

Lemma CompileConst : forall env A var (v v0 : nat),
  EXTRACT Ret v
  {{ var ~> v0 * A }}
    var <~const v
  {{ fun ret => var ~> ret * A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  do 2 eexists.
  intuition eauto.
  unfold Go.sel, id, Go.update_one, Go.setconst_impl in *.
  destruct vs0.
  repeat extract_var_val.
  repeat find_inversion_safe.
  find_reverse_rewrite.
  simpl in *.
  repeat find_inversion.
  rewrite add_upd.
  rewrite sep_star_assoc.
  eapply ptsto_upd.
  rewrite sep_star_assoc in H.
  eassumption.

  contradiction H1.
  repeat eexists.
  eapply Go.StepModify.
  rewrite sep_star_assoc in H.
  eapply sep_star_ptsto_some in H.
  unfold Go.sel; simpl.
  unfold mem_of in *.
  rewrite H.
  trivial.
  all: simpl; reflexivity.
Qed.

Ltac forwardauto1 H :=
  repeat eforward H; conclude H eauto.

Ltac forwardauto H :=
  forwardauto1 H; repeat forwardauto1 H.

Ltac forward_solve_step :=
  match goal with
    | _ => progress intuition eauto
    | [ H : forall _, _ |- _ ] => forwardauto H
    | _ => deex
  end.

Ltac forward_solve :=
  repeat forward_solve_step.

Definition vars_subset V (subset set : VarMap.t V) := forall k, VarMap.find k set = None -> VarMap.find k subset = None.

Definition list_max l := fold_left max l 0.

Theorem le_fold_max : forall l v,
  v <= fold_left Init.Nat.max l v.
Proof.
  induction l; auto.
  simpl; intros.
  let HH := fresh in (edestruct Max.max_dec as [HH | HH]; rewrite HH).
  eauto.
  eapply le_trans.
  apply Nat.max_r_iff; eauto.
  eauto.
Qed.

Theorem le_fold_max_trans : forall l a b,
  a <= b ->
  fold_left Init.Nat.max l a <= fold_left Init.Nat.max l b.
Proof.
  induction l; intros. auto.
  simpl.
  repeat (let HH := fresh in (edestruct Max.max_dec as [HH | HH]; rewrite HH));
  repeat rewrite ?Nat.max_l_iff, ?Nat.max_r_iff in *;
  intuition.
Qed.

Theorem gt_list_max : forall l v,
  v > list_max l ->
  ~ In v l.
Proof.
  unfold list_max.
  induction l; intros; simpl; auto.
  intuition. subst; simpl in *.
  pose proof (le_fold_max l v). omega.
  simpl in *. eapply IHl; [ | eauto].
  pose proof (le_fold_max_trans l (Peano.le_0_n a)).
  omega.
Qed.

Definition keys T (l : VarMap.t T) := fst (split (VarMap.elements l)).

Theorem varmap_find_oob : forall T (l : VarMap.t T) v,
  v > list_max (keys l) ->
  VarMap.find v l = None.
Proof.
  intros.
  apply VarMapFacts.not_find_in_iff.
  apply gt_list_max in H.
  intuition.
  apply H.
  unfold keys. clear H; rename H0 into H.
  apply VarMapFacts.elements_in_iff in H. destruct H.
  erewrite <- ListUtils.fst_pair with (a := v).
  apply in_split_l.
  apply mapsto_elements.
  apply VarMapFacts.elements_mapsto_iff.
  all : eauto.
Qed.

Theorem vars_subset_refl :
  forall V s, @vars_subset V s s.
Proof.
  unfold vars_subset.
  eauto.
Qed.

Theorem vars_subset_trans :
  forall V s1 s2 s3,
    @vars_subset V s1 s2 ->
    vars_subset s2 s3 ->
    vars_subset s1 s3.
Proof.
  unfold vars_subset.
  eauto.
Qed.

Hint Resolve vars_subset_refl vars_subset_trans.

Lemma can_always_declare:
  forall env t xp st,
    exists st'' p'',
      Go.step env (st, Go.Declare t xp) (st'', p'').
Proof.
  intros.
  destruct_pair.
  repeat eexists.
  econstructor; eauto.
  apply varmap_find_oob.
  eauto.
Qed.

(* TODO: should have a more general way of dispatching goals like this *)
Lemma subset_add_remove :
  forall T var m m' (v : T),
    vars_subset m' (var ->> v; m) ->
    vars_subset (VarMap.remove var m') m.
Proof.
  unfold vars_subset; intros.
  destruct (Nat.eq_dec k var).
  - eauto using VarMapFacts.remove_eq_o.
  - rewrite VarMapFacts.remove_neq_o; eauto.
    eapply H.
    rewrite VarMapFacts.add_neq_o; eauto.
Qed.
Hint Resolve subset_add_remove.

Lemma subset_replace :
  forall T var m (v0 v : T),
    VarMap.find var m = Some v0 ->
    vars_subset (var ->> v; m) m.
Proof.
  unfold vars_subset; intros.
  destruct (Nat.eq_dec k var).
  - congruence.
  - rewrite VarMapFacts.add_neq_o; eauto.
Qed.
Hint Resolve subset_replace.

Lemma subset_remove :
  forall T var (m : VarMap.t T),
    vars_subset (VarMap.remove var m) m.
Proof.
  unfold vars_subset; intros.
  destruct (Nat.eq_dec k var).
  - eauto using VarMapFacts.remove_eq_o.
  - rewrite VarMapFacts.remove_neq_o; eauto.
Qed.
Hint Resolve subset_remove.

Theorem exec_vars_decrease :
  forall env p d d' s s',
    Go.exec env ((d, s), p) (Go.Finished (d', s')) ->
    vars_subset s' s.
Proof.
  intros.
  find_eapply_lem_hyp Go.ExecFinished_Steps.
  find_eapply_lem_hyp Go.Steps_runsto'.
  prep_induction H; induction H; intros; subst; unfold Go.locals, Go.state in *;
    repeat destruct_pair; repeat find_inversion_safe; eauto.
    (* TODO: theorem about update_many *)
    admit.
  - invc H4; invc H5; eauto.
  - subst_definitions.
    admit. (* TODO: execution semantics are wrong here *)
  - admit.
Admitted.

(* Something like this is true when [pr] does not fail:

Theorem prog_vars_decrease :
  forall T env A B p (pr : prog T),
    EXTRACT pr
    {{ A }}
      p
    {{ B }} // env ->
    forall r,
    match A, B r with
      | Some A', Some B' => forall k, VarMap.In k B' -> VarMap.In k A'
      | _, _ => True
    end.
Admitted.
*)


Lemma CompileDeclare :
  forall env T t (zeroval : Go.type_denote t) {H : GoWrapper (Go.type_denote t)} A B (p : prog T) xp,
    wrap zeroval = Go.default_value t ->
    (forall var,
       EXTRACT p
       {{ var ~> zeroval * A }}
         xp var
       {{ fun ret => B ret }} // env) ->
    EXTRACT p
    {{ A }}
      Go.Declare t xp
    {{ fun ret => B ret }} // env.
Proof.
  unfold ProgOk.
  intros.
  repeat destruct_pair.
  destruct out.
  - intuition try discriminate.
    find_eapply_lem_hyp Go.ExecFailed_Steps.
    repeat deex.
    invc H5.
    contradiction H7.
    eapply can_always_declare; auto.

    destruct_pair.
    hnf in s.
    destruct_pair.
    simpl in *.
    invc H6.
    specialize (H1 var (r0, var ->> Go.default_value t; l) hm).
    forward H1.
    {
      simpl.
      rewrite <- H0.
      rewrite add_upd.
      rewrite sep_star_assoc.
      rewrite sep_star_comm.
      eapply ptsto_upd_disjoint; eauto.
    }
    intuition.
    simpl in *.
    find_eapply_lem_hyp Go.Steps_Seq.
    intuition.
    eapply H6; eauto.
    deex.
    eapply Go.Steps_ExecFailed in H8; eauto.
    intuition.
    contradiction H7.
    match goal with
    | [ H : Go.is_final _ |- _ ] => cbv [snd Go.is_final] in H; subst
    end.
    eauto.
    intuition.
    contradiction H7.
    repeat deex.
    eauto.

    forward_solve.
    invc H9.
    contradiction H7.
    destruct st'.
    repeat eexists. econstructor; eauto.
    invc H1.
    invc H10.
    contradiction H3.
    auto.
    invc H1.

    (*
  - invc H4.
    invc H5.
    specialize (H2 var).
    forward H2.
    {
      maps.
      simpl in *.
      pose proof (Forall_elements_forall_In H3).
      case_eq (VarMap.find var A); intros.
      destruct s.
      forward_solve.
      find_rewrite.
      intuition.
      auto.
    }
    intuition try discriminate.
    destruct_pair.
    find_inversion_safe.
    specialize (H5 (r, var ->> Go.default_value t; t0) hm).
    forward H5.
    {
      clear H5.
      simpl in *; maps.
      eapply forall_In_Forall_elements; intros.
      pose proof (Forall_elements_forall_In H3).
      destruct (VarMapFacts.eq_dec k var); maps.
      specialize (H5 k v).
      intuition.
    }
    find_eapply_lem_hyp Go.ExecFinished_Steps.
    find_eapply_lem_hyp Go.Steps_Seq.
    intuition; deex; try discriminate.
    repeat find_eapply_lem_hyp Go.Steps_ExecFinished.
    invc H8.
    invc H5.
    invc H9.
    invc H5.
    forward_solve.
    simpl in *.
    repeat eexists; eauto.
    maps.
    eapply forall_In_Forall_elements; intros.
    pose proof (Forall_elements_forall_In H10).
    forward_solve.
    destruct v.
    destruct (VarMapFacts.eq_dec k var).
    subst.
    maps.
    unfold vars_subset in H1.
    specialize (H1 r1 var).
    intuition.
    congruence.
    maps.

  - invc H4; [ | invc H6 ].
    invc H5.
    find_eapply_lem_hyp Go.ExecCrashed_Steps.
    repeat deex; try discriminate.
    find_inversion_safe.
    find_eapply_lem_hyp Go.Steps_Seq.
    intuition.
    repeat deex.
    invc H7.
    eapply Go.Steps_ExecCrashed in H5; eauto.
    simpl in *.
    specialize (H2 var).
    forward H2.
    {
      maps.
      simpl in *.
      pose proof (Forall_elements_forall_In H3).
      case_eq (VarMap.find var A); intros.
      destruct s.
      forward_solve.
      find_rewrite.
      intuition.
      auto.
    }
    intuition.
    specialize (H7 (r, var ->> Go.default_value t; t0) hm).
    forward H7.
    {
      clear H7.
      simpl in *; maps.
      eapply forall_In_Forall_elements; intros.
      pose proof (Forall_elements_forall_In H3).
      destruct (VarMapFacts.eq_dec k var); maps.
      specialize (H7 k v).
      intuition.
    }
    forward_solve.

    deex.
    invc H6.
    invc H7.
    invc H4.
    invc H8.
    invc H7.
    invc H4.
*)
Admitted.

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

Lemma CompileBind : forall T T' {H: GoWrapper T} env A (B : T' -> _) v0 p f xp xf var,
  EXTRACT p
  {{ var ~> v0 * A }}
    xp
  {{ fun ret => var ~> ret * A }} // env ->
  (forall (a : T),
    EXTRACT f a
    {{ var ~> a * A }}
      xf
    {{ B }} // env) ->
  EXTRACT Bind p f
  {{ var ~> v0 * A }}
    xp; xf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition subst.

  - find_eapply_lem_hyp Go.ExecFinished_Steps. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecFinished.
    forwardauto H0; intuition.
    forwardauto H3; repeat deex.
    specialize (H1 r).
    forward_solve.

  - find_eapply_lem_hyp Go.ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex.
    + invc H5. find_eapply_lem_hyp Go.Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct st'. find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecCrashed; eauto.
      forwardauto H0; intuition.
      forwardauto H3; repeat deex.
      specialize (H1 r0).
      forward_solve.

  - find_eapply_lem_hyp Go.ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Go.Steps_Seq.
    intuition; repeat deex.
    + eapply Go.Steps_ExecFailed in H5; eauto.
      forward_solve.
      unfold Go.is_final; simpl; intuition subst.
      contradiction H6. eauto.
      intuition. repeat deex.
      contradiction H6. eauto.
    + destruct st'. find_eapply_lem_hyp Go.Steps_ExecFinished. find_eapply_lem_hyp Go.Steps_ExecFailed; eauto.
      forwardauto H0; intuition.
      forwardauto H4; repeat deex.
      specialize (H1 r0).
      forward_solve.

  Unshelve.
  all: auto.
Qed.

Import Go.

Definition pimpl_subset (P Q : pred) := P =p=> Q * any.

Notation "p >p=> q" := (pimpl_subset p%pred q%pred) (right associativity, at level 90).

Lemma hoare_weaken_post : forall T env A (B1 B2 : T -> _) pr p,
  (forall x, B1 x >p=> B2 x)%pred ->
  EXTRACT pr
  {{ A }} p {{ B1 }} // env ->
  EXTRACT pr
  {{ A }} p {{ B2 }} // env.
Proof.
  unfold ProgOk, pimpl_subset.
  intros.
  forwardauto H0.
  intuition subst.
  forwardauto H3; repeat deex;
  repeat eexists; eauto.
  unfold pred_apply in *.
  pred_apply.
  rewrite H.
  rewrite sep_star_assoc.
  rewrite pimpl_any with (p := (any * any)%pred).
  eauto.
  eauto.
  eauto.
Qed.

Lemma hoare_strengthen_pre : forall T env A1 A2 (B : T -> _) pr p,
  (A2 >p=> A1)%pred ->
  EXTRACT pr
  {{ A1 }} p {{ B }} // env ->
  EXTRACT pr
  {{ A2 }} p {{ B }} // env.
Proof.
  unfold ProgOk, pimpl_subset, pred_apply in *; intros.
  rewrite H in H1.
  apply sep_star_assoc in H1.
  rewrite pimpl_any with (p := (any * any)%pred) in H1.
  forward_solve.
Qed.

Instance progok_hoare_proper :
  forall T env pr,
  Proper (@prog_equiv T ==> Basics.flip pimpl_subset ==> pointwise_relation _ pimpl_subset ==> Basics.impl) (@ProgOk T env pr).
Proof.
  intros.
  intros pr1 pr2 Hpr A1 A2 Hpre B1 B2 Hpost H.
  eauto using hoare_strengthen_pre, hoare_weaken_post, extract_equiv_prog.
Qed.

Instance piff_progok_proper : forall T p xp env,
  Proper (piff ==> pointwise_relation T piff ==> flip Basics.impl) (ProgOk env p xp).
Proof.
  repeat intro.
  rewrite H in H2.
  setoid_rewrite H0.
  edestruct H1; intuition eauto.
Defined.

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
  intuition subst.

  - find_eapply_lem_hyp ExecFinished_Steps. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFinished.
    (* [forward_solve] is not really good enough *)
    forwardauto H. intuition.
    forwardauto H2. repeat deex.
    forward_solve.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H4. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forwardauto H. intuition.
      forwardauto H2. repeat deex.
      forward_solve.

  - find_eapply_lem_hyp ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + eapply Steps_ExecFailed in H4; eauto.
      forward_solve.
      unfold is_final; simpl; intuition subst.
      contradiction H5. eauto.
      intuition. repeat deex.
      contradiction H5. eauto.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forwardauto H. intuition.
      forwardauto H3. repeat deex.
      forward_solve.

  Unshelve.
  all: auto.
Qed.


Example micro_dup : forall T {Wr: GoWrapper T}, sigT (fun p => forall (x v0 : T),
  EXTRACT Ret tt
  {{ 0 ~> x * 1 ~> v0 }}
    p
  {{ fun _ => 1 ~> x * 0 ~> x }} // StringMap.empty _).
Proof.
  eexists. intros.
  instantiate (1 := (1 <~dup 0)%go).
  unfold ProgOk.
  inv_exec_progok;
  inv_exec_progok.
  repeat eexists. eauto.
  unfold sel, duplicate_impl, update_one in *.
  find_apply_lem_hyp inj_pair2; subst.
  simpl in *.
  repeat extract_var_val.
  simpl in *.
  repeat find_inversion_safe.
  simpl in *.
  rewrite eq_dec_eq in *.
  find_inversion.
  rewrite ?add_upd.
  unfold pred_apply.
  eapply pimpl_apply; [ | eapply ptsto_upd ]; [ cancel | ].
  eapply pimpl_apply; [ | eassumption ]; cancel.

  contradiction H1.
  repeat eexists.
  econstructor.
  simpl; unfold sel.
  repeat extract_var_val.
  reflexivity.
  reflexivity.
  simpl.
  break_match; try congruence.
  reflexivity.
Defined.

Lemma CompileIf : forall P Q {H1 : GoWrapper ({P}+{Q})}
                         T {H : GoWrapper T}
                         A B env (pt pf : prog T) (cond : {P} + {Q}) xpt xpf xcond condvar,
  EXTRACT pt
  {{ A }}
    xpt
  {{ B }} // env ->
  EXTRACT pf
  {{ A }}
    xpf
  {{ B }} // env ->
  EXTRACT Ret cond
  {{ A }}
    xcond
  {{ fun ret => condvar ~> ret * A }} // env ->
  EXTRACT if cond then pt else pf
  {{ A }}
   xcond ; If Var condvar Then xpt Else xpf EndIf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition.
Admitted.

Lemma CompileWeq : forall A (a b : valu) env xa xb retvar avar bvar,
  EXTRACT Ret a
  {{ A }}
    xa
  {{ fun ret => avar ~> ret * A }} // env ->
  (forall (av : valu),
  EXTRACT Ret b
  {{ avar ~> av * A }}
    xb
  {{ fun ret => bvar ~> ret * avar ~> av * A }} // env) ->
  EXTRACT Ret (weq a b)
  {{ A }}
    xa ; xb ; retvar <~ (Var avar = Var bvar)
  {{ fun ret => retvar ~> ret * A }} // env.
Proof.
  unfold ProgOk.
  intuition.
Admitted.

Lemma CompileRead :
  forall env F avar vvar (v0 : valu) a,
    EXTRACT Read a
    {{ vvar ~> v0 * avar ~> a * F }}
      DiskRead vvar (Var avar)
    {{ fun ret => vvar ~> ret * avar ~> a * F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  {
    repeat eexists; eauto.
    admit.
    admit.
  }
  destruct (r a) as [p|] eqn:H'; eauto.
  destruct p.
  contradiction H1.
  repeat eexists; eauto.
  eapply StepDiskRead; eauto; unfold eval.
  (* TODO automate this *)
  rewrite sep_star_assoc_1 in H.
  admit.
  admit.
  admit.
Admitted.

Lemma CompileWrite : forall env F avar vvar a v,
  EXTRACT Write a v
  {{ avar ~> a * vvar ~> v * F }}
    DiskWrite (Var avar) (Var vvar)
  {{ fun _ => avar ~> a * vvar ~> v * F }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  {
    repeat eexists; eauto.
    admit.
  }
  destruct (r a) as [p|] eqn:H'; eauto.
  destruct p.
  contradiction H1.
  repeat eexists; eauto.
  eapply StepDiskWrite; eauto; unfold eval.
  (* TODO automate this *)
Admitted.

Lemma CompileAdd :
  forall env F sumvar avar bvar (sum0 a b : nat),
    EXTRACT Ret (a + b)
    {{ sumvar ~> sum0 * avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Plus) (sumvar, avar, bvar)
    {{ fun ret => sumvar ~> ret * avar ~> a * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  destruct_pair; simpl in *.
  inv_exec_progok.
  find_apply_lem_hyp inj_pair2; subst.
  unfold sel, numop_impl, update_one, id in *.
  simpl in *.
  repeat destruct_pair.
  repeat extract_var_val.
  repeat find_inversion_safe.
  simpl in *.
  find_inversion.
  simpl in *.
  find_inversion.
  repeat eexists.
  econstructor.
  rewrite ?add_upd.
  unfold pred_apply.
  eapply pimpl_apply; [ | eapply ptsto_upd ]; [ cancel | ].
  eapply pimpl_apply; [ | eassumption ]; cancel.

  contradiction H1.
  repeat eexists.
  econstructor.

  unfold sel; simpl; repeat extract_var_val.
  all: simpl; reflexivity.
Defined.

Lemma CompileAddInPlace1 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a + b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Plus) (avar, avar, bvar)
    {{ fun ret => avar ~> ret * bvar ~> b * F }} // env.
Proof.
  unfold ProgOk; intros.
  destruct_pair; simpl in *.
  inv_exec_progok.
  find_apply_lem_hyp inj_pair2; subst.
  unfold sel, numop_impl, update_one, id in *.
  simpl in *.
  repeat destruct_pair.
  repeat extract_var_val.
  repeat find_inversion_safe.
  simpl in *.
  find_inversion.
  simpl in *.
  find_inversion.
  repeat eexists.
  econstructor.
  rewrite ?add_upd.
  unfold pred_apply.
  eapply pimpl_apply; [ | eapply ptsto_upd ]; [ cancel | ].
  eapply pimpl_apply; [ | eassumption ]; cancel.

  contradiction H1.
  repeat eexists.
  econstructor.

  unfold sel; simpl; repeat extract_var_val.
  all: simpl; reflexivity.
Defined.

(* TODO: make it unnecessary to have all these separate lemmas *)
Lemma CompileAddInPlace2 :
  forall env F avar bvar (a b : nat),
    EXTRACT Ret (a + b)
    {{ avar ~> a * bvar ~> b * F }}
      Modify (ModifyNumOp Plus) (bvar, avar, bvar)
    {{ fun ret => bvar ~> ret * avar ~> a * F }} // env.
Proof.
  unfold ProgOk; intros.
  destruct_pair; simpl in *.
  inv_exec_progok.
  find_apply_lem_hyp inj_pair2; subst.
  unfold sel, numop_impl, update_one, id in *.
  simpl in *.
  repeat destruct_pair.
  repeat extract_var_val.
  repeat find_inversion_safe.
  simpl in *.
  find_inversion.
  simpl in *.
  find_inversion.
  repeat eexists.
  econstructor.
  rewrite ?add_upd.
  unfold pred_apply.
  eapply pimpl_apply; [ | eapply ptsto_upd ]; [ cancel | ].
  eapply pimpl_apply; [ | eassumption ]; cancel.

  contradiction H1.
  repeat eexists.
  econstructor.

  unfold sel; simpl; repeat extract_var_val.
  all: simpl; reflexivity.
Defined.

Definition any' : pred := any.

Lemma chop_any :
  forall P Q : pred,
    P =p=> Q ->
    P =p=> Q * any.
Proof.
  intros.
  rewrite H.
  cancel.
  eapply pimpl_any.
Qed.

(* TODO: less hackery *)
Ltac cancel_subset :=
  unfold pimpl_subset;
  fold any';
  unfold any' at 1;
  cancel;
  try solve [ eapply chop_any; cancel | eapply pimpl_any ].

Lemma compile_append :
  forall env F T {Wr: GoWrapper T} lvar vvar (x : T) xs,
  EXTRACT Ret (x :: xs)
  {{ vvar ~> x * lvar ~> xs * F }}
    Modify AppendOp (lvar, vvar)
  {{ fun ret => lvar ~> (x :: xs) * F }} // env.
Proof.
  unfold ProgOk; intros.
  repeat extract_var_val.
  inv_exec_progok.
  - find_apply_lem_hyp inj_pair2; subst.
    simpl in *.
    repeat find_rewrite.
    unfold append_impl, append_impl', update_one, id in *.
    repeat destruct_pair.
    repeat find_inversion_safe.
    simpl in *.
    rewrite ?eq_dec_eq in *.
    repeat find_inversion_safe.
    simpl in *.
    rewrite ?eq_dec_eq in *.
    destruct (can_alias wrap_type); simpl in *.
    + find_inversion.
      repeat eexists.
      eauto.
      rewrite ?add_upd.
      unfold pred_apply.
      eapply pimpl_apply; [ | eapply ptsto_upd ]; [ cancel_subset | ].
      eapply pimpl_apply; [ | eassumption ]; cancel_subset.
    + rewrite ?eq_dec_eq.
      find_inversion.
      repeat eexists.
      eauto.
      rewrite ?add_upd.
      unfold pred_apply.
      (* TODO: facts about [delete] *)
      (* eapply pimpl_apply; [ | eapply ptsto_upd ]; [ cancel_subset | ].*)
      admit.

  - contradiction H1.
    repeat eexists; econstructor.
    (* TODO: this is a mess *)
    all: unfold sel; simpl; repeat find_rewrite; try reflexivity; repeat (simpl; rewrite eq_dec_eq in * ); try reflexivity.
    simpl.
    rewrite ?eq_dec_eq in *.
    simpl.
    instantiate (Goal4 := ltac:(destruct (can_alias wrap_type))).
    destruct (can_alias wrap_type); simpl in *.
    + rewrite ?eq_dec_eq; reflexivity.
    + reflexivity.
Admitted.

Ltac unfold_expr :=
  unfold is_false, is_true, eval_bool, numop_impl', numop_impl,
         eval_test_m, eval_test_num, eval_test_bool,
         eval in *; simpl in *.

Ltac eval_expr :=
  repeat extract_var_val;
  repeat unfold_expr;
  simpl in *;
  repeat (match goal with
  | [e : ?x = _, H: context[match ?x with _ => _ end] |- _]
    => rewrite e in H
  | [e : ?x = _ |- context[match ?x with _ => _ end] ]
    => rewrite e
  | [H : context[if ?x then _ else _] |- _]
    => let H' := fresh in destruct x eqn:H'; try omega
  | [|- context[if ?x then _ else _] ]
    => let H' := fresh in destruct x eqn:H'; try omega
  end; simpl in *);
  repeat find_inversion_safe;
  simpl in *;
  unfold id in *;
  try solve[congruence | omega].

Ltac pred_cancel :=
  unfold pred_apply in *;
  match goal with
  | [H : _ |- _] => eapply pimpl_apply; [> | exact H]; solve [cancel_subset]
  end.

Lemma CompileFor : forall L G (L' : GoWrapper L) v loopvar F
                          (n i : W)
                          t0 term
                          env (pb : W -> L -> prog L) xpb nocrash oncrash,
    (forall t x,
        EXTRACT (pb x t)
  {{ loopvar ~> t * v ~> x * F }}
    xpb
  {{ fun ret => loopvar ~> ret * v ~> S x * F }} // env)
  ->
  EXTRACT (@ForN_ L G pb i n nocrash oncrash t0)
  {{ loopvar ~> t0 * v ~> i * term ~> (i + n) * F }}
    Go.While (TestE Lt (Var v) (Var term))
      (xpb)
  {{ fun ret => loopvar ~> ret * v ~> (i + n) * term ~> (i + n) * F }} // env.
Proof.
  (*
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
          pred_cancel.
          eauto.
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
          edestruct H4; eauto. simpl in *; repeat deex.
          destruct_pair; simpl in *.
          edestruct (IHn (S i));
            [> | | eapply Steps_ExecFailed; eauto |];
            rewrite ?plus_Snm_nSm; eauto.
          pred_cancel.
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
*)
Admitted.

Definition voidfunc2 A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) env :=
  forall avar bvar,
    forall a b, EXTRACT src a b
           {{ avar ~> a * bvar ~> b }}
             Call [] name [avar; bvar]
           {{ fun _ => emp (* TODO: could remember a & b if they are of aliasable type *) }} // env.


(* TODO: generalize for all kinds of functions *)
Lemma extract_voidfunc2_call :
  forall A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) arga argb arga_t argb_t env,
    forall and body ss,
      (forall a b, EXTRACT src a b {{ arga ~> a * argb ~> b }} body {{ fun _ => emp }} // env) ->
      StringMap.find name env = Some {|
                                    ParamVars := [(arga_t, arga); (argb_t, argb)];
                                    RetParamVars := [];
                                    Body := body;
                                    (* ret_not_in_args := rnia; *)
                                    args_no_dup := and;
                                    body_source := ss;
                                  |} ->
      voidfunc2 name src env.
Proof.
  unfold voidfunc2.
  intros A B C WA WB name src arga argb arga_t argb_t env and body ss Hex Henv avar bvar a b.
  specialize (Hex a b).
  intro.
  intros.
  intuition subst.
  - find_eapply_lem_hyp ExecFinished_Steps.
    find_eapply_lem_hyp Steps_runsto.
    invc H0.
    find_eapply_lem_hyp runsto_Steps.
    find_eapply_lem_hyp Steps_ExecFinished.
    rewrite Henv in H4.
    find_inversion_safe.
    subst_definitions. unfold sel in *. simpl in *. unfold ProgOk in *.
    repeat eforward Hex.
    forward Hex.
    shelve.
    forward_solve.
    simpl in *.
    do 2 eexists.
    intuition eauto.
    break_match.
    (*
    eauto.

    econstructor.
    econstructor.
  - find_eapply_lem_hyp ExecCrashed_Steps.
    repeat deex.
    invc H1; [ solve [ invc H2 ] | ].
    invc H0.
    rewrite Henv in H7.
    find_inversion_safe. unfold sel in *. simpl in *.
    assert (exists bp', (Go.step env)^* (d, callee_s, body) (final_disk, s', bp') /\ p' = InCall s [arga; argb] [] [avar; bvar] [] bp').
    {
      remember callee_s.
      clear callee_s Heqt.
      generalize H3 H2. clear. intros.
      prep_induction H3; induction H3; intros; subst.
      - find_inversion.
        eauto using rt1n_refl.
      - invc H0.
        + destruct st'.
          forwardauto IHclos_refl_trans_1n; deex.
          eauto using rt1n_front.
        + invc H3. invc H2. invc H.
    }
    deex.
    eapply Steps_ExecCrashed in H1.
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
      destruct st'. repeat eexists. econstructor; eauto.
      unfold sel; simpl in *.
      maps.
      find_all_cases.
      trivial.
    + invc H2.
      rewrite Henv in H8.
      find_inversion_safe. simpl in *.
      assert (exists bp', (Go.step env)^* (d, callee_s, body) (st', bp') /\ p' = InCall s [arga; argb] [] [avar; bvar] [] bp').
      {
        remember callee_s.
        clear callee_s Heqt.
        generalize H4 H0 H3. clear. intros.
        prep_induction H4; induction H4; intros; subst.
        - find_inversion.
          eauto using rt1n_refl.
        - invc H0.
          + destruct st'0.
            forwardauto IHclos_refl_trans_1n; deex.
            eauto using rt1n_front.
          + invc H4. contradiction H1. auto. invc H.
      }
      deex.
      eapply Steps_ExecFailed in H2.
      unfold ProgOk in *.
      repeat eforward Hex.
      forward Hex. shelve.
      forward_solve.
      intuition.
      contradiction H3.
      unfold is_final in *; simpl in *; subst.
      destruct st'. repeat eexists. eapply StepEndCall; simpl; eauto.
      intuition.
      contradiction H3.
      repeat deex; eauto.

  Unshelve.
  * simpl in *.
    maps.
    find_all_cases.
    find_inversion_safe.
    maps.
    find_all_cases.
    find_inversion_safe.
    eapply Forall_elements_remove_weaken.
    eapply forall_In_Forall_elements.
    intros.
    destruct (Nat.eq_dec k argb).
    subst. maps. find_inversion_safe.
    find_copy_eapply_lem_hyp NoDup_bool_sound.
    invc H.
    assert (arga <> argb).
    intro. subst. contradiction H2. constructor. auto.
    maps.
    intros. apply sumbool_to_bool_dec.
    maps.
  * (* argh *)
    simpl in *.
    subst_definitions.
    maps.
    find_all_cases.
    find_inversion_safe.
    maps.
    eapply Forall_elements_remove_weaken.
    eapply forall_In_Forall_elements.
    intros.
    destruct (Nat.eq_dec k argb).
    subst. maps. find_inversion_safe.
    find_copy_eapply_lem_hyp NoDup_bool_sound.
    invc H.
    assert (arga <> argb).
    intro. subst. contradiction H8. constructor. auto.
    find_cases avar s.
    find_cases bvar s.
    find_inversion_safe.
    maps.
    intros. apply sumbool_to_bool_dec.
    maps.
  * unfold sel in *; simpl in *.
    subst_definitions.
    simpl in *.
    find_cases avar s.
    find_cases bvar s.
    find_inversion_safe.
    maps.
    rewrite He in *.
    auto.
    eapply Forall_elements_remove_weaken.
    eapply forall_In_Forall_elements.
    intros.
    destruct (Nat.eq_dec k argb).
    subst. maps. find_inversion_safe.
    find_copy_eapply_lem_hyp NoDup_bool_sound.
    invc H.
    assert (arga <> argb).
    intro. subst. contradiction H9. constructor. auto.
    maps.
    rewrite He0 in *. auto.
    intros. apply sumbool_to_bool_dec.
    maps.
*)
Admitted.

Hint Constructors source_stmt.

Local Open Scope pred.

Ltac find_val v p :=
  match p with
    | context[?k ~> v] => constr:(Some k)
    | _ => constr:(@None var)
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
Local Hint Extern 0 (@find_ret ?T ?P) => (let x := find_ret_tac P in exact x) : typeclass_instances.
Ltac var_mapping_to_ret :=
  lazymatch goal with
    | [ |- EXTRACT _ {{ _ }} _ {{ fun ret : ?T => ?P }} // _ ] =>
      lazymatch constr:(fun ret : mark_ret T => (_:find_ret P)) with
        | (fun ret => ?var) => var
      end
  end.

Ltac compile_step :=
  match goal with
  | [ |- @sigT _ _ ] => eexists; intros
  | _ => eapply CompileBindDiscard
  | [ |- EXTRACT Bind ?p ?q {{ _ }} _ {{ _ }} // _ ] =>
    let v := fresh "var" in
    match type of p with (* TODO: shouldn't be necessary to type switch here *)
      | prog nat =>
        eapply CompileDeclare with (zeroval := 0) (t := Num)
      | prog valu =>
        eapply CompileDeclare with (zeroval := $0) (t := DiskBlock)
    end; auto; [ intro v; intros; eapply CompileBind; intros ]
  | _ => eapply CompileConst
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; [ cancel_subset ]
  | [ |- EXTRACT Read ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
    | Some ?k =>
      eapply hoare_strengthen_pre; [| eapply hoare_weaken_post; [ |
        eapply CompileRead with (avar := k) (vvar := retvar) ] ]; [ cancel_subset .. ]
    end
  | [ |- EXTRACT Write ?a ?v {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
    | Some ?ka =>
      match find_val v pre with
      | Some ?kv =>
        eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
          eapply CompileWrite with (avar := ka) (vvar := kv) ] ]; [ cancel_subset .. ]
      end
    end
  | [ H : voidfunc2 ?name ?f ?env |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // ?env ] =>
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken_post; [ | eapply hoare_strengthen_pre; [ |
              eapply H with (avar := ka) (bvar := kb) ] ]; [ cancel_subset .. ]
        end
    end
  | [ |- EXTRACT Ret (S ?a) {{ ?pre }} _ {{ _ }} // _ ] =>
    rewrite <- (Nat.add_1_r a)
  | [ |- EXTRACT Ret (?f ?a) {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
      | None => 
        eapply extract_equiv_prog; [
            let arg := fresh "arg" in
            set (arg := Ret (f a));
            pattern a in arg; subst arg;
            eapply bind_left_id | ]
    end
  | [ |- EXTRACT Ret (?a + ?b) {{ ?pre }} _ {{ _ }} // _ ] =>
    let retvar := var_mapping_to_ret in
    match find_val a pre with
      | Some ?ka =>
        match find_val b pre with
          | Some ?kb =>
            eapply hoare_weaken_post; [
            | eapply hoare_strengthen_pre;
              [ | (unify retvar ka; eapply CompileAddInPlace1 with (avar := ka) (bvar := kb)) ||
                  (unify retvar kb; eapply CompileAddInPlace2 with (avar := ka) (bvar := kb)) ||
                  eapply CompileAdd with (avar := ka) (bvar := kb) (sumvar := retvar) ] ];
            [ cancel_subset .. ]
        end
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

Ltac compile := repeat compile_step.

(*
Instance prog_equiv_equivalence T :
  Equivalence (@prog_equiv T).
Proof.
  split; hnf; unfold prog_equiv; firstorder.
  eapply H0. eapply H. trivial.
  eapply H. eapply H0. trivial.
Qed.
*)

Example micro_add_twice : sigT (fun p => forall x,
  EXTRACT Ret (1 + (2 + x))
  {{ 0 ~> x }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Defined.
Eval lazy in projT1 micro_add_twice.

Example micro_add_use_twice : sigT (fun p => forall x,
  EXTRACT Ret (x + (2 + x))
  {{ 0 ~> x }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Defined.
Eval lazy in projT1 micro_add_use_twice.

                                 
Example compile_one_read : sigT (fun p =>
  EXTRACT Read 1
  {{ 0 ~> $0 }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Defined.
Eval lazy in projT1 (compile_one_read).

Definition swap_prog a b :=
  va <- Read a;
  vb <- Read b;
  Write a vb;;
  Write b va;;
  Ret tt.

Example extract_swap_1_2 : forall env, sigT (fun p =>
  EXTRACT swap_prog 1 2 {{ emp }} p {{ fun _ => emp }} // env).
Proof.
  intros. unfold swap_prog.
  compile.
Defined.
Eval lazy in projT1 (extract_swap_1_2 (StringMap.empty _)).

Lemma extract_swap_prog : forall env, sigT (fun p =>
  forall a b, EXTRACT swap_prog a b {{ 0 ~> a * 1 ~> b }} p {{ fun _ => emp }} // env).
Proof.
  intros. unfold swap_prog.
  compile.
Defined.
Eval lazy in projT1 (extract_swap_prog (StringMap.empty _)).

Example extract_increment : forall env, sigT (fun p => forall i,
  EXTRACT (Ret (S i)) {{ 0 ~> i }} p {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros.
  compile.
Defined.
Eval lazy in projT1 (extract_increment (StringMap.empty _)).

(*
Declare DiskBlock
  (fun var0 : W =>
   (DiskRead var0 (Var 0);
    Declare DiskBlock
      (fun var1 : W =>
       (DiskRead var1 (Var 1);
        DiskWrite (Var 0) (Var var1);
        DiskWrite (Var 1) (Var var0);
        __)))%go)
*)

Opaque swap_prog.

Definition extract_swap_prog_corr env := projT2 (extract_swap_prog env).
Hint Resolve extract_swap_prog_corr : extractions.


Definition swap_env : Env :=
  ("swap" -s> {|
           ParamVars := [(Go.Num, 0); (Go.Num, 1)];
           RetParamVars := []; Body := projT1 (extract_swap_prog (StringMap.empty _));
           (* ret_not_in_args := ltac:(auto); *) args_no_dup := ltac:(auto); body_source := ltac:(repeat constructor);
         |}; (StringMap.empty _)).

Lemma swap_func : voidfunc2 "swap" swap_prog swap_env.
Proof.
  unfold voidfunc2.
  intros.
  eapply extract_voidfunc2_call; eauto with extractions.
  unfold swap_env; repeat rewrite ?StringMapFacts.add_eq_o, ?StringMapFacts.add_neq_o by congruence; reflexivity.
Qed.
Hint Resolve swap_func : funcs.

Definition call_swap :=
  swap_prog 0 1;;
  Ret tt.

Example extract_call_swap :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT call_swap {{ emp }} p {{ fun _ => emp }} // env).
Proof.
  intros.
  compile.
Defined.

Example extract_call_swap_top :
    sigT (fun p =>
          EXTRACT call_swap {{ emp }} p {{ fun _ => emp }} // swap_env).
Proof.
  apply extract_call_swap.
  auto with funcs.
Defined.
Eval lazy in projT1 (extract_call_swap_top).

Definition rot3_prog :=
  swap_prog 0 1;;
  swap_prog 1 2;;
  Ret tt.

Example extract_rot3_prog :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT rot3_prog {{ emp }} p {{ fun _ => emp }} // env).
Proof.
  intros.
  compile.
Defined.

Example extract_rot3_prog_top :
    sigT (fun p =>
          EXTRACT rot3_prog {{ emp }} p {{ fun _ => emp }} // swap_env).
Proof.
  apply extract_rot3_prog.
  auto with funcs.
Defined.
Eval lazy in projT1 (extract_rot3_prog_top).
(*
(Declare Num
   (fun var0 : W =>
    (var0 <~ Const Num 1;
     Declare Num
       (fun var1 : W =>
        (var1 <~ Const Num 0;
         Call [] "swap" [var1; var0]))));
 Declare Num
   (fun var0 : W =>
    (var0 <~ Const Num 2;
     Declare Num
       (fun var1 : W =>
        (var1 <~ Const Num 1;
         Call [] "swap" [var1; var0]))));
 __)%go
*)


Definition swap2_prog :=
  a <- Read 0;
  b <- Read 1;
  if weq a b then
    Ret tt
  else
    Write 0 b;;
    Write 1 a;;
    Ret tt.

(*
Example micro_swap2 : sigT (fun p =>
  EXTRACT swap2_prog {{ emp }} p {{ fun _ => emp }} // (StringMap.empty _)).
Proof.
  compile.

  eapply hoare_weaken_post; [ | eapply CompileIf with (condvar := "c0") (retvar := "r") ];
    try match_scopes; maps.

  apply GoWrapper_unit.
  compile. apply H.

  compile.
  eapply CompileWeq.

  shelve.
  shelve.
  shelve.

  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  intros.
  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  Unshelve.
  all: congruence.
Defined.
Eval lazy in projT1 micro_swap2.
*)