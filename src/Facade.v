Require Import ProofIrrelevance.
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
Require Import GoSep.

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
    (snd initial_state) ## initial_tstate ->
    forall out,
      Go.exec env (initial_state, eprog) out ->
    (forall final_state, out = Go.Finished final_state ->
      exists r hm',
        exec (fst initial_state) hm sprog (Finished (fst final_state) hm' r) /\
        (snd final_state) ## (final_tstate r)) /\
    (forall final_disk,
      out = Go.Crashed final_disk ->
      exists hm',
        exec (fst initial_state) hm sprog (Crashed T final_disk hm')) /\
    (out = Go.Failed ->
      exec (fst initial_state) hm sprog (Failed T)).

Notation "'EXTRACT' SP {{ A }} EP {{ B }} // EV" :=
  (ProgOk EV EP%go SP A%go_pred B%go_pred)
    (at level 60, format "'[v' 'EXTRACT'  SP '/' '{{'  A  '}}' '/'    EP '/' '{{'  B  '}}'  //  EV ']'").

Ltac GoWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | [ H : _ * _ |- _ ] => destruct H
                   | [ H : unit |- _ ] => destruct H
                   | [ H : _ = _ |- _ ] => inversion H; solve [eauto using inj_pair2]
                   | _ => solve [eauto using inj_pair2]
                   end).

Instance GoWrapper_Num : GoWrapper W.
Proof.
  refine {| wrap := Go.Val Go.Num;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_Bool : GoWrapper bool.
Proof.
  refine {| wrap := Go.Val Go.Bool;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_valu : GoWrapper valu.
Proof.
  refine {| wrap := Go.Val Go.DiskBlock;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_unit : GoWrapper unit.
Proof.
  refine {| wrap := Go.Val Go.EmptyStruct;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_dec {P Q} : GoWrapper ({P} + {Q}).
Proof.
  refine {| wrap := fun (v : {P} + {Q}) => if v then Go.Val Go.Bool true else Go.Val Go.Bool false;
            wrap_inj := _ |}.
  destruct v; destruct v'; intro; try eapply Go.value_inj in H; try congruence; intros; f_equal; try apply proof_irrelevance.
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
  {{ ∅ }}
    p
  {{ fun _ => ∅ }} // StringMap.empty _).
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
  repeat destruct_pair; repeat inv_exec; simpl in *;
  intuition (subst; try discriminate;
             repeat find_inversion_safe; repeat match_finds; repeat find_inversion_safe;  simpl in *;
               try solve [ exfalso; intuition eauto 10 ]; eauto 10).
(*
Example micro_write : sigT (fun p => forall a v,
  EXTRACT Write a v
  {{ 0 ~> a * 1 ~> v }}
    p
  {{ fun _ => ∅ }} // StringMap.empty _).
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

Lemma CompileConst : forall env A var (v v0 : nat),
  EXTRACT Ret v
  {{ var ~> v0 * A }}
    var <~ Go.Const Go.Num v
  {{ fun ret => var ~> ret * A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  do 2 eexists.
  intuition eauto.
  eapply ptsto_update; eauto.
  eapply pimpl_apply; eauto using pimpl_r.
  eapply ptsto_find in H.

  contradiction H1.
  repeat eexists.
  eauto.
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
  apply VarMapProperties.F.not_find_in_iff.
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
  instantiate (1 := S (list_max (keys l))).
  apply varmap_find_oob. omega.
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
    invc H5. (* TODO: make find_inversion_safe get this anyway *)
    invc H4.
    eauto.
  - invc H3; invc H4; eauto.
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


(* TODO: simplify wrapper system *)
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
      eauto using ptsto_update.
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

Lemma hoare_weaken_post : forall T env A (B1 B2 : T -> _) pr p,
  (forall x, B1 x =p=> B2 x)%go_pred ->
  EXTRACT pr
  {{ A }} p {{ B1 }} // env ->
  EXTRACT pr
  {{ A }} p {{ B2 }} // env.
Proof.
  unfold ProgOk.
  intros.
  forwardauto H0.
  intuition subst;
  forwardauto H3; repeat deex;
  repeat eexists; eauto using pimpl_apply.
Qed.

Lemma hoare_strengthen_pre : forall T env A1 A2 (B : T -> _) pr p,
  (A2 =p=> A1)%go_pred ->
  EXTRACT pr
  {{ A1 }} p {{ B }} // env ->
  EXTRACT pr
  {{ A2 }} p {{ B }} // env.
Proof.
  unfold ProgOk.
  eauto using pimpl_apply.
Qed.

Instance progok_hoare_proper :
  forall T env pr,
  Proper (@prog_equiv T ==> Basics.flip pimpl ==> pointwise_relation _ pimpl ==> Basics.impl) (@ProgOk T env pr).
Proof.
  intros.
  intros pr1 pr2 Hpr A1 A2 Hpre B1 B2 Hpost H.
  eauto using hoare_strengthen_pre, hoare_weaken_post, extract_equiv_prog.
Qed.

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

Example micro_inc : sigT (fun p => forall x,
  EXTRACT Ret (1 + x)
  {{ 0 ~> x }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  eexists.
  intros.
  instantiate (1 := (0 <~ Const Num 1 + Var 0)%go).
  intro. intros.
  inv_exec_progok.

  (*
  find_all_cases.
  simpl in *.
  repeat eexists; eauto. maps; eauto.
  simpl; congruence.
  eapply forall_In_Forall_elements.
  intros.
  rewrite remove_empty in *.
  maps.

  contradiction H1. repeat eexists. econstructor; simpl.
  maps. simpl in *. find_all_cases. eauto.
  eauto.
  maps. simpl in *. find_all_cases. eauto.
  eauto.
  trivial.
*)
Admitted.

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
    rewrite sep_star_assoc_1 in H.
    erewrite ptsto_find in H6 by eauto; simpl in *.
    repeat find_inversion_safe.
    rewrite sep_star_comm in H.
    rewrite sep_star_assoc_1 in H.
    erewrite ptsto_find in H9 by eauto; simpl in *.
    repeat find_inversion_safe.
    eauto.
    apply sep_star_assoc_2.
    apply ptsto_update.
    eapply pimpl_r.
    apply sep_star_assoc_1. eauto.
  }
  destruct (r a) as [p|] eqn:H'; eauto.
  destruct p.
  contradiction H1.
  repeat eexists; eauto.
  eapply StepDiskRead; eauto; unfold eval.
  (* TODO automate this *)
  rewrite sep_star_assoc_1 in H.
  eapply ptsto_find in H. eauto. auto.
  rewrite sep_star_assoc_1 in H.
  rewrite sep_star_comm in H.
  rewrite sep_star_assoc_1 in H.
  eapply ptsto_find in H. eauto.
Qed.

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
    rewrite sep_star_assoc_1 in H.
    erewrite ptsto_find in H6 by eauto; simpl in *.
    repeat find_inversion_safe.
    rewrite sep_star_comm in H.
    rewrite sep_star_assoc_1 in H.
    erewrite ptsto_find in H8 by eauto; simpl in *.
    repeat find_inversion_safe.
    eauto.
  }
  destruct (r a) as [p|] eqn:H'; eauto.
  destruct p.
  contradiction H1.
  repeat eexists; eauto.
  eapply StepDiskWrite; eauto; unfold eval.
  (* TODO automate this *)
  rewrite sep_star_assoc_1 in H.
  eapply ptsto_find in H. eauto.
  rewrite sep_star_assoc_1 in H.
  rewrite sep_star_comm in H.
  rewrite sep_star_assoc_1 in H.
  eapply ptsto_find in H. eauto.
Qed.

Lemma CompileFor : forall L G (L' : GoWrapper L) v loopvar F
                          (i n : W)
                          t0 term
                          env (pb : W -> L -> prog L) xpb nocrash oncrash,
  loopvar <> v ->
  (forall x A t,
  EXTRACT (pb x t)
  {{ loopvar ~> t * v ~> x * A }}
    xpb
  {{ fun ret => loopvar ~> ret * v ~> x * A }} // env)
  ->
  term = Const Num (i + n) ->
  EXTRACT (@ForN_ L G pb i n nocrash oncrash t0)
  {{ loopvar ~> t0 * v ~> i * F }}
    Go.For v term xpb
  {{ fun ret => loopvar ~> ret * v ~> (i + n) * F }} // env.
Proof.
  intros L G L' v loopvar F i n.
  generalize dependent i.
  induction n; intros; simpl.
  subst term.
  rewrite <- plus_n_O.
  unfold ProgOk. intros.
  inv_exec.
  {
    inv_exec; [| inv_exec_progok].
    rewrite sep_star_assoc_1 in H1.
    rewrite sep_star_comm in H1.
    rewrite sep_star_assoc_1 in H1.
    eapply ptsto_find in H1.
    unfold is_true in *; simpl in *.
    unfold eval_bool in *; simpl in *.
    unfold eval_test_m in *; simpl in *.
    rewrite H1 in H9.
    destruct Compare_dec.lt_dec. omega.
    find_inversion.
  }
  inv_exec_progok.
  admit.
  inv_exec_progok. subst.
  rewrite sep_star_assoc_1.
  (* need to rewrite sep_star assoc in postcondition *)
  admit.
Admitted.

Definition voidfunc2 A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) env :=
  forall avar bvar,
    forall a b, EXTRACT src a b
           {{ avar ~> a * bvar ~> b }}
             Call [] name [avar; bvar]
           {{ fun _ => ∅ (* TODO: could remember a & b if they are of aliasable type *) }} // env.


Lemma extract_voidfunc2_call :
  forall A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) arga argb arga_t argb_t env,
    forall and body ss,
      (forall a b, EXTRACT src a b {{ arga ~> a * argb ~> b }} body {{ fun _ => ∅ }} // env) ->
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

Local Open Scope go_pred.

Ltac remove_anys :=
  repeat match goal with
    | [ |- ?p_ =p=> ?q ] =>
        match p_ with
          | context[any * ?x] => etransitivity; [ rewrite any_r_2 with (p := x); reflexivity | ]
          | context[?x * any] => etransitivity; [ rewrite any_l_2 with (p := x); reflexivity | ]
        end ||
        match q with
          | context[any * ?x] => etransitivity; [ | rewrite <- any_r_1 with (p := x); reflexivity ]
          | context[?x * any] => etransitivity; [ | rewrite <- any_l_1 with (p := x); reflexivity ]
        end
  end.

Ltac flatten :=
  remove_anys;
  etransitivity; [ eapply any_r_1 | etransitivity; [ | eapply any_r_2 ]];
  repeat match goal with
    | [ |- context[?a * (?b * ?c)] ] => rewrite sep_star_assoc_2 with (p1 := a) (p2 := b) (p3 := c)
  end;
  repeat match goal with
    | [ |- context[?a * (?b * ?c)] ] => rewrite <- sep_star_assoc_1 with (p1 := a) (p2 := b) (p3 := c)
  end.

Lemma swap_on_right :
  forall a b c,
    a * b * c =p=> a * c * b.
Proof.
  intros.
  rewrite sep_star_assoc_1.
  rewrite sep_star_comm with (p1 := b) (p2 := c).
  rewrite sep_star_assoc_2.
  reflexivity.
Qed.

Lemma next_right_l :
  forall p q1 q2 r,
    p =p=> (q1 * r) * q2 ->
    p =p=> q1 * (q2 * r).
Proof.
  intros.
  rewrite <- sep_star_comm with (p1 := r) (p2 := q2).
  rewrite <- sep_star_assoc_1.
  assumption.
Qed.

Lemma cancel_one_right_l :
  forall p q1 q2 k v,
    p =p=> q1 * q2 ->
    p * k |-> v =p=> q1 * (q2 * k |-> v).
Proof.
  intros.
  rewrite <- sep_star_assoc_1.
  eapply pimpl_cancel_one.
  assumption.
Qed.

Ltac cancel_one_l' :=
  match goal with
    | [ |- _ =p=> _ * (_ * ?r) ] =>
      not_evar r; apply cancel_one_right_l; repeat apply next_right_l;
           try rewrite <- sep_star_comm with (p1 := any)
  end
    || (apply next_right_l; cancel_one_l').

Ltac add_to_frame p :=
  match goal with
    | [ |- context[?F] ] =>
      match type of F with
        | pred =>
          is_evar F;
            let F' := fresh "F" in
            evar (F' : pred);
          unify F (p * F'); subst F'
      end
  end;
  match goal with
    | [ |- _ =p=> ?q ] =>
      match q with
        | context[?p1_ * (p * ?p3_)] =>
          rewrite <- sep_star_assoc_1 with (p1 := p1_) (p2 := p) (p3 := p3_)
      end
  end.

Ltac cancel_one_l :=
  match goal with
    | [ |- _ * ?l =p=> _ ] =>
       cancel_one_l' || (add_to_frame l; cancel_one_l')
  end.

Ltac cancel_all_l :=
  simpl; intros;
  flatten;
  etransitivity; [ | apply any_r_2 ];
  repeat cancel_one_l;
  remove_anys; try reflexivity.

Lemma next_right_r :
  forall p1 p2 r q,
    (p1 * r) * p2 =p=> q ->
    p1 * (p2 * r) =p=> q.
Proof.
  intros.
  rewrite sep_star_comm with (p1 := p2) (p2 := r).
  rewrite sep_star_assoc_2.
  assumption.
Qed.

Lemma cancel_one_right_r :
  forall p1 p2 q k v,
    p1 * p2 =p=> q ->
    p1 * (p2 * k |-> v) =p=> q * k |-> v.
Proof.
  intros.
  rewrite sep_star_assoc_2.
  eapply pimpl_cancel_one.
  assumption.
Qed.

Ltac cancel_one_r :=
  (match goal with
     | [ |- _ * (_ * ?r) =p=> _ ] =>
       not_evar r;
     apply cancel_one_right_r; repeat apply next_right_r;
     try rewrite <- sep_star_comm with (p1 := any)
   end) || (apply next_right_r; cancel_one_r).

Ltac cancel_all_r :=
  simpl; intros;
  flatten;
  etransitivity; [ apply any_r_1 | ];
  repeat cancel_one_r;
  remove_anys; try apply pimpl_any.

Ltac find_val v p :=
  match p with
    | context[?k ~> v] => constr:(Some k)
    | _ => constr:(@None var)
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
    end; auto; [ intro v; intros; eapply CompileBind with (var := v); intros ]
  | _ => eapply CompileConst
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; cancel_all_r
  | [ |- EXTRACT Read ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
    | Some ?k =>
      eapply hoare_strengthen_pre; [
      | eapply hoare_weaken_post; [ | eapply CompileRead ] ]; [ cancel_all_l | cancel_all_r ]
    end
  | [ |- EXTRACT Write ?a ?v {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
    | Some ?ka =>
      match find_val v pre with
      | Some ?kv =>
        eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
          eapply CompileWrite with (avar := ka) (vvar := kv) ]]; [ cancel_all_l | cancel_all_r ]
      end
    end
      (*
  | [ H : voidfunc2 ?name ?f ?env |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // ?env ] =>
    match find_fast a pre with
      | Some ?ka =>
        match find_fast b pre with
            | Some ?kb =>
              eapply hoare_weaken_post; [ | eapply hoare_strengthen_pre; [ |
                eapply H ] ]; try match_scopes; maps
        end
    end
*)
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

Example compile_one_read : sigT (fun p =>
  EXTRACT Read 1
  {{ 0 ~> $0 }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Admitted.
Eval lazy in projT1 (compile_one_read).

Definition swap_prog a b :=
  va <- Read a;
  vb <- Read b;
  Write a vb;;
  Write b va;;
  Ret tt.

Example extract_swap_1_2 : forall env, sigT (fun p =>
  EXTRACT swap_prog 1 2 {{ ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros. unfold swap_prog.
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
  match goal with 
  | [ |- EXTRACT Read ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_val a pre with
    | Some ?k =>
      eapply hoare_strengthen_pre; [
      | eapply hoare_weaken_post; [ | eapply CompileRead with (avar := k) ] ]
    end                               
  end.
  cancel_all_l.
  cancel_all_r.
  (* ooops. argh. *)
Admitted.
(* Eval lazy in projT1 (extract_swap_1_2 (StringMap.empty _)).


Lemma extract_swap_prog : forall env, sigT (fun p =>
  forall a b, EXTRACT swap_prog a b {{ 0 ~> a; 1 ~> b; ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros. unfold swap_prog.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  subst.
  instantiate (F := 0 ~> a; var0 ~> a0; ∅).
  all: maps; auto.

  compile_step.
  compile_step.
  instantiate (F := 1 ~> b; var0 ~> a0; ∅).
  all: maps; auto.

  compile_step.
  match goal with
  | [ |- EXTRACT Write ?a ?v {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
    | Some ?ka =>
      match find_fast v pre with
      | Some ?kv =>
        eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
          eapply CompileWrite with (avar := ka) (vvar := kv) ]]
      end
    end
  end.
  instantiate (F := var1 ~> a1; 0 ~> a; ∅).
  match_scopes.
  match_scopes.
  destruct (Nat.eq_dec 1 var0); maps.

  compile_step.
Defined.
Eval lazy in projT1 (extract_swap_prog (StringMap.empty _)).

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
  unfold swap_env; map_rewrites. auto.
Qed.
Hint Resolve swap_func : funcs.

Definition call_swap :=
  swap_prog 0 1;;
  Ret tt.

Example extract_call_swap :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT call_swap {{ ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros.
  compile.
Defined.

Example extract_call_swap_top :
    sigT (fun p =>
          EXTRACT call_swap {{ ∅ }} p {{ fun _ => ∅ }} // swap_env).
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
          EXTRACT rot3_prog {{ ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros.
  compile.
Defined.

Example extract_rot3_prog_top :
    sigT (fun p =>
          EXTRACT rot3_prog {{ ∅ }} p {{ fun _ => ∅ }} // swap_env).
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


(*
Definition swap2_prog :=
  a <- Read 0;
  b <- Read 1;
  if weq a b then
    Ret tt
  else
    Write 0 b;;
    Write 1 a;;
    Ret tt.

Example micro_swap2 : sigT (fun p =>
  EXTRACT swap2_prog {{ ∅ }} p {{ fun _ => ∅ }} // (StringMap.empty _)).
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
*)
*)