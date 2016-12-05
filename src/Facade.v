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


Ltac invert_trivial H :=
  match type of H with
    | ?con ?a = ?con ?b =>
      let H' := fresh in
      assert (a = b) as H' by exact (match H with eq_refl => eq_refl end); clear H; rename H' into H
  end.

Lemma some_inj :
  forall A (x y : A), Some x = Some y -> x = y.
Proof.
  intros. find_inversion. auto.
Qed.

Lemma pair_inj :
  forall A B (a1 a2 : A) (b1 b2 : B), (a1, b1) = (a2, b2) -> a1 = a2 /\ b1 = b2.
Proof.
  intros. find_inversion. auto.
Qed.

Lemma Val_type_inj :
  forall t1 t2 v1 v2, Go.Val t1 v1 = Go.Val t2 v2 -> t1 = t2.
Proof.
  intros. find_inversion. auto.
Qed.

Lemma Here_inj :
  forall T (a b : T), Go.Here a = Go.Here b -> a = b.
Proof.
  intros. find_inversion. auto.
Qed.

Ltac find_inversion_safe :=
  match goal with
    | [ H : wrap _ = Go.Val _ _ |- _ ] => unfold wrap in H; simpl in H; unfold id in H
    | [ H : Go.Val _ _ = wrap _ |- _ ] => unfold wrap in H; simpl in H; unfold id in H
    | [ H : Some ?x = Some ?y |- _ ] => apply some_inj in H; try (subst x || subst y)
    | [ H : Go.Val ?ta ?a = Go.Val ?tb ?b |- _ ] =>
      (unify ta tb; unify a b; fail 1) ||
      assert (ta = tb) by (eapply Val_type_inj; eauto); try (subst ta || subst tb);
      assert (a = b) by (eapply Go.value_inj; eauto); clear H; try (subst a || subst b)
    | [ H : ?X ?a = ?X ?b |- _ ] =>
      (unify a b; fail 1) ||
      let He := fresh in
      assert (a = b) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; subst
    | [ H : ?X ?a1 ?a2 = ?X ?b1 ?b2 |- _ ] =>
      (unify a1 b1; unify a2 b2; fail 1) ||
      let He := fresh in
      assert (a1 = b1 /\ a2 = b2) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; destruct He as [? ?]; subst
    | [ H : (?a, ?b) = (?c, ?d) |- _ ] =>
      apply pair_inj in H; destruct H; try (subst a || subst c); try (subst b || subst d)
    | [ H : Go.Here ?a = Go.Here ?b |- _ ] =>
      apply Here_inj in H; try (subst a || subst b)
  end.

Create HintDb gowrapper discriminated.

Hint Resolve wrap_inj : gowrapper.

Ltac GoWrapper_finish :=
  solve [simpl; (f_equal + idtac); eauto using inj_pair2 with gowrapper].

Ltac GoWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | _ => progress (repeat find_inversion_safe)
                   | [ H : unit |- _ ] => destruct H
                   | [ H : _ * _ |- _ ] => destruct H
                   | _ => GoWrapper_finish
                   end).

Instance GoWrapper_Num : GoWrapper W.
Proof.
  refine {| wrap' := Go.Here;
            wrap_type := Go.Num |}; GoWrapper_t.
Defined.

Instance GoWrapper_Bool : GoWrapper bool.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.Bool |}; GoWrapper_t.
Defined.

Instance GoWrapper_valu : GoWrapper valu.
Proof.
  refine {| wrap' := Go.Here;
            wrap_type := Go.DiskBlock |}; GoWrapper_t.
Defined.

Instance GoWrapper_unit : GoWrapper unit.
Proof.
  refine {| wrap' := id;
            wrap_type := Go.EmptyStruct |}; GoWrapper_t.
Defined.

Instance GoWrapper_pair {A B} {WA : GoWrapper A} {WB : GoWrapper B} : GoWrapper (A * B).
Proof.
  refine {| wrap' := fun p => (wrap' (fst p), wrap' (snd p));
            wrap_type := Go.Pair (@wrap_type _ WA) (@wrap_type _ WB) |}; GoWrapper_t.
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
  refine {| wrap' := fun l => Go.Here (map wrap' l);
            wrap_type := Go.Slice wrap_type |}; GoWrapper_t.
Defined.

Instance GoWrapper_option {A} {WA : GoWrapper A} : GoWrapper (option A).
Proof.
  refine {| wrap' := fun o => match o with
                              | None => (false, Go.default_value' _)
                              | Some x => (true, wrap' x) end;
            wrap_type := Go.Pair Go.Bool (@wrap_type _ WA)|}.
  intros a b H.
  destruct a, b; invc H; GoWrapper_t.
Defined.

Instance GoWrapper_dec {P Q} : GoWrapper ({P} + {Q}).
Proof.
  refine {| wrap' := fun (v : {P} + {Q}) => if v then true else false;
            wrap_type := Go.Bool |}.
  intros.
  destruct a1, a2; f_equal; try discriminate; apply proof_irrelevance.
Qed.


Instance GoWrapper_addrmap {T} {WT : GoWrapper T} : GoWrapper (Go.Map.t T).
Proof.
  refine {| wrap_type := Go.AddrMap (@wrap_type _ WT);
            wrap' := fun m => Go.Here (Go.Map.map (@wrap' _ WT) m) |}.
  intros.
  apply MapUtils.addrmap_equal_eq.
  pose proof (MapUtils.AddrMap.MapFacts.Equal_refl
    (Go.Map.map wrap' a1)) as H0.
  find_inversion_safe. rewrite H in H0 at 2.
  eapply MoreAddrMapFacts.map_inj_equal; eauto.
  exact (@wrap_inj _ WT).
Defined.

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
    | [ H1: VarMap.find ?a ?s = ?v1, H2: VarMap.find ?a ?s = ?v2 |- _ ] => rewrite H1 in H2;
      (find_inversion_safe || invc H2 || idtac)
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
  find_eapply_lem_hyp sep_star_ptsto_some.
  eauto.
Qed.

Hint Resolve sep_star_ptsto_some_find.

Ltac extract_var_val_from H P s :=
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
  end.

Ltac extract_var_val :=
  lazymatch goal with
  | [ H: ?s ≲ ?P |- _ ] => extract_var_val_from H P s
  | [ H: (?P)%pred (mem_of ?s) |- _ ] => extract_var_val_from H P s
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

Ltac forwardauto1 H :=
  repeat eforward H; conclude H eauto.

Ltac forwardauto H :=
  forwardauto1 H; repeat forwardauto1 H.

Ltac forward_solve_step :=
  match goal with
    | _ => progress intuition eauto
    | [ H : forall _, _ |- _ ] => forwardauto H
    | _ => deex
    | _ => discriminate
  end.

Ltac forward_solve :=
  repeat forward_solve_step.

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
  unfold wrap in *; simpl in *.
  repeat find_inversion_safe.
  rewrite add_upd.
  eapply ptsto_upd.
  eassumption.

  contradiction H1.
  repeat eexists.
  eapply Go.StepModify.
  eapply sep_star_ptsto_some in H.
  unfold Go.sel; simpl.
  unfold mem_of in *.
  rewrite H.
  trivial.
  all: simpl; reflexivity.
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
  forward_solve.
  - invc H4;
    repeat find_apply_lem_hyp inj_pair2; repeat subst;
    eauto.
    invc H14.
  - invc H0.
    repeat find_apply_lem_hyp inj_pair2; repeat subst.
    invc H10.
  - invc H5.
    repeat find_apply_lem_hyp inj_pair2; repeat subst.
    invc H10.

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
  forward_solve.
  - invc H4;
    repeat find_apply_lem_hyp inj_pair2; repeat subst;
    eauto.
    invc H14.
  - invc H0.
    repeat find_apply_lem_hyp inj_pair2; repeat subst.
    invc H10.
  - invc H5.
    repeat find_apply_lem_hyp inj_pair2; repeat subst.
    invc H10.

  Unshelve.
  all: auto.
Qed.

Lemma CompileConst' : forall env A var (v v0 : nat),
  EXTRACT Ret tt
  {{ var ~> v0 * A }}
    var <~const v
  {{ fun _ => var ~> v * A }} // env.
Proof.
  eauto using CompileRet, CompileConst.
Qed.

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

Class DefaultValue T {Wrapper : GoWrapper T} :=
  {
    zeroval : T;
    default_zero : wrap zeroval = Go.default_value wrap_type;
  }.

Arguments DefaultValue T {Wrapper}.

Definition prod' := prod.

Ltac cancel_go :=
  simpl in *;
  fold prod' in *;
  cancel; cancel.

Lemma ptsto_upd_disjoint' : forall (F : pred) a v m,
  F m -> m a = None
  -> (a |-> v * F)%pred (upd m a v).
Proof.
  intros.
  eapply pred_apply_pimpl_proper; [ reflexivity | | eapply ptsto_upd_disjoint; eauto ].
  cancel.
Qed.

Lemma ptsto_delete' : forall a (F :pred) (m : mem),
  (a |->? * F)%pred m -> F (delete m a).
Proof.
  intros.
  apply pimpl_exists_r_star_r in H.
  unfold exis in H.
  deex.
  eapply ptsto_delete; eauto.
Qed.

Ltac pred_solve_step := match goal with
  | [ |- ( ?P )%pred (upd _ ?a ?x) ] =>
    match P with
    | context [(a |-> ?x)%pred] =>
      eapply pimpl_apply with (p := (a |-> x * _)%pred);
      [ cancel_go | (eapply ptsto_upd_disjoint'; solve [eauto]) || eapply ptsto_upd ]
    | context [(@ptsto ?AT ?AEQ ?V a ?y)%pred] =>
      let H := fresh in
      assert (@okToUnify AT AEQ V (ptsto a y) (ptsto a x)) as H;
      [ eauto with okToUnify | rewrite H ]
    end
  | [ |- ( ?P )%pred (delete _ ?a) ] =>
    eapply ptsto_delete' with (F := P)
  | [ H : _%pred ?t |- _%pred ?t ] => pred_apply; solve [cancel_go]
  | _ => solve [cancel_go]
  end.

Ltac pred_solve := progress (
  unfold pred_apply in *;
  repeat pred_solve_step;
  repeat rewrite ?add_upd, ?remove_delete, ?default_zero;
  repeat pred_solve_step).

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

    specialize (H var (r, var ->> Go.default_value wrap_type; l) hm).
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
    specialize (H var (r, var ->> Go.default_value wrap_type; l) hm).
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
    specialize (H var (r, var ->> Go.default_value wrap_type; l) hm).
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

Import Go.

Lemma hoare_weaken_post : forall T env A (B1 B2 : T -> _) pr p,
  (forall x, B1 x =p=> B2 x)%pred ->
  EXTRACT pr
  {{ A }} p {{ B1 }} // env ->
  EXTRACT pr
  {{ A }} p {{ B2 }} // env.
Proof.
  unfold ProgOk.
  intros.
  forwardauto H0.
  intuition subst.
  forwardauto H3; repeat deex;
  repeat eexists; eauto.
  unfold pred_apply in *.
  pred_apply.
  rewrite H.
  eauto.
  eauto.
  eauto.
Qed.

Lemma hoare_strengthen_pre : forall T env A1 A2 (B : T -> _) pr p,
  (A2 =p=> A1)%pred ->
  EXTRACT pr
  {{ A1 }} p {{ B }} // env ->
  EXTRACT pr
  {{ A2 }} p {{ B }} // env.
Proof.
  unfold ProgOk, pred_apply in *; intros.
  apply H in H1.
  forward_solve.
Qed.

Lemma hoare_weaken : forall T env A1 A2 (B1 B2 : T -> _) pr p,
  EXTRACT pr
  {{ A1 }} p {{ B1 }} // env ->
  (A2 =p=> A1)%pred ->
  (forall x, B1 x =p=> B2 x)%pred ->
  EXTRACT pr
  {{ A2 }} p {{ B2 }} // env.
Proof.
  eauto using hoare_strengthen_pre, hoare_weaken_post.
Qed.


Inductive Declaration :=
| Decl (T : Type) {Wr: GoWrapper T} {D : DefaultValue T}.

Arguments Decl T {Wr} {D}.

Fixpoint n_tuple_unit n (T : Type) : Type :=
  match n with
  | 0 => unit
  | S n' => n_tuple_unit n' T * T
  end.

Definition decls_pre (decls : list Declaration) (vars : n_tuple_unit (length decls) var) : pred.
  induction decls; simpl in *.
  - exact emp.
  - destruct a.
    exact ((snd vars |-> wrap zeroval * IHdecls (fst vars))%pred).
Defined.

Definition decls_post (decls : list Declaration) (vars : n_tuple_unit (length decls) var) : pred.
  induction decls; simpl in *.
  - exact emp.
  - exact ((snd vars |->? * IHdecls (fst vars))%pred).
Defined.

Lemma decls_pre_impl_post :
  forall decls vars,
    decls_pre decls vars =p=> decls_post decls vars.
Proof.
  induction decls; simpl in *; intros.
  - auto.
  - destruct a.
    cancel. auto.
Qed.

Definition many_declares (decls : list Declaration) (xp : n_tuple_unit (length decls) var -> stmt) : stmt.
  induction decls; simpl in *.
  - exact (xp tt).
  - destruct a.
    eapply (Declare wrap_type); intro var.
    apply IHdecls; intro.
    apply xp.
    exact (X, var).
Defined.

Lemma CompileDeclareMany :
  forall env T (decls : list Declaration) xp A B (p : prog T),
    (forall vars : n_tuple_unit (length decls) var,
       EXTRACT p
       {{ decls_pre decls vars * A }}
         xp vars
       {{ fun ret => decls_post decls vars * B ret }} // env) ->
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
Qed.


Instance progok_hoare_proper :
  forall T env pr,
  Proper (@prog_equiv T ==> Basics.flip pimpl ==> pointwise_relation _ pimpl ==> Basics.impl) (@ProgOk T env pr).
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
      contradiction H5.
      repeat eexists. eauto.
      intuition. repeat deex.
      contradiction H5. eauto.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forwardauto H. intuition.
      forwardauto H3. repeat deex.
      forward_solve.

  Unshelve.
  all: auto.
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
  eapply extract_equiv_prog.
  instantiate (pr1 := Ret tt;; p).
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
    (* [forward_solve] is not really good enough *)
    forwardauto H. intuition.
    forwardauto H2. repeat deex.
    forward_solve.
    invc H8; repeat (find_apply_lem_hyp inj_pair2; subst); [ | invc H18 ]; eauto.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H4. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forwardauto H. intuition.
      forwardauto H2. repeat deex.
      forward_solve.
      invc H0.
      repeat (find_apply_lem_hyp inj_pair2; subst).
      invc H15.

  - find_eapply_lem_hyp ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + eapply Steps_ExecFailed in H4; eauto.
      forward_solve.
      unfold is_final; simpl; intuition subst.
      contradiction H5.
      repeat eexists. eauto.
      intuition. repeat deex.
      contradiction H5. eauto.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forwardauto H. intuition.
      forwardauto H3. repeat deex.
      forward_solve.
      invc H10.
      repeat (find_apply_lem_hyp inj_pair2; subst).
      invc H15.

  Unshelve.
  all: auto.
Qed.

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

Ltac unfold_expr :=
  match goal with
  | [H : _ |- _ ] =>
      progress (unfold is_false, is_true, eval_bool,
         numop_impl', numop_impl,
         split_pair_impl, split_pair_impl',
         join_pair_impl, join_pair_impl',
         map_add_impl, map_add_impl',
         map_remove_impl, map_remove_impl',
         map_find_impl, map_find_impl',
         map_card_impl, map_card_impl',
         map_elements_impl, map_elements_impl',
         eval_test_m, eval_test_num, eval_test_bool,
         update_one, setconst_impl, duplicate_impl,
         sel, id, eval, eq_rect_r, eq_rect
         in H); simpl in H
  | _ => progress (unfold is_false, is_true, eval_bool,
         numop_impl', numop_impl,
         split_pair_impl, split_pair_impl',
         join_pair_impl, join_pair_impl',
         map_add_impl, map_add_impl',
         map_remove_impl, map_remove_impl',
         map_find_impl, map_find_impl',
         map_card_impl, map_card_impl',
         map_elements_impl, map_elements_impl',
         eval_test_m, eval_test_num, eval_test_bool,
         update_one, setconst_impl, duplicate_impl,
         sel, id, eval, eq_rect_r, eq_rect
         ); simpl
  end.


Ltac deex_hyp H :=
  match type of H with
  | exists varname, _ =>
    let varname' := fresh varname in
    destruct H as (varname', H); intuition subst
  end.

Ltac extract_pred_apply_exists :=
  match goal with
  | [ H : _ ≲ _ |- _ ] =>
    repeat setoid_rewrite pimpl_exists_l_star_r in H;
    repeat setoid_rewrite pimpl_exists_r_star_r in H;
      unfold pred_apply, exis in H; deex_hyp H; repeat deex_hyp H
  end.

Ltac eval_expr_step :=
    repeat extract_var_val;
    repeat (destruct_pair + unfold_expr); simpl in *;
    try extract_pred_apply_exists;
    try subst;
    match goal with
    | [H : context [match ?e in (_ = _) return _ with _ => _ end] |- _ ]
      => rewrite (proof_irrelevance _ e (eq_refl)) in H
    | [H : context [eq_sym ?t] |- _ ]
      => setoid_rewrite (proof_irrelevance _ t eq_refl) in H
    | [e : ?x = _, H: context[match ?x with _ => _ end] |- _]
      => rewrite e in H
    | [e : ?x = _ |- context[match ?x with _ => _ end] ]
      => rewrite e
    | [H : context[if ?x then _ else _] |- _]
      => let H' := fresh in destruct x eqn:H'; try omega
    | [|- context[if ?x then _ else _] ]
      => let H' := fresh in destruct x eqn:H'; try omega
    | [H : context [match ?x with _ => _ end],
       H': _ = ?x |- _]
      => rewrite <- H' in H
    | [H : context [match ?x with _ => _ end],
       H': ?x = _ |- _]
      => rewrite H' in H
    | [H : context [match ?x with _ => _ end] |- _]
      => let H' := fresh in destruct x eqn:H'
    | [ |- context [match ?e in (_ = _) return _ with _ => _ end] ]
      => rewrite (proof_irrelevance _ e (eq_refl))
    | [ |- context [eq_sym ?t] ]
      => setoid_rewrite (proof_irrelevance _ t eq_refl)
    | [ |- context [match ?x with _ => _ end] ]
      => let H' := fresh in destruct x eqn:H'
    | _
      => idtac
    end; try solve [congruence | omega];
    repeat find_inversion_safe.

Ltac eval_expr := repeat eval_expr_step.

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
    eval_expr.
    repeat eexists; eauto.
    pred_solve.
  }
  destruct (r a) as [p|] eqn:H'; eauto.
  destruct p.
  contradiction H1.
  repeat econstructor; eauto.
  all : eval_expr; eauto.
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
    eval_expr.
    repeat eexists; eauto.
  }
  destruct (r a) as [p|] eqn:H'; eauto.
  destruct p.
  contradiction H1.
  repeat eexists; eauto.
  econstructor; eauto.
  all : eval_expr; eauto.
Qed.


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
  eval_expr.
  repeat econstructor.
  pred_solve.
  contradiction H1.
  repeat econstructor.

  eval_expr.
  all: simpl; reflexivity.
Qed.

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
  eval_expr.
  repeat econstructor.
  pred_solve.

  contradiction H1.
  repeat econstructor.

  eval_expr.
  all: simpl; reflexivity.
Qed.

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
  eval_expr.
  repeat econstructor.
  pred_solve.
  contradiction H1.
  repeat econstructor.

  eval_expr.
  all: simpl; reflexivity.
Qed.

Lemma CompileAppend :
  forall env F T {Wr: GoWrapper T} (lvar vvar : var) (x : T) xs,
  EXTRACT Ret (x :: xs)
  {{ vvar ~> x * lvar ~> xs * F }}
    Modify AppendOp (lvar, vvar)
  {{ fun ret => vvar |-> moved_value (wrap x) * lvar ~> ret * F }} // env.
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
    simpl in *. subst.
    rewrite ?eq_dec_eq in *.
    repeat find_inversion_safe.
    simpl in *.
    rewrite ?eq_dec_eq in *.
    repeat find_inversion_safe.
    destruct (can_alias wrap_type); simpl in *.
    + rewrite ?eq_dec_eq in *. simpl in *. find_inversion; simpl in *.
      repeat eexists.
      eauto.
      pred_solve.
    + rewrite ?eq_dec_eq in *; simpl in *.
      find_inversion.
      repeat econstructor.
      pred_solve.

  - contradiction H1.
    repeat eexists; econstructor.
    unfold append_impl'. simpl.
    (* TODO: this is a mess *)
    all: unfold sel; simpl; repeat find_rewrite; try reflexivity; repeat (simpl; rewrite eq_dec_eq in * ); try reflexivity.
    simpl.
    rewrite ?eq_dec_eq in *.
    simpl.
    instantiate (1 := ltac:(destruct (can_alias wrap_type))).
    destruct (can_alias wrap_type); simpl in *.
    + rewrite ?eq_dec_eq; reflexivity.
    + reflexivity.
Qed.

Ltac pred_cancel :=
  unfold pred_apply in *;
  match goal with
  | [H : _ |- _] => eapply pimpl_apply; [> | exact H]; solve [cancel_go]
  end.

Lemma map_add_okToUnify : forall AT AEQ {T} {Wr : GoWrapper T} var m k (v : T),
  (@okToUnify AT AEQ value (var ~> Map.add k v m)
  (var |-> (Val (AddrMap wrap_type) (Here (Map.add k (wrap' v) (Map.map wrap' m))))))%pred.
Proof.
  intros. unfold okToUnify.
  unfold wrap. simpl. repeat f_equal.
  eauto using MapUtils.addrmap_equal_eq,
    MoreAddrMapFacts.map_add_comm,
    MapUtils.AddrMap.MapFacts.Equal_refl.
Qed.

Local Hint Extern 1 (okToUnify (?var ~> Map.add ?k ?v ?m)
  (?var |-> (Val (AddrMap wrap_type) (Here (Map.add ?k (wrap' ?v) (Map.map wrap' ?m))))))
  => apply map_add_okToUnify.

Lemma CompileMapAdd : forall env F T {Wr : GoWrapper T} mvar kvar vvar m k (v : T),
  EXTRACT Ret (Go.Map.add k v m)
  {{ mvar ~> m * kvar ~> k * vvar ~> v * F }}
    Go.Modify Go.MapAdd (mvar, kvar, vvar)
  {{ fun ret => mvar ~> ret * kvar ~> k * vvar |-> moved_value (wrap v) * F }} // env.
Proof.
  unfold ProgOk.
  repeat inv_exec_progok.
  - eval_expr; [ repeat eexists; eauto; pred_solve..].
  - eval_expr.
    repeat (contradiction H1;
    repeat econstructor; eauto;
    [ eval_expr; eauto ..]).
Qed.

Lemma map_remove_okToUnify : forall AT AEQ {T} {Wr : GoWrapper T} var m k,
  (@okToUnify AT AEQ value (var ~> Map.remove k m)
  (var |-> (Val (AddrMap wrap_type) (Here (Map.remove k (Map.map wrap' m))))))%pred.
Proof.
  intros. unfold okToUnify.
  unfold wrap. simpl. repeat f_equal.
  eauto using MapUtils.addrmap_equal_eq,
    MoreAddrMapFacts.map_remove_comm,
    MapUtils.AddrMap.MapFacts.Equal_refl.
Qed.

Local Hint Extern 1 (okToUnify (?var ~> Map.remove ?k ?m)
  (?var |-> (Val (AddrMap wrap_type) (Here (Map.remove ?k (Map.map wrap' ?m))))))
  => apply map_remove_okToUnify.

Lemma CompileMapRemove : forall env F T {Wr : GoWrapper T} mvar kvar m k,
  EXTRACT Ret (Go.Map.remove k m)
  {{ mvar ~> m * kvar ~> k * F }}
    Go.Modify Go.MapRemove (mvar, kvar)
  {{ fun ret => mvar ~> ret * kvar ~> k * F }} // env.
Proof.
  unfold ProgOk.
  repeat inv_exec_progok.
  - eval_expr; [ repeat eexists; eauto; pred_solve..].
  - eval_expr.
    repeat (contradiction H1;
    repeat econstructor; eauto;
    [ eval_expr; eauto ..]).
Qed.

Lemma map_find_some_okToUnify : forall AT AEQ {T} {Wr : GoWrapper T} var m k v,
  Map.find k (Map.map wrap' m) = Some v ->
  (@okToUnify AT AEQ value (var ~> Map.find k m)
  (var |-> Val (Pair Bool wrap_type) (true, v))).
Proof.
  intros. unfold okToUnify, wrap. simpl.
  rewrite MapUtils.AddrMap.MapFacts.map_o in H.
  destruct Map.find; simpl in *; congruence.
Qed.

Lemma map_find_none_okToUnify : forall AT AEQ {T} {Wr : GoWrapper T} var m k,
  Map.find k (Map.map wrap' m) = None ->
  (@okToUnify AT AEQ value (var ~> Map.find k m)
  (var |-> Val (Pair Bool wrap_type) (false, default_value' wrap_type))).
Proof.
  intros. unfold okToUnify, wrap. simpl.
  rewrite MapUtils.AddrMap.MapFacts.map_o in H.
  destruct Map.find; simpl in *; congruence.
Qed.

Local Hint Extern 1 (okToUnify (?var ~> Map.find ?k ?m)
  (?var |-> (Val (Pair Bool wrap_type) (true, ?v))))
  => eapply map_find_some_okToUnify.

Local Hint Extern 1 (okToUnify (?var ~> Map.find ?k ?m)
  (?var |-> (Val (Pair Bool wrap_type) (false, ?v))))
  => eapply map_find_none_okToUnify.

Lemma CompileMapFind : forall env F T {Wr : GoWrapper T} mvar kvar vvar m k (v0 : option T),
  EXTRACT Ret (Go.Map.find k m)
  {{ mvar ~> m * kvar ~> k * vvar ~> v0 * F }}
    Go.Modify Go.MapFind (mvar, kvar, vvar)
  {{ fun ret => vvar ~> ret * mvar ~> m * kvar ~> k * F }} // env.
Proof.
  unfold ProgOk.
  repeat inv_exec_progok.
  - eval_expr.
    repeat eexists; eauto. pred_solve.
    repeat eexists; eauto. pred_solve.
  - eval_expr.
    repeat (contradiction H1;
    repeat econstructor;
    [ eval_expr; eauto..]).
Qed.

Lemma map_cardinal_okToUnify : forall AT AEQ {T} {Wr : GoWrapper T} var m,
  (@okToUnify AT AEQ value (var ~> Map.cardinal m)
  (var |-> (Val Num (Here (Map.cardinal (Map.map wrap' m))))))%pred.
Proof.
  intros. unfold okToUnify.
  unfold wrap. simpl. repeat f_equal. unfold id.
  eauto using MapUtils.AddrMap.map_cardinal_map_eq.
Qed.

Local Hint Extern 1 (okToUnify (?var ~> Map.cardinal ?m)
  (?var |-> (Val Num (Here (Map.cardinal (Map.map wrap' ?m))))))
  => apply map_cardinal_okToUnify.

Lemma CompileMapCardinal : forall env F T {Wr : GoWrapper T} mvar m var (v0 : W),
  EXTRACT Ret (Go.Map.cardinal m)
  {{ var ~> v0 * mvar ~> m * F }}
    Go.Modify Go.MapCardinality (mvar, var)
  {{ fun ret => var ~> ret * mvar ~> m * F }} // env.
Proof.
  unfold ProgOk.
  repeat inv_exec_progok.
  - eval_expr.
    repeat eexists; eauto. pred_solve.
  - contradiction H1.
    repeat econstructor; [ eval_expr; eauto..].
Qed.

Lemma map_elements_okToUnify : forall AT AEQ {T} {Wr : GoWrapper T} var m,
  @okToUnify AT AEQ value (var ~> Map.elements m)
  (var |-> Val (Slice (Pair Num wrap_type))
         (Here (map (fun x => (Here (fst x), snd x))
               (Map.elements (Map.map wrap' m))))).
Proof.
  intros.
  unfold okToUnify.
  unfold wrap; simpl wrap. repeat f_equal.
  simpl wrap'. repeat f_equal.
  rewrite MapUtils.AddrMap.map_elements_map_eq.
  rewrite map_map. simpl. reflexivity.
Qed.

Local Hint Extern 1 (okToUnify (?var ~> Map.elements ?k ?m)
  (?var |-> (Val _ (Here (map _ (Map.elements _))))))
  => eapply map_elements_okToUnify : okToUnify.

Local Hint Extern 1 (okToUnify (?var ~> Map.elements _)
  (?var |-> Val _ (Here(map _
   (MapUtils.AddrMap_List.Raw.map wrap' (MapUtils.AddrMap_List.this _))))))
  => eapply map_elements_okToUnify : okToUnify.

Lemma CompileMapElements : forall env F T {Wr : GoWrapper T} mvar m var (v0 : list (W * T)),
  EXTRACT Ret (Go.Map.elements m)
  {{ var ~> v0 * mvar ~> m * F }}
    Go.Modify Go.MapElements (mvar, var)
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
          edestruct H4; eauto. simpl in *; repeat deex.
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

Instance num_default_value : DefaultValue nat := {| zeroval := 0 |}. auto. Defined.
Instance valu_default_value : DefaultValue valu := {| zeroval := $0 |}. auto. Defined.
Instance bool_default_value : DefaultValue bool := {| zeroval := false |}. auto. Defined.
Instance emptystruct_default_value : DefaultValue unit := {| zeroval := tt |}. auto. Defined.

Lemma default_zero' :
  forall T {W : GoWrapper T} v,
    wrap v = default_value wrap_type -> wrap' v = default_value' wrap_type.
Proof.
  unfold wrap, default_value; intros.
  eauto using value_inj.
Qed.

Instance pair_default_value A B {Wa : GoWrapper A} {Wb : GoWrapper B}
  {Da : DefaultValue A} {Db : DefaultValue B} : DefaultValue (A * B) := {| zeroval := (zeroval, zeroval) |}.
  destruct Da, Db. unfold wrap; simpl. repeat find_apply_lem_hyp default_zero'.
  repeat find_rewrite. reflexivity.
Defined.

Instance list_default_value A {W : GoWrapper A} : DefaultValue (list A) := {| zeroval := [] |}. auto. Defined.

Lemma SetConstBefore : forall T (T' : GoWrapper T) (p : prog T) env xp v n (x : W) A B,
  EXTRACT p {{ v ~> n * A }} xp {{ B }} // env ->
  EXTRACT p
    {{ v ~> x * A }}
      v <~const n; xp
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
  inv_exec_progok.
  - repeat inv_exec.
    eval_expr.
    repeat econstructor.
    pred_solve.
  - repeat inv_exec.
  - repeat inv_exec.
    + exfalso; eauto.
    + contradiction H1. eval_expr.
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
  unfold ProgOk.
  inv_exec_progok.
  - do 5 inv_exec. inv_exec.
    eval_expr.
    edestruct H; forward_solve.
    simpl. pred_solve.
  - do 5 inv_exec; try solve [inv_exec].
    eval_expr.
    edestruct H; forward_solve.
    simpl. pred_solve.
  - inv_exec.
    do 3 inv_exec; forward_solve.
    inv_exec. inv_exec.
    eval_expr.
    edestruct H; forward_solve.
    simpl. pred_solve.
    contradiction H2.
    repeat eexists; eauto.
    do 2 econstructor; solve [eval_expr; eauto].
Qed.

Lemma AddInPlaceLeftBefore : forall T (T' : GoWrapper T) (p : prog T) B xp env
  va a v x F,
  EXTRACT p {{ v ~> (x + a) * va ~> a * F }} xp {{ B }} // env ->
  EXTRACT p
  {{ v ~> x * va ~> a * F }}
    Go.Modify (Go.ModifyNumOp Plus) (v, v, va); xp
  {{ B }} // env.
Proof.
  intros.
  eapply CompileBefore; eauto.
  eapply hoare_weaken.
  eapply CompileRet with (T := nat).
  instantiate (var0 := v).
  eapply hoare_weaken_post; [ | eapply CompileAddInPlace1 with (avar := v) (bvar := va) ].
  all : cancel_go.
Qed.

Lemma AddInPlaceLeftAfter : forall T (T' : GoWrapper T) (p : prog T) A xp env
  va a v x F,
  EXTRACT p {{ A }} xp {{ fun ret => F ret * v ~> x * va ~> a }} // env ->
  EXTRACT p
  {{ A }}
    xp; Go.Modify (Go.ModifyNumOp Plus) (v, v, va)
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
      one <~const 1;
      Declare Num (fun term => (
        Go.Modify (Go.DuplicateOp) (term, v);
        Go.Modify (Go.ModifyNumOp Go.Plus) (term, term, vn);
        Go.While (TestE Lt (Var v) (Var term)) (
          xpb v term one;
          Go.Modify (Go.ModifyNumOp Go.Plus) (v, v, one)
        )
      ))
    ))
  {{ fun ret => loopvar ~> ret * v |->? * vn |->? * F }} // env.
Proof.
  intros.
  eapply CompileDeclare with (Wr := GoWrapper_Num). intro one.
  eapply SetConstBefore; eauto.
  eapply CompileDeclare with (Wr := GoWrapper_Num). intro term.
  eapply hoare_strengthen_pre; [>
  | eapply DuplicateBefore with (x' := 0) (x := i); eauto].
  cancel_go.
  eapply hoare_strengthen_pre; [>
  | eapply AddInPlaceLeftBefore with (a := n) (x := i); eauto ].
  cancel_go.
  eapply hoare_strengthen_pre; [>
  | eapply hoare_weaken_post; [>
  | eapply CompileForLoopBasic with (t0 := t0) (loopvar := loopvar)] ].
  cancel_go.
  cancel_go.
  intros.
  eapply hoare_weaken_post; [>
  | eapply AddInPlaceLeftAfter with (a := 1) (x := x); eauto].
  rewrite Nat.add_1_r.
  instantiate (1 := fun x0 => (loopvar ~> x0 * term ~> (i + n) * _)%pred).
  cancel_go.
  specialize (H t x v term one).
  eapply hoare_strengthen_pre. shelve.
  eapply hoare_weaken_post. shelve.
  eauto.
  Unshelve.
  all : cancel_go.
Qed.

Definition voidfunc2 A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) env :=
  forall avar bvar,
    forall a b, EXTRACT src a b
           {{ avar ~> a * bvar ~> b }}
             Call [] name [avar; bvar]
           {{ fun _ => avar |->? * bvar |->? (* TODO: could remember a & b if they are of aliasable type *) }} // env.


(* TODO: generalize for all kinds of functions *)
Lemma extract_voidfunc2_call :
  forall A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) arga argb arga_t argb_t env,
    forall and body ss,
      (forall a b, EXTRACT src a b {{ arga ~> a * argb ~> b }} body {{ fun _ => arga |->? * argb |->? }} // env) ->
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

Lemma CompileSplit :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (p : A * B),
    EXTRACT Ret tt
    {{ avar ~>? A * bvar ~>? B * pvar ~> p * F }}
      Modify SplitPair (pvar, avar, bvar)
    {{ fun _ => avar ~> fst p * bvar ~> snd p * pvar |-> moved_value (wrap p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok.
  - repeat inv_exec.
    eval_expr.
    repeat econstructor.
    pred_solve.
  - inv_exec_progok.
  - inv_exec_progok.
    eval_expr.
    contradiction H1.
    repeat econstructor;
    [ eval_expr; eauto ..].
Qed.

Lemma CompileFst :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (p : A * B),
    EXTRACT Ret (fst p)
    {{ avar ~>? A * bvar ~>? B * pvar ~> p * F }}
      Modify SplitPair (pvar, avar, bvar)
    {{ fun ret => avar ~> ret * bvar ~> snd p * pvar |-> moved_value (wrap p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok.
  - repeat inv_exec.
    repeat econstructor.
    eval_expr.
    pred_solve.
  - inv_exec_progok.
  - inv_exec_progok.
    eval_expr.
    contradiction H1.
    repeat econstructor;
    [ eval_expr; eauto ..].
Qed.

Lemma CompileSnd :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar F (p : A * B),
    EXTRACT Ret (snd p)
    {{ avar ~>? A * bvar ~>? B * pvar ~> p * F }}
      Modify SplitPair (pvar, avar, bvar)
    {{ fun ret => avar ~> fst p * bvar ~> ret * pvar |-> moved_value (wrap p) * F }} // env.
Proof.
  intros; unfold ProgOk.
  inv_exec_progok.
  - repeat inv_exec.
    repeat econstructor.
    eval_expr.
    pred_solve.
  - inv_exec_progok.
  - inv_exec_progok.
    eval_expr.
    contradiction H1.
    repeat econstructor;
    [ eval_expr; eauto ..].
Qed.

Lemma CompileJoin :
  forall env A B {HA: GoWrapper A} {HB: GoWrapper B} avar bvar pvar (a : A) (b : B) pa pb F,
    EXTRACT Ret (a, b)
    {{ avar ~> a * bvar ~> b * pvar |-> Val (Pair (@wrap_type _ HA) (@wrap_type _ HB)) (pa, pb) * F }}
      Modify JoinPair (pvar, avar, bvar)
    {{ fun ret => avar |-> moved_value (wrap a) * bvar |-> moved_value (wrap b) * pvar ~> ret * F }} // env.
Proof.
  intros; unfold ProgOk.
  repeat inv_exec_progok.
  - repeat inv_exec.
    eval_expr.
    repeat econstructor.
    pred_solve.
  - contradiction H1.
    repeat econstructor.
    eval_expr; eauto.
    eval_expr; eauto.
    eval_expr; eauto.
Qed.

Hint Constructors source_stmt.

Lemma CompileRetOptionSome : forall env B {HB: GoWrapper B} {D : DefaultValue B}
  avar bvar pvar (b : B) (p : bool * B) F,
  EXTRACT Ret (Some b)
  {{ avar ~> true * bvar ~> b * pvar ~> p * F }}
    Modify JoinPair (pvar, avar, bvar)
  {{ fun ret => pvar ~> ret *
                avar |-> moved_value (wrap true) *
                bvar |-> moved_value (wrap b) * F }} // env.
Proof.
  intros.
  unfold ProgOk.
  inv_exec_progok.
  - repeat inv_exec.
    repeat econstructor.
    eval_expr.
    pred_solve.
  - inv_exec_progok.
  - inv_exec_progok.
    contradiction H1.
    repeat econstructor;
    [ eval_expr; eauto..].
Qed.

Lemma option_none_okToUnify : forall AT AEQ {T} {HT : GoWrapper T} {D : DefaultValue T} var,
  @okToUnify AT AEQ value (var ~> None) (var |-> Val (Pair Bool wrap_type) (false, wrap' zeroval)).
Proof.
  intros.
  unfold wrap. simpl.
  rewrite default_zero' by apply default_zero.
  reflexivity.
Qed.

Local Hint Extern 1 (okToUnify (?var ~> None)
  (?var |-> Val (Pair Bool wrap_type) (false, wrap' zeroval)))
  => apply option_none_okToUnify.

Lemma CompileRetOptionNone : forall env B {HB: GoWrapper B} {D : DefaultValue B}
  avar pvar (p : bool * B) F,
  EXTRACT Ret None
  {{ avar ~> false * pvar ~> p * F }}
    Declare wrap_type (fun bvar =>
      Modify JoinPair (pvar, avar, bvar)
    )
  {{ fun ret => pvar ~> ret *
                avar |-> moved_value (wrap false) * F }} // env.
Proof.
  intros.
  eapply CompileDeclare. intro bvar.
  unfold ProgOk.
  inv_exec_progok.
  - repeat inv_exec.
    repeat econstructor.
    eval_expr.
    pred_solve.
  - inv_exec_progok.
  - inv_exec_progok.
    contradiction H1.
    repeat econstructor;
    [ eval_expr; eauto..].
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
    Modify SplitPair (ovar, avar, bvar) ;
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
    destruct o; simpl. cancel_go.
    unfold wrap. simpl.
    erewrite <- default_zero' by apply default_zero. cancel_go.
  }
  destruct o; simpl in *.
  + unfold ProgOk; inv_exec_progok.
    - inv_exec.
      inv_exec; eval_expr.
      edestruct H; eauto.
      simpl. pred_solve.
      forward_solve.
    - inv_exec; inv_exec; eval_expr.
      edestruct H; eauto.
      simpl. pred_solve.
      forward_solve.
    - inv_exec.
      inv_exec; eval_expr.
      edestruct H; eauto.
      simpl. pred_solve.
      forward_solve.
      contradiction H3.
      repeat eexists. apply StepIfTrue. eval_expr.
  + erewrite <- default_zero' in * by apply default_zero.
    unfold ProgOk; inv_exec_progok.
    - inv_exec.
      inv_exec; eval_expr.
      edestruct H0; eauto.
      simpl. pred_solve.
      forward_solve.
    - inv_exec; inv_exec; eval_expr.
      edestruct H0; eauto.
      simpl. pred_solve.
      forward_solve.
    - inv_exec.
      inv_exec; eval_expr.
      edestruct H0; eauto.
      simpl. pred_solve.
      forward_solve.
      contradiction H3.
      repeat eexists. apply StepIfFalse. eval_expr.
Qed.

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

Ltac Type_denote x :=
  match x with
  | W => Num
  | bool => Bool
  | valu => DiskBlock
  | unit => EmptyStruct
  | ?A * ?B =>
    let ta := Type_denote A in
    let tb := Type_denote B in
    constr:(Pair ta tb)
  | list ?A =>
    let ta := Type_denote A in
    constr:(Slice ta)
  (* TODO add more types here *)
  end.

Ltac compile_bind := match goal with
  | [ |- EXTRACT Bind ?p ?q {{ _ }} _ {{ _ }} // _ ] =>
    match type of p with
    | prog ?T_ =>
      let v := fresh "var" in
      let Wr_ := constr:(ltac:(eauto with typeclass_instances) : GoWrapper T_) in
      eapply CompileDeclare with (T := T_) (Wr := Wr_);
      intro v; intros; eapply CompileBind; intros
    end
  end.

Ltac compile_const :=
  lazymatch goal with
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
        [eapply CompileConst with (var0 := x) | cancel_go..]
      end
  end.

Ltac compile_ret := match goal with
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; [ cancel_go ]
  end.

Ltac do_declare T cont :=
  lazymatch goal with
  | [ |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ ] =>
    lazymatch pre with
    | context [decls_pre ?decls ?vars] =>
      let decls' := fresh "decls" in
      evar (decls' : list Declaration);
      unify decls (Decl T :: decls'); subst decls'; cont (snd vars)
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
            eapply hoare_weaken_post; [ | eapply hoare_strengthen_pre; [ |
              eapply H with (avar := ka) (bvar := kb) ] ]; [ cancel_go .. ]
        end
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
        match find_val xs pre with
          | Some ?kxs =>
            eapply hoare_weaken_post; [
            | eapply hoare_strengthen_pre;
              [ | eapply CompileAppend with (lvar := xs) (vvar := x) ] ];
            [ cancel_go .. ]
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
  | [ |- EXTRACT Ret (Map.add ?k ?v ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    match find_val k pre with
    | Some ?vark =>
      match find_val v pre with
      | Some ?varv =>
        match find_val m pre with
        | Some ?varm =>
          eapply hoare_weaken; [
          eapply CompileMapAdd with (kvar := vark) (vvar := varv) (mvar := varm) |
          cancel_go..]
        end
      end
    end
  | [ |- EXTRACT Ret (Map.remove ?k ?m) {{ ?pre }} _ {{ fun ret : ?T => ?post }} // _ ] =>
    match find_val k pre with
    | Some ?vark =>
      match find_val m pre with
      | Some ?varm =>
        eapply hoare_weaken; [
        eapply CompileMapRemove with (kvar := vark) (mvar := varm) |
        cancel_go..]
      end
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

Ltac compile_step :=
  match goal with
  | [ |- @sigT _ _ ] => eexists; intros; eapply CompileDeclareMany; intro
  | _ => eapply CompileBindDiscard
  | _ => eapply decls_pre_impl_post
  end
  || compile_bind
  || compile_const
  || compile_ret
  || compile_match
  || compile_read_write
  || compile_for
  || compile_call
  || compile_add
  || compile_listop
  || compile_map_op
  || compile_split
  || compile_decompose
  .

Ltac compile :=
  unshelve (repeat compile_step); try exact nil.

Example append_list_in_pair : sigT (fun p => forall (a x : nat) xs,
  EXTRACT Ret (a, x :: xs)
  {{ 0 ~> (a, xs) * 1 ~> x }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? nat }} // StringMap.empty _).
Proof.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  eapply CompileBefore.
  eapply CompileRet with (v := a0) (var0 := var0).
  eapply hoare_weaken.
  evar (F : pred).
  apply (@CompileDup _ _ _ F var1 var0 a0).
  cancel_go.
  cancel_go.

  eapply hoare_weaken.
  pose proof CompileAppend.
  simpl in *.
  evar (F : pred).
  specialize (H (StringMap.empty _) F nat _ var0 1 x a0). (* why is this necessary? *)
  eapply hoare_weaken. eapply H.
  cancel_go. intro; simpl. subst F.
  match goal with
  | [ |- ?l =p=> ?r ] => set (l_ := l)
  end.
  pattern x0 in l_.
  subst l_.
  reflexivity.
  cancel_go.
  cancel_go.

  eapply hoare_weaken.
  eapply CompileJoin with (A := nat) (B := list nat) (avar := snd vars) (bvar := var0) (pvar := 0).
  cancel_go.
  cancel_go.
  apply decls_pre_impl_post.

Unshelve.
  exact [].
Defined.
Eval lazy in (projT1 append_list_in_pair).

Instance defaultvalue_option : forall T {H : GoWrapper T},
  DefaultValue (option T).
Proof.
  intros. refine {| zeroval := None |}. reflexivity.
Defined.

Require Import Cache.

Class WrapByTransforming T := {
  T' : Type;
  WrT' : GoWrapper T';
  transform : T -> T';
  transform_inj : forall t1 t2 : T, transform t1 = transform t2 -> t1 = t2;
}.

Instance WrapByTransforming_cachestate : WrapByTransforming cachestate.
  refine {|
    transform := fun cs => (CSMap cs, CSMaxCount cs, CSEvict cs);
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.

Instance GoWrapper_transform T {Tr : WrapByTransforming T} : GoWrapper T.
  refine {| wrap_type := wrap_type;
            wrap' := fun t => @wrap' _ (@WrT' _ Tr) (@transform _ Tr t) |}.
  intros.
  apply wrap_inj in H.
  auto using transform_inj.
Defined.

Instance cachestate_default_value : DefaultValue cachestate := {| zeroval :=
  {| CSMap := Go.Map.empty _; CSMaxCount := 0; CSEvict := tt |} |}.
  unfold wrap, wrap', GoWrapper_transform, default_value. simpl.
  repeat f_equal.
  apply MapUtils.addrmap_equal_eq.
  apply MapUtils.AddrMap.map_empty.
  auto with map.
Defined.

Theorem transform_pimpl : forall T {Tr : WrapByTransforming T} k (t : T),
  (k |-> (@wrap _ (@GoWrapper_transform _ Tr) t) : pred) <=p=> k |-> (@wrap _ WrT' (transform t)).
Proof.
  intros.
  reflexivity.
Qed.

Example compile_writeback : forall env, sigT (fun p => forall a cs,
  EXTRACT BUFCACHE.writeback a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  unfold BUFCACHE.writeback.
  intros.
  compile_step.
  eapply hoare_strengthen_pre.
  rewrite transform_pimpl. simpl. reflexivity. (* TODO *)
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
(* TODO
  (* TODO: Can't put [a0] in [?B0]. *)
  instantiate (B0 := _ * snd (fst vars) ~>? nat).
  cancel_go.
  compile_step.
  (* TODO: Can't put [val] in [?F]. *)
  instantiate (F := _ * snd (fst vars) ~>? nat).
  cancel_go.
  compile_step.
  (* TODO
  destruct b; simpl. (* TODO *)
  compile_match.
  compile_step.
  compile_step.
  compile_step.
*)
Abort.

Example match_option : sigT (fun p => forall env (o : option W) (r0 : W),
  EXTRACT match o with
  | Some t => Ret (S t)
  | None => Ret 0
  end
  {{ 0 ~> o * 1 ~> r0 }}
    p
  {{ fun ret => 1 ~> ret * 0 |->? }} // env
  ).
Proof.
  compile.
Defined.

Example find_in_map : sigT (fun p => forall env (m : Map.t W) (f0 : W),
  EXTRACT (match Map.find (S f0) m with
    | Some t => Ret (S t)
    | None => Ret 0
    end)
  {{ 0 ~> m * 1 ~> f0}}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  intros. compile.
Defined.

Eval lazy in (projT1 find_in_map).

Example add_to_map : sigT (fun p => forall env m,
  EXTRACT (Ret (Map.add 1 5 m))
  {{ 0 ~> m }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros. compile.
Defined.

Example remove_from_map : sigT (fun p => forall env (m : Map.t W),
  EXTRACT (Ret (Map.remove 1 m))
  {{ 0 ~> m }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros. compile.
Defined.

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
  forall a b, EXTRACT swap_prog a b {{ 0 ~> a * 1 ~> b }} p {{ fun _ => 0 |->? * 1 |->? }} // env).
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

Example extract_for_loop : forall env, sigT (fun p =>
  forall cnt nocrash crashed,
  EXTRACT (@ForN_ W W (fun i sum => Ret (sum + i)) 1 cnt nocrash crashed 0)
  {{ 0 ~> 0 * 1 ~> cnt }} p {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros.
  compile.
Defined.
Eval lazy in projT1 (extract_for_loop (StringMap.empty _)).

(*
Declare DiskBlock
  (fun var0 : nat =>
   (DiskRead var0 (Var 0);
    Declare DiskBlock
      (fun var1 : nat =>
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
