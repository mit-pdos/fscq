Require Import Eqdep.
Require Import List PeanoNat.
Require Import Omega.
Require Import Structures.OrderedTypeEx.
Require Import Mem AsyncDisk Pred PredCrash ProgMonad SepAuto.
Require Import GoTactics2.
Require Import GoHoare.
Require Import GoSemantics.
Require Import StringMap MoreMapFacts.

Set Implicit Arguments.

Module VarMapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(VarMap).
Module Import MoreVarMapFacts := MoreFacts_fun(Nat_as_OT)(VarMap).

Notation "k -s> v ;  m" := (StringMap.add k v m) (at level 21, right associativity) : map_scope.
Delimit Scope map_scope with map.

Notation "k ->> v ;  m" := (VarMap.add k v m) (at level 21, right associativity) : map_scope.


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

Local Open Scope map_scope.

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
  unshelve (edestruct H1); eauto.
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