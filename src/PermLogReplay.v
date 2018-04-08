Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classes.SetoidTactics.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Eqdep_dec.
Require Import ListUtils.
Require Import Pred.
Require Import MapUtils.
Require Import FMapFacts.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Word.

Require Export PermGenSepN PermDiskLog.

Import AddrMap.
Import ListNotations.

Definition gen_map {T} := Map.t T.
Definition gmap0 {T} := map0 T.
Definition blockmap := @gen_map tagged_block.
Definition bmap0 := @gmap0 tagged_block.
Definition handlemap := @gen_map handle.
Definition hmap0 := @gmap0 handle.
Definition diskstate := list valuset.

Lemma map_empty_gmap0 : forall T, Map.Empty (@gmap0 T).
Proof.
  apply Map.empty_1.
Qed.

Lemma map_empty_bmap0 : Map.Empty bmap0.
Proof.
  apply Map.empty_1.
Qed.

Lemma map_empty_hmap0 : Map.Empty hmap0.
Proof.
  apply Map.empty_1.
Qed.


Module LogReplay.

  Definition replay_mem {A} (log : @generic_contents A) init : gen_map :=
    fold_left (fun m e => Map.add (fst e) (snd e) m) log init.

  Definition replay_disk (log : list (addr * tagged_block)) (m : diskstate) : diskstate:=
    fold_left (fun m' e => updN m' (fst e) (snd e, nil)) log m.

  Definition map_merge {T} (m1 m2 : @gen_map T) :=
    replay_mem (Map.elements m2) m1.

  Definition map_replay ms old cur : Prop :=
    cur = replay_disk (Map.elements ms) old.

  Hint Resolve MapProperties.eqke_equiv.
  Hint Resolve KNoDup_map_elements.

  Lemma replay_disk_length : forall l m,
    length (replay_disk l m) = length m.
  Proof.
    induction l; intros; simpl; auto.
    rewrite IHl.
    rewrite length_updN; auto.
  Qed.

  Lemma replay_disk_updN_comm : forall l d a v,
    ~ In a (map fst l)
    -> replay_disk l (updN d a v) = updN (replay_disk l d) a v.
  Proof.
    induction l; simpl; intuition; simpl in *.
    rewrite updN_comm by auto.
    apply IHl; auto.
  Qed.

  Lemma replay_disk_selN_other : forall l d a def,
    ~ In a (map fst l)
    -> selN (replay_disk l d) a def = selN d a def.
  Proof.
    induction l; simpl; intuition; simpl in *.
    rewrite IHl; auto.
    rewrite selN_updN_ne; auto.
  Qed.

  Lemma replay_disk_selN_In : forall l m a v def,
    In (a, v) l -> NoDup (map fst l) -> a < length m ->
    selN (replay_disk l m) a def = (v, nil).
  Proof.
    induction l; simpl; intros; auto.
    inversion H.
    inversion H0; subst.
    destruct a; intuition; simpl.
    inversion H2; subst.
    rewrite replay_disk_updN_comm by auto.
    rewrite selN_updN_eq; auto.
    erewrite replay_disk_length; auto.
    simpl in *.
    apply IHl; auto.
    rewrite length_updN; auto.
  Qed.

  Lemma replay_disk_selN_In_KNoDup : forall a v l m def,
    In (a, v) l -> KNoDup l -> a < length m ->
    selN (replay_disk l m) a def = (v, nil).
  Proof.
    intros.
    eapply replay_disk_selN_In; eauto.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma replay_disk_selN_MapsTo : forall a v ms m def,
    Map.MapsTo a v ms -> a < length m ->
    selN (replay_disk (Map.elements ms) m) a def = (v, nil).
  Proof.
    intros.
    apply replay_disk_selN_In_KNoDup; auto.
    apply InA_eqke_In.
    apply MapFacts.elements_mapsto_iff; auto.
  Qed.

  Lemma replay_disk_selN_not_In : forall a ms m def,
    ~ Map.In a ms
    -> selN (replay_disk (Map.elements ms) m) a def = selN m a def.
  Proof.
    intros.
    apply replay_disk_selN_other; auto.
    contradict H.
    erewrite MapFacts.elements_in_iff.
    apply in_map_fst_exists_snd in H; destruct H.
    eexists. apply In_InA; eauto.
  Qed.

  Hint Rewrite replay_disk_length : lists.

  Lemma replay_disk_add : forall a v ds m,
    replay_disk (Map.elements (Map.add a v ds)) m = updN (replay_disk (Map.elements ds) m) a (v, nil).
  Proof.
    intros.
    eapply list_selN_ext.
    autorewrite with lists; auto.
    intros.
    destruct (eq_nat_dec pos a); subst; autorewrite with lists in *.
    rewrite selN_updN_eq by (autorewrite with lists in *; auto).
    apply replay_disk_selN_MapsTo; auto.
    apply Map.add_1; auto.

    rewrite selN_updN_ne by auto.
    case_eq (Map.find pos ds); intros; autorewrite with lists in *.
    (* [pos] is in the transaction *)
    apply Map.find_2 in H0.
    setoid_rewrite replay_disk_selN_MapsTo at 2; eauto.
    erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.add_2; eauto.
    (* [pos] is not in the transaction *)
    repeat rewrite replay_disk_selN_not_In; auto.
    apply MapFacts.not_find_in_iff; auto.
    apply MapFacts.not_find_in_iff.
    rewrite MapFacts.add_neq_o by auto; auto.
    Unshelve.
    exact valuset0.
  Qed.


  Lemma replay_disk_eq : forall a v v' ms d vs,
    Map.find a ms = Some v ->
    (exists F, F * a |-> (v', vs))%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    v = v'.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel with (def := valuset0) in H0 as Hx.
    erewrite replay_disk_selN_MapsTo in Hx.
    inversion Hx; auto.
    apply Map.find_2; auto.
    apply list2nmem_ptsto_bound in H0.
    repeat rewrite replay_disk_length in *; auto.
  Qed.

  Lemma replay_disk_none_selN : forall a v ms d def,
    Map.find a ms = None ->
    (exists F, F * a |-> v)%pred
      (list2nmem (replay_disk (Map.elements ms) d)) ->
    selN d a def = v.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel in H0 as Hx.
    rewrite Hx.
    rewrite replay_disk_selN_not_In; eauto;
    apply MapFacts.not_find_in_iff; auto.
  Qed.

  Lemma synced_data_replay_inb : forall a v c1 d,
    (exists F, F * a |-> v)%pred (list2nmem (replay_disk c1 d))
    -> a < length d.
  Proof.
    intros.
    destruct H.
    apply list2nmem_ptsto_bound in H.
    autorewrite with lists in *; auto.
  Qed.


  Lemma replay_disk_is_empty : forall d ms,
    Map.is_empty ms = true -> replay_disk (Map.elements ms) d = d.
  Proof.
    intros.
    apply Map.is_empty_2 in H.
    apply MapProperties.elements_Empty in H.
    rewrite H.
    simpl; auto.
  Qed.


  Lemma replay_mem_map0 : forall T m,
    Map.Equal (replay_mem (Map.elements m) (@gmap0 T)) m.
  Proof.
    intros; hnf; intro.
    unfold replay_mem.
    rewrite <- Map.fold_1.
    rewrite MapProperties.fold_identity; auto.
  Qed.

  Local Hint Resolve MapFacts.Equal_refl.

  Lemma replay_mem_app' : forall T l m,
    Map.Equal (replay_mem ((Map.elements m) ++ l) (@gmap0 T)) (replay_mem l m).
  Proof.
    induction l using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite replay_mem_map0; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    setoid_rewrite <- IHl; auto.
  Qed.

  Lemma replay_mem_app : forall T l2 l m,
    Map.Equal m (replay_mem l (@gmap0 T)) ->
    Map.Equal (replay_mem (l ++ l2) (@gmap0 T)) (replay_mem l2 m).
  Proof.
    induction l2 using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite H; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    setoid_rewrite <- IHl2; eauto; auto.
  Qed.

  Lemma replay_mem_equal : forall T (l: @generic_contents T) m1 m2,
    Map.Equal m1 m2 ->
    Map.Equal (replay_mem l m1) (replay_mem l m2).
  Proof.
    induction l; simpl; intros; auto.
    hnf; intro.
    apply IHl.
    apply MapFacts.add_m; auto.
  Qed.


  Instance replay_mem_proper : forall T,
    Proper (eq ==> Map.Equal ==> Map.Equal) (@replay_mem T).
  Proof.
    unfold Proper, respectful; intros; subst.
    apply replay_mem_equal; auto.
  Qed.

  Lemma replay_mem_add : forall T (l: @generic_contents T) k v m,
    ~ KIn (k, v) l -> KNoDup l ->
    Map.Equal (replay_mem l (Map.add k v m)) (Map.add k v (replay_mem l m)).
  Proof.
    induction l; simpl; intros; auto.
    destruct a; simpl.
    rewrite <- IHl.
    apply replay_mem_equal.
    apply map_add_comm.
    contradict H; inversion H0; subst.
    constructor; hnf; simpl; auto.
    contradict H.
    apply InA_cons.
    right; auto.
    inversion H0; auto.
  Qed.


  Lemma In_replay_mem_mem0 : forall T (l: @generic_contents T) k,
    KNoDup l ->
    In k (map fst (Map.elements (replay_mem l gmap0))) ->
    In k (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl in *.
    destruct (addr_eq_dec n k).
    left; auto.
    right.
    inversion H; subst.
    apply In_map_fst_MapIn in H0.
    rewrite replay_mem_add in H0 by auto.
    apply MapFacts.add_neq_in_iff in H0; auto.
    apply IHl; auto.
    apply In_map_fst_MapIn; auto.
  Qed.

  Lemma replay_disk_replay_mem0 : forall l d,
    KNoDup l ->
    replay_disk l d = replay_disk (Map.elements (elt:=tagged_block) (replay_mem l bmap0)) d.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; inversion H; subst; simpl.
    rewrite IHl by auto.
    rewrite replay_disk_updN_comm.
    rewrite <- replay_disk_add.
    f_equal; apply eq_sym.
    apply mapeq_elements.
    apply replay_mem_add; auto.
    contradict H2.
    apply In_fst_KIn; simpl.
    apply In_replay_mem_mem0; auto.
  Qed.

  Lemma replay_disk_merge' : forall l1 l2 d,
    KNoDup l1 -> KNoDup l2 ->
    replay_disk l2 (replay_disk l1 d) =
    replay_disk (Map.elements (replay_mem l2 (replay_mem l1 bmap0))) d.
  Proof.
    induction l1; intros; simpl.
    induction l2; simpl; auto.
    inversion H0; subst.
    erewrite mapeq_elements.
    2: apply replay_mem_add; destruct a; auto.
    rewrite replay_disk_add.
    rewrite <- IHl2 by auto.
    apply replay_disk_updN_comm.
    contradict H3.
    apply In_fst_KIn; auto.

    induction l2; destruct a; simpl; auto.
    inversion H; simpl; subst.
    erewrite mapeq_elements.
    2: apply replay_mem_add; auto.
    rewrite replay_disk_add.
    rewrite replay_disk_updN_comm.
    f_equal.

    apply replay_disk_replay_mem0; auto.
    contradict H3.
    apply In_fst_KIn; auto.

    destruct a0; simpl in *.
    inversion H; inversion H0; simpl; subst.
    rewrite replay_disk_updN_comm.
    rewrite IHl2 by auto.
    rewrite <- replay_disk_add.
    f_equal.
    apply eq_sym.
    apply mapeq_elements.
    apply replay_mem_add; auto.
    contradict H7.
    apply In_fst_KIn; simpl; auto.
  Qed.


  Lemma replay_disk_merge : forall m1 m2 d,
    replay_disk (Map.elements m2) (replay_disk (Map.elements m1) d) =
    replay_disk (Map.elements (map_merge m1 m2)) d.
  Proof.
    intros.
    unfold map_merge.
    setoid_rewrite mapeq_elements at 3.
    2: eapply replay_mem_equal with (m2 := m1); auto.
    rewrite replay_disk_merge' by auto.
    f_equal.
    apply mapeq_elements.
    apply replay_mem_equal.
    apply replay_mem_map0.
  Qed.

  Lemma replay_mem_not_in' : forall T (l: @generic_contents T) a v ms,
    KNoDup l ->
    ~ In a (map fst l) ->
    Map.MapsTo a v (replay_mem l ms) ->
    Map.MapsTo a v ms.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *; intuition.
    apply IHl; auto.
    inversion H; subst; auto.
    rewrite replay_mem_add in H1.
    apply Map.add_3 in H1; auto.
    inversion H; auto.
    inversion H; auto.
  Qed.

  Lemma replay_mem_not_in : forall T a (v: T) ms m,
    Map.MapsTo a v (replay_mem (Map.elements m) ms) ->
    ~ Map.In a m ->
    Map.MapsTo a v ms.
  Proof.
    intros.
    eapply replay_mem_not_in'; eauto.
    auto.
    contradict H0.
    apply In_map_fst_MapIn; auto.
  Qed.

  Lemma map_merge_repeat' : forall T (l: @generic_contents T) m,
    KNoDup l ->
    Map.Equal (replay_mem l (replay_mem l m)) (replay_mem l m).
  Proof.
    induction l; intros; auto.
    destruct a; inversion H; simpl; subst.
    rewrite replay_mem_add by auto.
    rewrite IHl by auto.
    setoid_rewrite replay_mem_add; auto.
    apply map_add_repeat.
  Qed.

  Lemma map_merge_repeat : forall T (a b: @gen_map T),
    Map.Equal (map_merge (map_merge a b) b) (map_merge a b).
  Proof.
    unfold map_merge; intros.
    apply map_merge_repeat'; auto.
  Qed.


  Lemma map_merge_id: forall T (m: @gen_map T),
    Map.Equal (map_merge m m) m.
  Proof.
    unfold map_merge, replay_mem; intros.
    rewrite <- Map.fold_1.
    apply MapProperties.fold_rec_nodep; auto.
    intros.
    rewrite H0.
    apply MapFacts.Equal_mapsto_iff; intros.

    destruct (eq_nat_dec k0 k); subst; split; intros.
    apply MapFacts.add_mapsto_iff in H1; intuition; subst; auto.
    apply MapFacts.add_mapsto_iff; left; intuition.
    eapply MapFacts.MapsTo_fun; eauto.
    eapply Map.add_3; hnf; eauto.
    eapply Map.add_2; hnf; eauto.
  Qed.



  Lemma replay_disk_updN_absorb : forall l a v d,
    In a (map fst l) -> KNoDup l ->
    replay_disk l (updN d a v) = replay_disk l d.
  Proof.
    induction l; intros; simpl; auto.
    inversion H.
    destruct a; simpl in *; intuition; subst.
    rewrite updN_twice; auto.
    inversion H0; subst.
    setoid_rewrite <- IHl at 2; eauto.
    rewrite updN_comm; auto.
    contradict H3; subst.
    apply In_fst_KIn; auto.
  Qed.

  Lemma replay_disk_twice : forall l d,
    KNoDup l ->
    replay_disk l (replay_disk l d) = replay_disk l d.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst; simpl.
    rewrite <- replay_disk_updN_comm.
    rewrite IHl; auto.
    rewrite updN_twice; auto.
    contradict H2.
    apply In_fst_KIn; auto.
  Qed.


  Lemma replay_disk_eq_length_eq : forall l l' a b,
    replay_disk l a = replay_disk l' b ->
    length a = length b.
  Proof.
    induction l; destruct l'; simpl; intros; subst;
    repeat rewrite replay_disk_length; autorewrite with lists; auto.
    setoid_rewrite <- length_updN.
    eapply IHl; eauto.
  Qed.

  Lemma ptsto_replay_disk_not_in' : forall l F a v d,
    ~ In a (map fst l) ->
    KNoDup l ->
    (F * a |-> v)%pred (list2nmem (replay_disk l d)) ->
    ((arrayN_ex (@ptsto _ addr_eq_dec valuset) d a) * a |-> v)%pred (list2nmem d).
  Proof.
    induction l; simpl; intros; auto.
    erewrite list2nmem_sel with (x := v); eauto.
    apply list2nmem_ptsto_cancel.
    eapply list2nmem_ptsto_bound; eauto.

    inversion H0; destruct a; subst.
    erewrite list2nmem_sel with (x := v); eauto.
    eapply IHl; simpl; auto.
    rewrite replay_disk_updN_comm, selN_updN_ne.
    apply list2nmem_ptsto_cancel.
    apply list2nmem_ptsto_bound in H1.
    rewrite replay_disk_length, length_updN in *; auto.
    intuition.
    contradict H4.
    apply In_KIn; auto.
    Unshelve. all: eauto.
  Qed.

  Lemma ptsto_replay_disk_not_in : forall F a v d m,
    ~ Map.In a m ->
    (F * a |-> v)%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    ((arrayN_ex (@ptsto _ addr_eq_dec valuset) d a) * a |-> v)%pred (list2nmem d).
  Proof.
    intros.
    eapply ptsto_replay_disk_not_in'; eauto.
    contradict H.
    apply In_map_fst_MapIn; auto.
  Qed.

  Lemma replay_disk_updN_eq_not_in : forall Fd a v vs d ms,
    ~ Map.In a ms ->
    (Fd * a |-> vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    updN (replay_disk (Map.elements ms) d) a (v, (vsmerge vs)) =
      replay_disk (Map.elements ms) (vsupd d a v).
  Proof.
    unfold vsupd; intros.
    rewrite replay_disk_updN_comm.
    repeat f_equal.
    erewrite <- replay_disk_selN_not_In; eauto.
    eapply list2nmem_sel; eauto.
    contradict H.
    apply In_map_fst_MapIn; eauto.
  Qed.

  Lemma replay_disk_updN_eq_empty : forall Fd a v vs d ms,
    Map.Empty ms ->
    (Fd * a |-> vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    updN (replay_disk (Map.elements ms) d) a (v, (vsmerge vs)) =
      replay_disk (Map.elements ms) (vsupd d a v).
  Proof.
    intros.
    eapply replay_disk_updN_eq_not_in; eauto.
    apply MapFacts.not_find_in_iff.
    rewrite MapFacts.elements_o.
    apply MapProperties.elements_Empty in H.
    rewrite H; auto.
  Qed.



  Lemma replay_disk_selN_snd_nil : forall l a d,
    In a (map fst l) ->
    snd (selN (replay_disk l d) a valuset0) = nil.
  Proof.
    induction l; simpl; intros; intuition.
    destruct a; subst; simpl.
    destruct (In_dec (eq_nat_dec) n (map fst l)).
    apply IHl; auto.
    rewrite replay_disk_updN_comm by auto.
    destruct (lt_dec n (length d)).
    rewrite selN_updN_eq; auto.
    rewrite replay_disk_length; auto.
    rewrite selN_oob; auto.
    rewrite length_updN, replay_disk_length; omega.
  Qed.

  Lemma replay_disk_vssync_comm_list : forall l d a,
    vssync (replay_disk l d) a =
    replay_disk l (vssync d a).
  Proof.
    induction l; simpl; auto; intros.
    rewrite IHl; unfold vssync; destruct a; simpl in *.
    destruct (addr_eq_dec a0 n); subst.
    - repeat rewrite updN_twice.
      destruct (lt_dec n (length d)).
      repeat rewrite selN_updN_eq; auto.
      rewrite selN_oob; repeat rewrite updN_oob; auto; try omega.
      apply not_gt; auto.
      apply not_gt; auto.
    - repeat rewrite selN_updN_ne by auto.
      rewrite updN_comm; auto.
  Qed.

  Lemma replay_disk_vssync_vecs_comm_list : forall l ents d,
    vssync_vecs (replay_disk ents d) l =
    replay_disk ents (vssync_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    rewrite <- IHl by auto.
    rewrite replay_disk_vssync_comm_list; auto.
  Qed.

  Lemma replay_disk_vssync_comm : forall m d a,
    vssync (replay_disk (Map.elements m) d) a =
    replay_disk (Map.elements m) (vssync d a).
  Proof.
    intros; apply replay_disk_vssync_comm_list.
  Qed.

  Lemma replay_disk_vssync_vecs_comm : forall l m d,
    vssync_vecs (replay_disk (Map.elements m) d) l =
    replay_disk (Map.elements m) (vssync_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    rewrite <- IHl by auto.
    rewrite replay_disk_vssync_comm; auto.
  Qed.


  Lemma replay_disk_empty : forall m d,
    Map.Empty m ->
    replay_disk (Map.elements m) d = d.
  Proof.
    intros.
    apply MapProperties.elements_Empty in H.
    rewrite H; simpl; auto.
  Qed.


  Lemma replay_disk_remove_updN_eq : forall F m d a v,
    (F * a |-> v)%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    replay_disk (Map.elements m) d =
    replay_disk (Map.elements (Map.remove a m)) (updN d a v).
  Proof.
    intros.
    eapply list_selN_ext with (default := valuset0); intros.
    repeat rewrite replay_disk_length; rewrite length_updN; auto.
    rewrite replay_disk_updN_comm.

    destruct (Nat.eq_dec pos a); subst.
    rewrite selN_updN_eq; [ apply eq_sym | ].
    eapply list2nmem_sel; eauto.
    rewrite replay_disk_length in *; eauto.

    rewrite selN_updN_ne by auto.
    case_eq (Map.find pos m); intros.
    apply Map.find_2 in H1.
    rewrite replay_disk_length in *.
    repeat erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.remove_2; eauto.

    apply MapFacts.not_find_in_iff in H1.
    setoid_rewrite replay_disk_selN_not_In; auto.
    apply not_in_remove_not_in; auto.

    rewrite In_map_fst_MapIn.
    apply Map.remove_1; auto.
  Qed.


  Lemma list2nmem_replay_disk_remove_updN_ptsto : forall F a vs vs' d ms,
    (F * a |-> vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    (F * a |-> vs')%pred
      (list2nmem (replay_disk (Map.elements (Map.remove a ms)) (updN d a vs'))).
  Proof.
    intros.
    rewrite replay_disk_updN_comm.
    erewrite <- updN_twice.
    eapply list2nmem_updN.
    rewrite <- replay_disk_updN_comm.
    erewrite <- replay_disk_remove_updN_eq; eauto.

    rewrite In_map_fst_MapIn; apply Map.remove_1; auto.
    rewrite In_map_fst_MapIn; apply Map.remove_1; auto.
  Qed.


  Set Regular Subst Tactic.


  Lemma updN_replay_disk_remove_eq : forall m d a v,
    d = replay_disk (Map.elements m) d ->
    updN d a v = replay_disk (Map.elements (Map.remove a m)) (updN d a v).
  Proof.
    intros.
    eapply list_selN_ext with (default := valuset0); intros.
    repeat rewrite replay_disk_length; rewrite length_updN; auto.
    rewrite replay_disk_updN_comm.
    rewrite length_updN in H0.

    destruct (Nat.eq_dec pos a); subst.
    repeat rewrite selN_updN_eq; auto.
    rewrite replay_disk_length in *; eauto.

    repeat rewrite selN_updN_ne by auto.
    rewrite H at 1.
    case_eq (Map.find pos m); intros.
    apply Map.find_2 in H1.
    repeat erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.remove_2; eauto.

    apply MapFacts.not_find_in_iff in H1.
    setoid_rewrite replay_disk_selN_not_In; auto.
    apply not_in_remove_not_in; auto.

    rewrite In_map_fst_MapIn.
    apply Map.remove_1; auto.
  Qed.


  Lemma replay_mem_add_find_none : forall T l a (v:T) m,
    ~ Map.find a (replay_mem l (Map.add a v m)) = None.
  Proof.
    induction l; simpl; intros.
    rewrite MapFacts.add_eq_o; congruence.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst.
    rewrite map_add_repeat.
    apply IHl.
    rewrite map_add_comm by auto.
    apply IHl.
  Qed.


  Lemma map_find_replay_mem_not_in : forall T a (l: @generic_contents T) m,
    Map.find a (replay_mem l m) = None ->
    ~ In a (map fst l).
  Proof.
    induction l; intuition; simpl in *.
    eapply IHl; intuition eauto; subst.
    destruct a0; simpl in *.
    contradict H.
    apply replay_mem_add_find_none.
  Qed.

  Lemma replay_mem_find_none_mono : forall T (l: @generic_contents T) a m,
    Map.find a (replay_mem l m) = None ->
    Map.find a m = None.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; simpl in *.
    destruct (addr_eq_dec n a0); subst.
    contradict H.
    apply replay_mem_add_find_none.
    erewrite <- MapFacts.add_neq_o; eauto.
  Qed.

  Definition ents_remove a (ents : list (addr * tagged_block)) := 
    filter (fun e => if (addr_eq_dec (fst e) a) then false else true) ents.


  Lemma ents_remove_not_in : forall ents a,
    ~ In a (map fst (ents_remove a ents)).
  Proof.
    induction ents; auto; intros; simpl.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst; auto.
    simpl; intuition.
    eapply IHents; eauto.
  Qed.

  Local Hint Resolve ents_remove_not_in.
  Lemma replay_disk_ents_remove_updN : forall ents d a v,
    updN (replay_disk (ents_remove a ents) d) a v =  updN (replay_disk ents d) a v.
  Proof.
    induction ents; intros; simpl; auto.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst; simpl; auto.
    rewrite <- replay_disk_updN_comm by auto.
    rewrite <- IHents.
    rewrite <- replay_disk_updN_comm by auto.
    rewrite updN_twice; auto.
  Qed.

  Definition ents_remove_list (al : list addr) (ents: contents) := 
    filter (fun e => if (In_dec addr_eq_dec (fst e) al) then false else true) ents.


  (**********************
   * validity of map and log entries 
   *
   *)


  Definition map_valid {T} (ms : @gen_map T) (m : diskstate) :=
     forall a v, Map.MapsTo a v ms -> a <> 0 /\ a < length m.

  Definition log_valid {T} (ents : @generic_contents T) (m : diskstate) :=
     KNoDup ents /\ forall a v, KIn (a, v) ents -> a <> 0 /\ a < length m.


  Lemma map_valid_map0 : forall T m,
    map_valid (@gmap0 T) m.
  Proof.
    unfold map_valid, map0; intuition; exfalso;
    apply MapFacts.empty_mapsto_iff in H; auto.
  Qed.

  Lemma map_valid_empty : forall T l m,
    Map.Empty m -> @map_valid T m l.
  Proof.
    unfold map_valid; intros.
    exfalso; eapply map_empty_find_exfalso; eauto.
    apply Map.find_1; eauto.
  Qed.

  Lemma map_valid_add : forall T d a (v: T) ms,
    map_valid ms d ->
    a < length d -> a <> 0 ->
    map_valid (Map.add a v ms) d.
  Proof.
    unfold map_valid; intros.
    destruct (addr_eq_dec a0 a); subst.
    eauto.
    eapply H.
    eapply Map.add_3; hnf; eauto.
  Qed.

  Lemma map_valid_updN : forall T m d a v,
    @map_valid T m d -> map_valid m (updN d a v).
  Proof.
    unfold map_valid; simpl; intuition.
    eapply H; eauto.
    rewrite length_updN.
    eapply H; eauto.
  Qed.


  Lemma map_valid_remove : forall T a ms d1 d2,
    @map_valid T ms d1 ->
    length d1 = length d2 ->
    map_valid (Map.remove a ms) d2.
  Proof.
    unfold map_valid; intros.
    erewrite <- H0.
    eapply H.
    eapply Map.remove_3; eauto.
  Qed.


  Lemma map_valid_equal : forall T d m1 m2,
    Map.Equal m1 m2 -> @map_valid T m1 d -> map_valid m2 d.
  Proof.
    induction d; unfold map_valid; simpl; intros; split;
    eapply H0; rewrite H; eauto.
  Qed.


  Lemma length_eq_map_valid : forall T m a b,
    @map_valid T m a -> length b = length a -> map_valid m b.
  Proof.
    unfold map_valid; firstorder.
  Qed.

  Lemma map_valid_vsupd_vecs : forall T l d m,
    @map_valid T m d ->
    map_valid m (vsupd_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    apply IHl.
    apply map_valid_updN; auto.
  Qed.

  Lemma map_valid_vssync_vecs : forall T l d m,
    @map_valid T m d ->
    map_valid m (vssync_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    apply IHl.
    apply map_valid_updN; auto.
  Qed.


  Lemma map_valid_Forall_fst_synced : forall T d ms,
    @map_valid T ms d ->
    Forall (fun e => fst e < length d) (Map.elements ms).
  Proof.
    unfold map_valid; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    destruct x; simpl.
    apply (H n t).
    apply Map.elements_2.
    apply In_InA; auto.
  Qed.

  Hint Resolve map_valid_Forall_fst_synced.

  Lemma map_valid_Forall_synced_map_fst : forall T d ms,
    @map_valid T ms d ->
    Forall (fun e => e < length d) (map fst (Map.elements ms)).
  Proof.
    unfold map_valid; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    apply In_map_fst_MapIn in H0.
    apply MapFacts.elements_in_iff in H0.
    destruct H0.
    eapply (H x).
    apply Map.elements_2; eauto.
  Qed.


  Lemma map_valid_replay : forall T d ms1 ms2,
    @map_valid T ms1 d ->
    map_valid ms2 d ->
    map_valid ms1 (replay_disk (Map.elements ms2) d).
  Proof.
    unfold map_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.

  Lemma map_valid_replay_mem : forall T d ms1 ms2,
    @map_valid T ms1 d ->
    map_valid ms2 d ->
    map_valid (replay_mem (Map.elements ms1) ms2) d.
  Proof.
    unfold map_valid; intros.
    destruct (MapFacts.In_dec ms1 a).
    apply MapFacts.in_find_iff in i.
    destruct (Map.find a ms1) eqn:X.
    eapply H.
    apply MapFacts.find_mapsto_iff; eauto.
    tauto.
    eapply H0.
    eapply replay_mem_not_in; eauto.
  Qed.

  Lemma map_valid_replay_disk : forall T l m d,
    @map_valid T m d ->
    map_valid m (replay_disk l d).
  Proof.
    unfold map_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.






  Lemma log_valid_nodup : forall T l d,
    @log_valid T l d -> KNoDup l.
  Proof.
    unfold log_valid; intuition.
  Qed.

  Lemma map_valid_log_valid : forall T ms d,
    @map_valid T ms d ->
    log_valid (Map.elements ms) d.
  Proof.
    unfold map_valid, log_valid; intuition;
    apply KIn_exists_elt_InA in H0;
    destruct H0; simpl in H0;
    eapply H; eauto;
    apply Map.elements_2; eauto.
  Qed.


  Lemma log_valid_entries_valid : forall T ents d l raw,
    goodSize addrlen (length raw) ->
    d = replay_disk l raw ->
    @log_valid T ents d -> entries_valid ents.
  Proof.
    unfold log_valid, entries_valid; intuition.
    rewrite Forall_forall.
    intros; destruct x.
    unfold entry_valid, addr_valid; intuition.
    eapply H3; eauto; simpl.
    apply In_fst_KIn.
    eapply in_map; eauto.

    simpl; subst.
    rewrite replay_disk_length in *.
    eapply goodSize_trans; [ | apply H].
    apply Nat.lt_le_incl.
    eapply H3.
    apply In_fst_KIn.
    eapply in_map; eauto.
  Qed.

  Lemma log_vaild_filter : forall T ents d f,
    @log_valid T ents d ->
    log_valid (filter f ents) d.
  Proof.
    unfold log_valid; intuition.
    apply KNoDup_filter; eauto.
    edestruct H1; eauto.
    eapply InA_filter; eauto.
    edestruct H1; eauto.
    eapply InA_filter; eauto.
  Qed.

  Local Hint Resolve Map.is_empty_1 Map.is_empty_2.

  Lemma map_valid_replay_mem' : forall T ents d ms,
    @log_valid T ents d ->
    map_valid ms d ->
    map_valid (replay_mem ents ms) d.
  Proof.
    unfold map_valid, log_valid; intros.
    destruct (InA_dec (@eq_key_dec T) (a, v) ents).
    eapply H; eauto.
    eapply H0.
    eapply replay_mem_not_in'.
    3: eauto. apply H.
    contradict n.
    apply In_fst_KIn; simpl; auto.
  Qed.

  Lemma log_valid_replay : forall T ents d ms,
    map_valid ms d ->
    @log_valid T ents (replay_disk (Map.elements ms) d) ->
    log_valid ents d.
  Proof.
    unfold log_valid, map_valid; intros.
    split; intros.
    apply H0.
    rewrite replay_disk_length in H0.
    eapply H0; eauto.
  Qed.

  Lemma log_valid_length_eq : forall T ents d d',
    @log_valid T ents d ->
    length d = length d' ->
    log_valid ents d'.
  Proof.
    unfold log_valid; intuition.
    eapply H2; eauto.
    substl (length d').
    eapply H2; eauto.
  Qed.

  Lemma replay_disk_replay_mem : forall l m d,
    log_valid l (replay_disk (Map.elements m) d) ->
    replay_disk l (replay_disk (Map.elements m) d) =
    replay_disk (Map.elements (replay_mem l m)) d.
  Proof.
    unfold log_valid; induction l; intros; intuition; auto.
    destruct a; inversion H0; subst; simpl.
    rewrite replay_disk_updN_comm.
    rewrite IHl.
    setoid_rewrite mapeq_elements at 2.
    2: apply replay_mem_add; auto.
    rewrite replay_disk_add; auto.
    split; auto; intros.
    eapply H1.
    apply InA_cons_tl; eauto.
    contradict H3.
    apply In_fst_KIn; auto.
  Qed.

  Instance map_valid_iff_proper : forall T,
    Proper (Map.Equal ==> eq ==> iff) (@map_valid T).
  Proof.
    unfold Proper, respectful; intros; subst; split;
    apply map_valid_equal; auto.
    apply MapFacts.Equal_sym; auto.
  Qed.

  Instance map_valid_impl_proper : forall T,
    Proper (Map.Equal ==> eq ==> Basics.impl) (@map_valid T).
  Proof.
    unfold Proper, respectful, impl; intros; subst.
    eapply map_valid_equal; eauto.
  Qed.

  Instance map_valid_impl_proper2 : forall T,
    Proper (Map.Equal ==> eq ==> flip Basics.impl) (@map_valid T).
  Proof.
    unfold Proper, respectful, impl, flip; intros; subst.
    apply MapFacts.Equal_sym in H.
    eapply map_valid_equal; eauto.
  Qed.

  Lemma possible_crash_log_valid : forall T l l' ents,
    possible_crash (list2nmem l) (list2nmem l')
    -> @log_valid T ents l'
    -> log_valid ents l.
  Proof.
    intros.
    eapply log_valid_length_eq; eauto.
    apply possible_crash_list2nmem_length in H; eauto.
  Qed.

  Lemma possible_crash_replay_disk : forall ents d d',
    log_valid ents d'
    -> possible_crash (list2nmem d)
           (list2nmem d')
    -> possible_crash (list2nmem (replay_disk ents d))
      (list2nmem (replay_disk ents d')).
  Proof.
    induction ents; intros; simpl.
    unfold replay_disk; simpl; auto.
    eapply possible_crash_log_valid in H as H'; eauto.

    apply IHents.
    unfold log_valid in *.
    split.
    unfold KNoDup.
    eapply KNoDup_cons_inv; intuition eauto.
    intros.
    rewrite length_updN.
    eapply H.
    unfold KIn in *.
    eapply InA_cons_tl; eauto.

    repeat erewrite listupd_memupd; eauto.
    eapply possible_crash_upd; auto.
    destruct a; simpl; auto.

    unfold log_valid in *; intuition.
    eapply H2 with (v:=t).
    unfold KIn.
    eapply InA_cons_hd.
    unfold Map.eq_key; eauto.

    unfold log_valid in *; intuition.
    eapply H3 with (v:=snd a).
    unfold KIn.
    eapply InA_cons_hd.
    unfold Map.eq_key; eauto.
  Qed.

  Lemma crash_xform_replay_disk : forall ents d d',
    log_valid ents d'
    -> crash_xform (diskIs (list2nmem d))
     (list2nmem d')
    -> crash_xform (diskIs (list2nmem (replay_disk ents d)))
     (list2nmem (replay_disk ents d')).
  Proof.
    intros.
    eapply crash_xform_diskIs in H0.
    destruct_lift H0.
    unfold diskIs in *; subst.
    eapply crash_xform_diskIs_r; unfold diskIs; eauto.
    eapply possible_crash_replay_disk; auto.
  Qed.

  Lemma replay_disk_vsupd_vecs : forall l d,
    KNoDup l
    -> replay_disk l d = replay_disk l (vsupd_vecs d l).
  Proof.
    induction l; intros; simpl; auto.

    destruct (in_dec eq_nat_dec (fst a) (map fst l));
    denote KNoDup as HKNoDup;
    apply KNoDup_cons_inv in HKNoDup.
    rewrite replay_disk_updN_absorb; auto.
    rewrite replay_disk_updN_absorb; auto.
    rewrite <- IHl; auto.
    unfold vsupd.
    rewrite replay_disk_updN_absorb; auto.

    rewrite vsupd_vecs_vsupd_notin; auto.
    unfold vsupd.
    rewrite updN_twice.
    repeat rewrite replay_disk_updN_comm; auto.
    rewrite IHl; auto.
  Qed.

  Set Implicit Arguments.

  Fixpoint overlap V (l : list addr) (m : Map.t V) : bool :=
  match l with
  | nil => false
  | a :: rest => if (Map.mem a m) then true else overlap rest m
  end.

  Lemma overlap_firstn_overlap : forall V n l (m : Map.t V),
    overlap (firstn n l) m = true ->
    overlap l m = true.
  Proof.
    induction n; destruct l; simpl; firstorder.
    destruct (MapFacts.In_dec m n0); auto.
    rewrite Map.mem_1; auto.
    apply MapFacts.not_mem_in_iff in n1; rewrite n1 in *; auto.
  Qed.

  Lemma In_MapIn_overlap : forall V l a (ms : Map.t V),
    In a l ->
    Map.In a ms ->
    overlap l ms = true.
  Proof.
    induction l; intros; simpl.
    inversion H.
    destruct (MapFacts.In_dec ms a); auto.
    rewrite Map.mem_1; auto.
    apply MapFacts.not_mem_in_iff in n as Hx; rewrite Hx in *; auto.
    inversion H; destruct (addr_eq_dec a a0); subst; firstorder.
  Qed.

  Lemma overlap_empty : forall V al (m : Map.t V),
    Map.Empty m ->
    overlap al m = false.
  Proof.
    induction al; simpl; auto; intros.
    replace (Map.mem a m) with false; eauto.
    symmetry.
    eapply MapFacts.not_mem_in_iff.
    apply map_empty_not_In; auto.
  Qed.


  Lemma replay_disk_vsupd_vecs_nonoverlap : forall l m d,
    overlap (map fst l) m = false ->
    vsupd_vecs (replay_disk (Map.elements m) d) l =
    replay_disk (Map.elements m) (vsupd_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    destruct (MapFacts.In_dec m (fst a)); simpl in *.
    rewrite Map.mem_1 in H; congruence.
    apply MapFacts.not_mem_in_iff in n as Hx; rewrite Hx in *; auto.
    rewrite <- IHl by auto.
    unfold vsupd, vsmerge.
    rewrite replay_disk_updN_comm.
    erewrite replay_disk_selN_not_In; eauto.
    contradict n.
    apply In_map_fst_MapIn; eauto.
  Qed.

  Lemma overlap_equal : forall T l (m1 m2 : Map.t T),
    Map.Equal m1 m2 ->
    overlap l m1 = overlap l m2.
  Proof.
    induction l; intros; auto; simpl.
    destruct (Map.mem a m1) eqn:?; destruct (Map.mem a m2) eqn:?; auto.
    rewrite H in Heqb; congruence.
    rewrite H in Heqb; congruence.
  Qed.

  Instance overlap_proper : forall T,
    Proper (eq ==> Map.Equal ==> eq) (@overlap T).
  Proof.
    unfold Proper, respectful, impl; intros; subst.
    apply overlap_equal; auto.
  Qed.

  Lemma nonoverlap_replay_mem_disjoint : forall T al ents d,
    overlap al (@replay_mem T ents d) = false ->
    disjoint al (map fst ents).
  Proof.
    induction al; intuition; simpl in *.
    apply disjoint_nil_l.
    destruct (Map.mem a (replay_mem ents d)) eqn:?; try congruence.
    apply disjoint_cons_l.
    eapply IHal; eauto.
    eapply map_find_replay_mem_not_in.
    rewrite MapFacts.mem_find_b in Heqb.
    destruct (Map.find a (replay_mem ents d)) eqn:?; try congruence.
    eauto.
  Qed.

  Lemma replay_mem_nonoverlap_mono : forall T al ents m,
    overlap al (@replay_mem T ents m) = false ->
    overlap al m = false.
  Proof.
    induction al; simpl; intros; auto.
    destruct (Map.mem a m) eqn:?; 
    destruct (Map.mem a (replay_mem ents m)) eqn:?; try congruence.
    rewrite MapFacts.mem_find_b in *.
    destruct (Map.find a m) eqn:?; try congruence.
    destruct (Map.find a (replay_mem ents m)) eqn:?; try congruence.
    apply replay_mem_find_none_mono in Heqo0; congruence.
    eapply IHal; eauto.
  Qed.

  Lemma replay_disk_vsupd_vecs_disjoint : forall l ents d,
    disjoint (map fst l) (map fst ents) ->
    vsupd_vecs (replay_disk ents d) l =
    replay_disk ents (vsupd_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    destruct (In_dec addr_eq_dec (fst a) (map fst ents)); simpl in *.
    specialize (H (fst a)); simpl in H; intuition.
    rewrite <- IHl.
    unfold vsupd, vsmerge.
    rewrite replay_disk_updN_comm by auto.
    erewrite replay_disk_selN_other; auto.
    unfold disjoint in *; firstorder.
  Qed.

  Lemma replay_disk_vssync_vecs_disjoint : forall l ents d,
    disjoint l (map fst ents) ->
    vssync_vecs (replay_disk ents d) l =
    replay_disk ents (vssync_vecs d l).
  Proof.
    induction l; simpl; intros; auto.
    destruct (In_dec addr_eq_dec a (map fst ents)); simpl in *.
    specialize (H a); simpl in H; intuition.
    rewrite <- IHl.
    unfold vssync, vsmerge.
    rewrite replay_disk_updN_comm by auto.
    erewrite replay_disk_selN_other; auto.
    unfold disjoint in *; firstorder.
  Qed.

End LogReplay.

