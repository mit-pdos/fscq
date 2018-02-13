Require Export Prog ProgMonad.
Require Export Pred.
Require Export Omega.
Require Export SepAuto.
Require Export Word.
Require Export FunctionalExtensionality.
Require Export List.
Require Export AsyncDisk.
Require Export ListUtils.
Require Export BasicProg.
Require Export Array.
Require Export Bytes.
Require Export Mem.
Require Export GenSepN.

Set Implicit Arguments.

Ltac sub_inv := 
  match goal with
  | [H: ?a = _, H0: ?a = _ |- _ ] => rewrite H in H0; inversion H0; subst; eauto
  end.
Ltac sep_unfold H := unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H; repeat deex; repeat match goal with [H: diskIs _ _ |- _] => inversion H; subst; clear H end.

Ltac split_hyp:= repeat match goal with [H: _ /\ _ |- _] => destruct H end.

Definition valu0 n := bytes2valu  (natToWord (valubytes*8) n).
Definition valuset0 n := (valu0 n, valu0 (S n)::nil).

Definition singleton AT AEQ V (a: AT) (v: V) : @mem AT AEQ V := 
  fun a' => if (AEQ a' a) then Some v else None.

Notation "l [[ a ]] ? d" := (selN l a d) (at level 35).

Lemma mem_disjoint_sync_mem_l:
  forall AT AEQ (m1 m2: @mem AT AEQ _),
  mem_disjoint m1 m2
  -> mem_disjoint (sync_mem m1) m2.
Proof.
  unfold mem_disjoint, sync_mem in *; intuition.
  apply H.
  repeat deex.
  exists a.
  destruct (m1 a); try congruence.
  destruct (m2 a); try congruence.
  eauto.
Qed.

Lemma exec_mem_disjoint:
  forall T (p: prog T) m1 m2 m3 vm hm  vm' hm' r,
  mem_disjoint m1 m2
  -> exec m1 vm hm p (Finished m3 vm' hm' r)
  -> mem_disjoint m3 m2.
Proof.
  induction p; intros; inv_exec; auto.
  eapply mem_disjoint_upd; eauto.
  apply mem_disjoint_sync_mem_l; auto.
  eapply mem_disjoint_upd; eauto.
  eapply H; [ | eauto].
  eapply IHp; eauto.
Qed.

Lemma diskIs_id: forall AT AEQ V (m:Mem.mem), @diskIs AT AEQ V m m.
Proof. intros; unfold diskIs; reflexivity. Qed.

Hint Resolve diskIs_id.

Lemma diskIs_mem_disjoint :
  forall AT AEQ V (m m1 m2: @mem AT AEQ V),
  (diskIs m1 ✶ diskIs m2)%pred m
  -> mem_disjoint m1 m2.
Proof.
  intros.
  unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
  repeat deex.
  destruct H1; destruct H3; subst; auto.
Qed.

Lemma mem_union_disjoint_sel:
  forall AT AEQ V (m1 m2: @mem AT AEQ V) a v,
  mem_disjoint m1 m2 ->
  m1 a = Some v ->
  mem_union m1 m2 a = m1 a.
Proof.
 intros. 
 apply mem_union_sel_l; auto.
 eapply mem_disjoint_either; eauto.
Qed.

Lemma list2nmem_ptsto_in:
  forall V (l: list V) F a v ,
  (F * a|-> v)%pred (list2nmem l)
  -> In v l.
Proof.
  induction l; intros.
  apply ptsto_valid' in H; unfold list2nmem in *; simpl in *; congruence.
  apply ptsto_valid' in H as Hx; unfold list2nmem in Hx; simpl in *.
  destruct a0.
  left; congruence.
  erewrite selN_map in Hx.
  right; eapply IHl.
  inversion Hx.
  apply list2nmem_array_pick.
  apply list2nmem_inbound in H; simpl in *; omega.
  apply list2nmem_inbound in H; simpl in *; omega.
  Unshelve.
  auto.
Qed.

Lemma diskIs_mem_union:
  forall AT AEQ V (m1 m2: @mem AT AEQ V),
  mem_disjoint m1 m2
  -> diskIs (mem_union m1 m2) <=p=> (diskIs m1 * diskIs m2)%pred.
Proof.
  split; unfold diskIs, mem_union, pimpl; intros.
  rewrite <- H0.
  unfold_sep_star; repeat eexists; eauto.
  sep_unfold H0; auto.
Qed.

Lemma pred_diskIs:
  forall AT AEQ V (pre: @pred AT AEQ V),
  pre =p=> exists m, diskIs m * [[ pre m ]].
Proof.
  unfold pimpl; intros.
  exists m.
  apply sep_star_lift_apply'; auto.
Qed.

Lemma skipn_is_nil:
  forall A (l: list A) n ,
  skipn n l = nil
  -> l = nil \/ n >= length l.
Proof.
  induction l; intros; auto.
  destruct n; simpl in *.
  inversion H.
  apply IHl in H.
  destruct H;
  right; subst; simpl; omega.
Qed.

Lemma list2nmem_mem_except_diskIs:
  forall A (l: list A) m a def,
  a < length l
  -> (a |-> (selN l a def))%pred m
  -> (diskIs (mem_except (list2nmem l) a) * diskIs m)%pred (list2nmem l).
Proof.
  intros.
  unfold_sep_star; repeat eexists; eauto.
  extensionality x.
  unfold mem_union, mem_except.
  destruct (Nat.eq_dec x a).
  destruct H0.
  subst.
  rewrite H0; apply list2nmem_sel_inb; auto.
  
  
  destruct (list2nmem l x); auto.
  destruct H0.
  symmetry; eauto.
  unfold mem_disjoint, mem_except.
  unfold not; intros; repeat deex.
  destruct (Nat.eq_dec a0 a).
  congruence.
  destruct H0.
  rewrite H1 in H3.
  congruence.
  omega.
Qed.

Lemma list2nmem_arrayN_ex_diskIs_ptsto:
  forall A (l: list A) m a def,
  a < length l
  -> (arrayN_ex (ptsto (V:= A)) l a * diskIs m)%pred (list2nmem l)
  -> (a |-> (selN l a def))%pred m.
Proof.
  intros.
  sep_unfold H0.
  assert (A0: list2nmem l a = m2 a).
  rewrite H1.
  apply mem_union_sel_r; auto.
  unfold arrayN_ex in H2.
  sep_unfold H2.
  apply mem_union_sel_none.
  apply list2nmem_array_mem_eq in H4; subst.
  apply list2nmem_oob.
  rewrite firstn_length_le; omega.
  eapply arrayN_oob_lt; eauto; omega.
  erewrite list2nmem_sel_inb in A0; eauto.
  split; intros; eauto.
  destruct (lt_dec a' (length l)).
  
  unfold arrayN_ex in H2.
  sep_unfold H2.
  destruct (lt_dec a a').
  eapply mem_disjoint_either; eauto.
  erewrite mem_union_sel_r; eauto.
  eapply arrayN_selN with (F := emp).
  pred_apply; cancel.
  omega.
  destruct l; simpl in *.
  omega.
  rewrite skipn_length.
  omega.
  eapply arrayN_oob; eauto.
  rewrite firstn_length_l; omega.
  
  eapply mem_disjoint_either; eauto.
  rewrite mem_union_sel_l; eauto.
  
  apply list2nmem_array_mem_eq in H5; subst.
  eapply list2nmem_sel_inb.
  rewrite firstn_length_l; omega.
  eapply arrayN_oob_lt; eauto; omega.
  
  eapply mem_union_none_sel.
  rewrite <- H1.
  apply list2nmem_oob; omega.
  Unshelve.
  all: auto.
Qed.
  
Lemma diskIs_ptsto_eq:
  forall AT AEQ V a v (m: @mem AT AEQ V),
    (a|->v)%pred m
    -> diskIs m <=p=> (a|->v)%pred.
Proof.
  intros.
  split.
  erewrite diskIs_pred; eauto.
  erewrite pred_diskIs; eauto.
  cancel.
  eapply ptsto_complete in H; eauto; subst; eauto.
Qed.


Lemma arrayN_ex_ptsto_merge:
  forall AEQ V (l: list V) a def,
  a < length l
  -> arrayN (@ptsto _ AEQ V) 0 l <=p=> arrayN_ex (@ptsto _ AEQ V) l a * a|->(selN l a def).
Proof.
  split; unfold pimpl; intuition.
  apply list2nmem_array_mem_eq in H0; subst.
  eapply list2nmem_array_pick; auto.
  eapply arrayN_isolate with (i:=a); simpl; auto.
  pred_apply; unfold arrayN_ex; cancel.
Qed.

  
Lemma mem_union_eq_l:
  forall AT AEQ V (m1 m2 m2': @mem AT AEQ V),
    m2 = m2'
    -> mem_union m1 m2 = mem_union m1 m2'.
Proof.
  intros; subst; auto.
Qed.

Lemma mem_union_eq_r:
  forall AT AEQ V (m1 m1' m2: @mem AT AEQ V),
    m1 = m1'
    -> mem_union m1 m2 = mem_union m1' m2.
Proof.
  intros; subst; auto.
Qed.

Lemma arrayN_mem_eq:
  forall V l a m m',
  arrayN (ptsto (V:=V)) a l m
  -> arrayN (ptsto (V:=V)) a l m'
  -> m = m'.
Proof.
  induction l; simpl; intuition; eauto.
  apply emp_empty_mem_only in H.
  apply emp_empty_mem_only in H0.
  subst; auto.
  sep_unfold H.
  sep_unfold H0.
  specialize (IHl _ _ _ H4 H6).
  eapply ptsto_complete in H2; eauto.
  subst; auto.
Qed.

Lemma arrayN_ex_ptsto_eq:
  forall AEQ V (l: list V) a v m m',
  (arrayN_ex (@ptsto _ AEQ V) l a * a|->v)%pred m
  -> (arrayN_ex (@ptsto _ AEQ V) l a * a|->v)%pred m'
  -> m = m'.
Proof.
  intuition.
  unfold arrayN_ex in *.
  sep_unfold H.
  sep_unfold H0.
  apply list2nmem_array_mem_eq in H3; subst.
  apply list2nmem_array_mem_eq in H7; subst.
  eapply ptsto_complete in H4; eauto; subst.
  eapply arrayN_mem_eq in H6; eauto; subst; eauto.
Qed.



