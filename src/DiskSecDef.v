Require Import Mem Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import GenSepN.
Require Import ListPred.
Require Import List ListUtils.
Require Import Bytes.
Require Import Rec.
Require Import Arith.
Require Import Errno.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Prog ProgLoop ProgList.
Require Import ProgAuto.

Import ListNotations.
Set Implicit Arguments.

(***** WEAKENING FOR PAPER *****)
(* This is a weaker version of trace security that only checks for unseals. 
 * I overloaded the definition here to match the paper. *)
Fixpoint trace_secure pr tr :=
  match tr with
  | nil => True
  |h::tl => match h with
           | Uns t => can_access pr t
           | _ => True
           end /\ trace_secure pr tl
  end.

Lemma trace_secure_impl:
  forall tr pr,
    Sec.trace_secure pr tr -> trace_secure pr tr.
Proof.
  unfold Sec.trace_secure, trace_secure; induction tr; intros; simpl in *; auto.
  unfold op_secure in *; logic_clean.
  specialize (IHtr _ H0).
  destruct a; auto.
Qed.

Lemma trace_secure_app_split:
  forall tr1 tr2 pr,
    trace_secure pr (tr1 ++ tr2) -> trace_secure pr tr1 /\ trace_secure pr tr2.
Proof.
  unfold trace_secure; induction tr1; intros; simpl in *; auto.
  logic_clean.
  specialize (IHtr1 _ _ H0).
  destruct a; intuition.
Qed.

(* Overloaded weak version for paper *)
Fixpoint only_public_operations tr:=
  match tr with
  | nil => True
  | h::tl => match h with
            | Uns t => t = Public
            | _ => True
            end /\ only_public_operations tl
  end.

Lemma only_public_operations_impl:
  forall tr,
    Sec.only_public_operations tr -> only_public_operations tr.
Proof.
  unfold Sec.only_public_operations, only_public_operations; induction tr; intros;
  simpl in *; auto.
  logic_clean.
  specialize (IHtr H0).
  destruct a; intuition.
Qed.

Lemma only_public_operations_app:
  forall tr1 tr2,
    only_public_operations (tr1++tr2) ->
    only_public_operations tr1 /\
    only_public_operations tr2.
Proof.
  unfold only_public_operations; induction tr1; intros; simpl in *; auto.
  logic_clean.
  specialize (IHtr1 _ H0).
  destruct a; intuition.
Qed.


(****** DISKSEC ******)
Definition equivalent_for tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 = tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).


Definition blockmem_equivalent_for tag (bm1 bm2: block_mem) :=
  forall a,
    (bm1 a = None /\ bm2 a = None) \/
    (exists v1 v2,
       bm1 a = Some v1 /\ bm2 a = Some v2 /\
       fst v1 = fst v2 /\
       (fst v1 = tag -> snd v1 = snd v2)).


Definition same_except tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 <> tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).

Definition blockmem_same_except tag (bm1 bm2: block_mem) :=
  forall a,
    (bm1 a = None /\ bm2 a = None) \/
    (exists v1 v2,
       bm1 a = Some v1 /\ bm2 a = Some v2 /\
       fst v1 = fst v2 /\
       (fst v1 <> tag -> snd v1 = snd v2)).

Axiom can_access_dec: forall pr t, {can_access pr t}+{~can_access pr t}.

Lemma forall2_tag_refl:
  forall l, Forall2 (fun tb1 tb2 : tag * block => fst tb1 = fst tb2) l l.
Proof.
  induction l; simpl; intuition.
Qed.

Lemma forall2_tag_ne_refl:
  forall l t, Forall2 (fun tb1 tb2 : tag * block => fst tb1 <> t -> snd tb1 = snd tb2) l l.
Proof.
  induction l; simpl; intuition.
Qed.

Lemma forall2_tag_eq_refl:
  forall l t, Forall2 (fun tb1 tb2 : tag * block => fst tb1 = t -> snd tb1 = snd tb2) l l.
Proof.
  induction l; simpl; intuition.
Qed.

Lemma equivalent_for_refl:
  forall tag d,
    equivalent_for tag d d.
Proof.
  unfold equivalent_for; intros.
  destruct (d a); eauto.
  right; repeat eexists; eauto.
  apply forall2_tag_refl.
  eapply forall2_tag_eq_refl.
Qed.

Lemma blockmem_equivalent_for_refl:
  forall tag bm,
    blockmem_equivalent_for tag bm bm.
Proof.
  unfold blockmem_equivalent_for; intros.
  destruct (bm a); intuition.
  right; exists t, t; intuition eauto.
Qed.

Lemma blockmem_equivalent_for_empty_mem:
  forall pr, 
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag empty_mem empty_mem).
Proof.
  intros; apply blockmem_equivalent_for_refl.
Qed.

Lemma blockmem_same_except_refl:
  forall tag bm,
    blockmem_same_except tag bm bm.
Proof.
  unfold blockmem_same_except; intros.
  destruct (bm a); eauto.
  right; exists t, t; intuition eauto.
Qed.
    
Lemma same_except_refl:
  forall t d, same_except t d d.
Proof.
  unfold same_except; intros.
  destruct (d a); eauto.
  right; repeat eexists; eauto.
  apply forall2_tag_refl.
  apply forall2_tag_ne_refl.
Qed.

Lemma blockmem_same_except_upd:
  forall bm t h v1 v2,
    blockmem_same_except t (upd bm h (t, v1)) (upd bm h (t, v2)).
Proof.
  unfold blockmem_same_except; intros.
  destruct (handle_eq_dec h a); subst.
  repeat rewrite upd_eq; eauto.
  right; repeat eexists; intuition eauto.
  repeat rewrite upd_ne; eauto.
  destruct (bm a); eauto.
  right; repeat eexists; intuition eauto.
Qed.

Theorem same_except_to_equivalent_for:
  forall t1 t2 d1 d2,
    same_except t1 d1 d2 ->
    t1 <> t2 ->
    equivalent_for t2 d1 d2.
Proof.
  unfold equivalent_for, same_except; intros.
  specialize (H a); split_ors; cleanup; eauto.
  right; repeat eexists; eauto.
  apply forall2_length in H3 as Hx.
  apply forall2_forall in H3.
  eapply forall_forall2; auto.
  eapply Forall_impl; eauto.
  simpl; intros; apply H4; subst; eauto.
Qed.

Theorem blockmem_same_except_to_equivalent_for:
  forall t1 t2 d1 d2,
    blockmem_same_except t1 d1 d2 ->
    t1 <> t2 ->
    blockmem_equivalent_for t2 d1 d2.
Proof.
  unfold blockmem_equivalent_for, blockmem_same_except; intros.
  specialize (H a); split_ors; cleanup; eauto.
  right; repeat eexists; eauto.
  intros; subst; eauto.
Qed.


  Lemma blockmem_same_except_upd_same:
    forall t bm bm' h b b0,
      blockmem_same_except t bm bm' ->
      blockmem_same_except t (upd bm h (t, b)) (upd bm' h (t, b0)).
  Proof.
    unfold blockmem_same_except; intros.
    destruct (handle_eq_dec h a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    simpl in *; intuition.
    repeat rewrite upd_ne in *; eauto.
  Qed.

  Lemma blockmem_same_except_upd_eq:
    forall t bm bm' h v,
      blockmem_same_except t bm bm' ->
      blockmem_same_except t (upd bm h v) (upd bm' h v).
  Proof.
    unfold blockmem_same_except; intros.
    destruct (handle_eq_dec h a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    repeat rewrite upd_ne in *; eauto.
  Qed.


  Lemma same_except_upd_same:
    forall t d d' n b b0 b1 b2 t2 l l0,
      same_except t d d' ->
      Forall2 (fun tb1 tb2 => fst tb1 <> t -> snd tb1 = snd tb2)
              (vsmerge (t2, b1, l)) (vsmerge (t2, b2, l0)) ->
      Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) l l0 ->
      same_except t (upd d n (t, b, vsmerge (t2, b1, l)))
                  (upd d' n (t, b0, vsmerge (t2, b2, l0))).
  Proof.
    unfold same_except; intros.
    destruct (addr_eq_dec n a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    unfold vsmerge in *; simpl in *; intuition.
    unfold vsmerge in *; simpl in *; intuition.
    repeat rewrite upd_ne in *; eauto. 
  Qed.


  Lemma same_except_upd_eq:
    forall t d d' n b b1 b2 t1 t2 l l0,
      same_except t d d' ->
      Forall2 (fun tb1 tb2 => fst tb1 <> t -> snd tb1 = snd tb2)
              (vsmerge (t2, b1, l)) (vsmerge (t2, b2, l0)) ->
      Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) l l0 ->
      same_except t (upd d n (t1, b, vsmerge (t2, b1, l)))
                  (upd d' n (t1, b, vsmerge (t2, b2, l0))).
  Proof.
    unfold same_except; intros.
    destruct (addr_eq_dec n a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    unfold vsmerge in *; simpl in *; intuition.
    unfold vsmerge in *; simpl in *; intuition.
    repeat rewrite upd_ne in *; eauto. 
  Qed.

  Lemma same_except_sync_mem:
    forall t d d',
      same_except t d d' ->
      same_except t (sync_mem d) (sync_mem d').
  Proof.
    unfold sync_mem, same_except; intros.
    specialize (H a); split_ors; cleanup; eauto.
    destruct x, x0; simpl in *.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    unfold vsmerge in *; simpl in *; intuition.
    inversion H1; eauto.
    unfold vsmerge in *; simpl in *; intuition.
    inversion H2; eauto.
  Qed.


Fixpoint index {T} (EQ:forall (x y:T), {x=y}+{x<>y}) (item: T) (list: list T) :=
  match list with
  |nil => 0
  |h::tl => if EQ item h then
             0
           else
             S(index EQ item tl)
  end.
   
Lemma index_app_l:
  forall T EQ l1 l2 (t:T),
    In t l1 ->
    index EQ t (l1++l2) = index EQ t l1.
Proof.
  induction l1; intros.
  inversion H.
  destruct H; subst; simpl in *.
  destruct (EQ t t); try congruence.
  destruct (EQ t a); subst; eauto.
Qed.

Lemma index_in_lt:
  forall T EQ l (t:T),
    In t l -> index EQ t l < length l.
Proof.
  induction l; intros.
  inversion H.
  destruct H; subst; simpl.
  destruct (EQ t t); try congruence; try omega.
  destruct (EQ t a); subst; eauto; try omega.
  specialize IHl with (1:=H); omega.
Qed.

Lemma index_in_selN:
  forall T EQ l (t:T) def,
    In t l -> selN l (index EQ t l) def = t.
Proof.
  induction l; intros; inversion H; subst.
  simpl; auto.
  destruct (EQ t t); try congruence; auto.
  simpl.
  destruct (EQ t a); subst; eauto.
Qed.


Lemma possible_crash_equivalent:
  forall d1 cd1 d2 pr,
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2) ->
    possible_crash d1 cd1 ->
    exists cd2, possible_crash d2 cd2 /\
    (forall tag, can_access pr tag -> equivalent_for tag cd1 cd2).
Proof.
  unfold equivalent_for, possible_crash; intros.
  exists(fun i => match cd1 i with
          | Some (v, []) =>
            match d1 i with
            | Some vs1 =>
              match d2 i with
              | Some vs2 =>
                Some (selN (vsmerge vs2)
                       (index tagged_block_dec v (vsmerge vs1))
                        tagged_block0, [])
              | _ => None (** Not reachable **)
              end
            | _ => None (** Not reachable **)
            end
          | _ => None
          end); split; intros.
  {
    specialize (H0 a); intuition.
    specialize H with (1:= can_access_public pr) as Hx;
    specialize (Hx a); intuition; cleanup; try congruence.
    left; auto.
    cleanup.
    specialize H with (1:= can_access_public pr) as Hx;
    specialize (Hx a); intuition; cleanup; try congruence.
    right; do 2 eexists; eauto.
    repeat split; eauto.
    apply in_selN.
    apply forall2_length in H5; setoid_rewrite <- H5.
    eapply index_in_lt; eauto.
  }

  {
    specialize (H0 a); intuition.
    cleanup; left;  eauto.
    cleanup.
    specialize H with (1:=H1) as Hx;
    specialize (Hx a); intuition; cleanup; try congruence.
    right; do 2 eexists; eauto.
    repeat split; eauto.
    eapply forall2_selN with
        (n:= (index tagged_block_dec x0 (vsmerge x1))) in H6.
    constructor; eauto.
    erewrite index_in_selN in H6; eauto.
    simpl; auto.
    eapply index_in_lt; eauto.
    
    eapply forall2_selN with
        (n:= (index tagged_block_dec x0 (vsmerge x1))) in H7.
    constructor; eauto.
    erewrite index_in_selN in H7; eauto.
    simpl; auto.
    eapply index_in_lt; eauto.
  }
  
  Unshelve.
  all: exact tagged_block0.
Qed.

Lemma possible_crash_same_except:
  forall tag d1 cd1 d2,
    same_except tag d1 d2 ->
    possible_crash d1 cd1 ->
    exists cd2, possible_crash d2 cd2 /\
    same_except tag cd1 cd2.
Proof.
  unfold same_except, possible_crash; intros.
  exists(fun i => match cd1 i with
          | Some (v, []) =>
            match d1 i with
            | Some vs1 =>
              match d2 i with
              | Some vs2 =>
                Some (selN (vsmerge vs2)
                       (index tagged_block_dec v (vsmerge vs1))
                        tagged_block0, [])
              | _ => None (** Not reachable **)
              end
            | _ => None (** Not reachable **)
            end
          | _ => None
          end); split; intros.
  {
    specialize (H0 a); intuition.
    specialize (H a); intuition; cleanup; try congruence.
    left; auto.
    cleanup.
    specialize (H a); intuition; cleanup; try congruence.
    right; do 2 eexists; eauto.
    repeat split; eauto.
    apply in_selN.
    apply forall2_length in H5; setoid_rewrite <- H5.
    eapply index_in_lt; eauto.
  }

  {
    specialize (H0 a); intuition.
    cleanup; left;  eauto.
    cleanup.
    specialize (H a); intuition; cleanup; try congruence.
    right; do 2 eexists; eauto.
    repeat split; eauto.
    eapply forall2_selN with
        (n:= (index tagged_block_dec x0 (vsmerge x1))) in H4.
    constructor; eauto.
    erewrite index_in_selN in H4; eauto.
    simpl; auto.
    eapply index_in_lt; eauto.
    
    eapply forall2_selN with
        (n:= (index tagged_block_dec x0 (vsmerge x1))) in H5.
    constructor; eauto.
    erewrite index_in_selN in H5; eauto.
    simpl; auto.
    eapply index_in_lt; eauto.
  }
  
  Unshelve.
  all: exact tagged_block0.
Qed.
  
  