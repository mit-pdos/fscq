Require Import Prog ProgMonad.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import List.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import ListUtils.
Require Import ProofIrrelevance.
Require Import BasicProg.
Require Import Array.
Require Import Bytes.
Require Import Mem.
Require Import Cache. 
Require Import GenSepN.
Require Import ClassicalFacts.

Set Implicit Arguments.


  Ltac sub_inv := 
  match goal with
  | [H: ?a = _, H0: ?a = _ |- _ ] => rewrite H in H0; inversion H0; subst; eauto
  end.
Ltac sep_unfold H := unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H; repeat deex.


(** * Some helpful [prog] combinators and proofs *)

Lemma sync_invariant_possible_sync : forall (F: rawpred) (m: rawdisk),
    F m ->
    sync_invariant F ->
    possible_sync m =p=> F.
Proof.
  unfold sync_invariant; eauto.
Qed.

Hint Resolve sync_invariant_possible_sync.

(* 
    Meaning of the definition:
      Take two memories 
          m1 = x \union mp
          m2 = y \union mp
      Assume: 
          F1 x
          F2 y
          pre mp
          If p executes with m1 vm hm, then produces out1
       Then:
          there exists two memories such that
              m1' = x' \union mr
              m2' = y' \union mr
          memories are m1'(m2') vm' hm' after executing p on m1(m2)
          output of both executions is r
          post mr
        OR
          "same for crash"
*)
(* Frames does not say for the remainder memory is unchanged or not. *)
(* 
    Can we say
      Defintion pequal P Q := forall m, P m <-> Q m.
      Lemma exists_diskIs: forall F, exists p m, F m -> pequal F ([[ P ]] * diskIs m).
*)

Definition prog_secure T (p : prog T) (pre : pred) (post : pred) :=
  forall m1 m2 mp F1 F2 out1 vm hm,

  (F1 * diskIs mp)%pred m1 ->
  (F2 * diskIs mp)%pred m2 ->
  pre mp ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' vm' hm' mr,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * diskIs mr)%pred m1' /\
   (F2 * diskIs mr)%pred m2' /\
   post mr) \/

  (exists m1' m2' hm' mc,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   (F1 * diskIs mc)%pred m1' /\
   (F2 * diskIs mc)%pred m2').

Theorem bind_secure:
  forall T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) pre post1 post2,
  prog_secure p1 pre post1 ->
  (forall x, prog_secure (p2 x) post1 post2) ->
  prog_secure (Bind p1 p2) pre post2.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* p1 Finished *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H11).
    intuition; repeat deex; try congruence.
    inversion H4; subst.
    specialize (H0 r _ _ _ _ _ _ _ _ H5 H6 H8 H14).
    intuition; repeat deex.
    + left.
      do 6 eexists; intuition eauto.
    + right.
      do 4 eexists; intuition eauto.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
    right.
    inversion H4; subst.
    do 4 eexists; intuition.
    constructor.
    eauto.
    eauto.
    eauto.
Qed.

Theorem bind_secure_weaker:
  forall T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) pre post1 post2,
  prog_secure p1 pre post1 ->
  (forall m vm hm m' vm' hm' r, exec m vm hm p1 (Finished m' vm' hm' r) -> prog_secure (p2 r) post1 post2) ->
  prog_secure (Bind p1 p2) pre post2.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* p1 Finished *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H11).
    intuition; repeat deex; try congruence.
    inversion H4; subst.
    specialize (H0 _ _ _ _ _ _ r H11 _ _ _ _ _ _ _ _ H5 H6 H8 H14).
    intuition; repeat deex.
    + left.
      do 6 eexists; intuition eauto.
    + right.
      do 4 eexists; intuition eauto.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
    right.
    inversion H4; subst.
    do 4 eexists; intuition.
    constructor.
    eauto.
    eauto.
    eauto.
Qed.

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

(* Failed attempt 1 *)
Module Failed1.

Definition prog_secure' T (p : prog T) (pre post: @pred _ addr_eq_dec _) :=
  forall m mp F vm hm,
  (F * diskIs mp)%pred m ->
  pre mp ->
  (exists r vm' hm' mr, exec mp vm hm p (Finished mr vm' hm' r) /\ post mr)
  \/ exists hm' mc, exec mp vm hm p (Crashed _ mc hm').
  
Theorem bind_secure':
  forall T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) pre post1 post2,
  prog_secure' p1 pre post1 ->
  (forall x, prog_secure' (p2 x) post1 post2) ->
  prog_secure' (Bind p1 p2) pre post2.
Proof.
  unfold prog_secure'; intros.
  specialize (H _ _ _ vm hm H1 H2).
  destruct H;  repeat deex.
  eapply diskIs_sep_star_split in H1; repeat deex.
  inversion H; subst.
  specialize (H0 r (mem_union mp0 mr) mr F vm' hm').
  destruct H0; eauto.
  apply sep_star_mem_union; auto.
  apply mem_disjoint_comm; eapply exec_mem_disjoint; eauto.
  assert (A: diskIs m m).
  apply diskIs_id.
  apply H6 in A.
  apply mem_disjoint_comm; eapply diskIs_mem_disjoint; eauto.
  repeat deex.
  left; repeat eexists; eauto.
  repeat deex.
  right; repeat eexists; eauto.
  right; repeat eexists; eauto.
Qed.

Theorem bind_secure'_rev_l:
  forall T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) pre post,
  T2 
  -> EqDec T2
  -> prog_secure' (Bind p1 p2) pre post
  -> exists post1, prog_secure' p1 pre post1.
Proof.
  unfold prog_secure'; intros; eexists; intros. 
  - specialize (H _ _ _ vm hm H0 H1).
    destruct H; repeat deex.
    * inv_exec.
      left; repeat eexists; eauto.
      apply diskIs_id.
    * inv_exec.
      left; repeat eexists; eauto.
      right; repeat eexists; eauto.
  Unshelve.
  all: trivial.
  repeat constructor; auto.
Qed.


Lemma exec_sep_star:
  forall T (p: prog T) m1 m1' m2 vm vm' hm hm' r,
  mem_disjoint m1 m2
  -> exec m1 vm hm p (Finished m1' vm' hm' r)
  -> exec (mem_union m1 m2) vm hm p (Finished (mem_union m1' m2) vm' hm' r).
Proof.
  induction p; intros; inv_exec; try solve [repeat econstructor; eauto].
  - repeat econstructor.
     apply mem_union_addr; eauto.
  - rewrite mem_union_upd.
    repeat econstructor.
    apply mem_union_addr; eauto.
  - admit. (* Sync *)
  - rewrite mem_union_upd.
    repeat econstructor.
    apply mem_union_addr; eauto.
  - inversion H8; eauto.
  - inversion H14; eauto. 
  - eapply  XBindFinish.
    eapply IHp; eauto.
    eapply H; eauto.
    eapply exec_mem_disjoint; eauto.
Abort.

Lemma exec_eq:
  forall T (p: prog T) m vm hm m1' vm1' hm1' r1 m2' vm2' hm2' r2,
  exec m vm hm p (Finished m1' vm1' hm1' r1)
  ->  exec m vm hm p (Finished m2' vm2' hm2' r2)
  -> m1' = m2' /\ vm1' = vm2' /\ hm1' = hm2' /\ r1 = r2.
Proof.
  induction p; intros; try solve [inv_exec; inv_exec; eauto; sub_inv].
  - admit. (* Trim changes memory nondeterministically *)
  - admit. (* VarAlloc changes vm and also returns nondeterministically *)
  - admit. (* VarGet returns nondeterministically *)
  - admit. (* Rdtsc returns nondeterministically *)
  - inv_exec; inv_exec.
    edestruct IHp with (m1':= m') (m2':= m'0); eauto.
    destruct H1; subst.
    destruct H2; subst.
    eauto.
Abort.

Theorem prog_secure'_is_noninterference :
  forall T (p : prog T) pre post a v1 v2 m1 m2 mp vm hm,
  prog_secure' p pre post ->
  (a |+> v1 * diskIs mp)%pred m1 ->
  (a |+> v2 * diskIs mp)%pred m2 ->
  pre mp ->
  forall m1' vm' hm' v,
  exec m1 vm hm p (Finished m1' vm' hm' v) ->
  exists m2' vm'' hm'',
  exec m2 vm hm p (Finished m2' vm'' hm'' v).
Proof.
  induction p; unfold prog_secure' in *; intros.
  - specialize (H _ _ _ vm hm H0 H2) as Hx.
     intuition; repeat deex; try congruence.
     inv_exec; inv_exec.
     repeat eexists; eauto.
     inv_exec; inv_exec.
  - specialize (H _ _ _ vm hm H0 H2) as Hx.
     intuition; repeat deex; try congruence.
     inv_exec; inv_exec.
     admit. (*Solvable*)
     inv_exec; inv_exec.
     (*Not solvable! Definition is wrong!*)
Abort.
End Failed1.

Module Variant2.
Definition prog_secure' T (p : prog T) (pre : pred) (post : pred) :=
  forall m1 m2 F1 F2 out1 vm hm,

  (F1 * pre)%pred m1 ->
  (F2 * pre)%pred m2 ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' vm' hm',
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * post)%pred m1' /\
   (F2 * post)%pred m2') \/

  (exists m1' m2' hm' mc,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   (F1 * diskIs mc)%pred m1' /\
   (F2 * diskIs mc)%pred m2').
   
Theorem prog_secure'_is_noninterference :
  forall T (p : prog T) pre post a v1 v2 m1 m2 mp vm hm,
  prog_secure' p pre post ->
  (a |+> v1 * diskIs mp)%pred m1 ->
  (a |+> v2 * diskIs mp)%pred m2 ->
  pre mp ->
  forall m1' vm' hm' v,
  exec m1 vm hm p (Finished m1' vm' hm' v) ->
  exists m2' vm'' hm'',
  exec m2 vm hm p (Finished m2' vm'' hm'' v).
Proof.
  unfold prog_secure'; intros.
  erewrite diskIs_pred in H0; eauto.
  erewrite diskIs_pred in H1; eauto.
  specialize (H _ _ _ _ _ _ _ H0 H1 H3).
  intuition; repeat deex; try congruence.
  do 3 eexists.
  inversion H4; subst.
  eauto.
Qed.

Theorem sync_secure':
  prog_secure' Sync (fun m => forall a, exists vs, m a = Some vs) (fun m => forall a, exists v, m a = Some (v, nil)).
Proof.
  unfold prog_secure'; intros.
  inv_exec.
  specialize (H _ _ _ vm hm H1 H2).
  destruct H;  repeat deex.
  eapply diskIs_sep_star_split in H1; repeat deex.
  inversion H; subst.
  specialize (H0 r (mem_union mp0 mr) mr F vm' hm').
  destruct H0; eauto.
  apply sep_star_mem_union; auto.
  apply mem_disjoint_comm; eapply exec_mem_disjoint; eauto.
  assert (A: diskIs m m).
  apply diskIs_id.
  apply H6 in A.
  apply mem_disjoint_comm; eapply diskIs_mem_disjoint; eauto.
  repeat deex.
  left; repeat eexists; eauto.
  repeat deex.
  right; repeat eexists; eauto.
  right; repeat eexists; eauto.
Qed.

Lemma prog_secure_eq:
  forall T (p: prog T) pre post,
  prog_secure' p pre post ->
  prog_secure p pre post.
Proof.
  unfold prog_secure, prog_secure'; intros.
  erewrite diskIs_pred in H0; eauto.
  erewrite diskIs_pred in H1; eauto.
  specialize (H _ _ _ _ _ _ _ H0 H1 H3).
  intuition; repeat deex; try congruence.
  sep_unfold H5.
  sep_unfold H7.
  left; repeat eexists; eauto.
  (* Memory contents can be different *)
Abort.
End Variant2.

Definition valu0 n := bytes2valu  (natToWord (valubytes*8) n).
Definition valuset0 n := (valu0 n, valu0 (S n)::nil).

Theorem sync_not_secure:
  forall pre post,
  (exists m, pre m /\ exists a, m a = None) ->
  ~ prog_secure Sync pre post.
Proof.
  unfold prog_secure, not; intros.
  repeat deex.
  remember (insert (@empty_mem _ addr_eq_dec _) a (valuset0 0)) as mx.
 remember (insert (@empty_mem _ addr_eq_dec _) a (valuset0 1)) as my.
  edestruct H0; eauto.
  - instantiate (1:= mem_union mx m).
    instantiate (1:= diskIs mx).
    apply sep_star_mem_union; auto.
    unfold mem_disjoint, not; intros; repeat deex.
    unfold insert, empty_mem in H3.
    destruct (addr_eq_dec a0 a); subst; try sub_inv.
    inversion H3.
  
  - instantiate (1:= mem_union my m).
    instantiate (1:= diskIs my).
    apply sep_star_mem_union; auto.
    unfold mem_disjoint, not; intros; repeat deex.
    unfold insert, empty_mem in H3.
    destruct (addr_eq_dec a0 a); subst; try sub_inv.
    inversion H3.
    
  - repeat deex.
    inversion H3; subst; clear H3.
    inv_exec.
    sep_unfold H4.
    inversion H4; inversion H8; subst; clear H4 H8.
    assert (A: (mem_union (insert empty_mem a (valuset0 0)) m2) a = Some (valuset0 0)).
    unfold mem_union; simpl.
    unfold insert, empty_mem; simpl.
    destruct (addr_eq_dec a a); try omega; auto.
    rewrite <- H3 in A.
    unfold sync_mem, mem_union, insert, empty_mem, valuset0 in A; simpl in A.
    destruct (addr_eq_dec a a); try omega; auto.
    inversion A.
    
  - repeat deex.
    inversion H3.
    
  Unshelve.
  all: repeat econstructor; eauto.
Qed.


Theorem trim_secure:
  forall a vs,
  prog_secure (Trim a) (a|->vs)%pred (a|->?)%pred.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - left. 
    do 6 eexists; repeat split.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H1) in H0.
      eapply ptsto_valid' in H0; eauto.
    + eapply diskIs_sep_star_upd. 2: eauto.
      unfold ptsto in H1; intuition eauto.
    + eapply diskIs_sep_star_upd. 2: eauto.
      unfold ptsto in H1; intuition eauto.
    + eapply pimpl_apply.
      2: eapply ptsto_upd.
      2: pred_apply; cancel.
      cancel.
  - exfalso.
    rewrite (diskIs_pred _ H1) in H.
    eapply ptsto_valid' in H.
    congruence.
Qed.

Theorem varalloc_secure:
  forall T (a: T),
  prog_secure (VarAlloc a) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  left; repeat eexists; eauto.
Qed.

Theorem vardelete_secure:
  forall i,
  prog_secure (VarDelete i) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  - left; repeat eexists; eauto.
  - inversion H8; subst.
     (* Fail Case not possible to prove *)
Abort.


Theorem varget_secure:
  forall T i,
  prog_secure (@VarGet T i) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  - left; repeat eexists; eauto.
  - inversion H8; subst.
    sub_inv.
     (* Fail Case not possible to prove *)
Abort.



Theorem varget_secure:
  forall T i (v: T),
  prog_secure (VarSet i v) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  - left; repeat eexists; eauto.
  - (* Fail Case not possible to prove *)
Abort.


Theorem debug_secure:
  forall s a,
  prog_secure (Debug s a) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  left; repeat eexists; eauto.
Qed.

Theorem rdtsc_secure:
  prog_secure (Rdtsc) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  left; repeat eexists; eauto.
Qed.


Theorem hash_secure:
  forall sz buf,
  prog_secure (@Hash sz buf) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  left; repeat eexists; eauto.
Qed.

Theorem hash2_secure:
  forall sz1 sz2 buf1 buf2,
  prog_secure (@Hash2 sz1 sz2 buf1 buf2) emp emp.
Proof.
  unfold prog_secure; intros.
  apply emp_empty_mem_only in H1; subst.
  inv_exec.
  left; repeat eexists; eauto.
Qed.






Definition addr_is_in {AT AEQ V} (a: AT) (pre: pred):=
  forall (m: @mem AT AEQ V), pre m -> indomain a m.  
  
Definition valu0:= bytes2valu  (natToWord (valubytes*8) 0).
  
Lemma addr_is_in_id:
  forall AT AEQ V a vs,
  @addr_is_in AT AEQ V a (a |-> vs).
Proof.
  unfold addr_is_in; intros.
  destruct H.
  eexists; eauto.
Qed.

Lemma pred_upd_w_pimpl:
  forall a vs v,
  pred_upd_w (a |-> vs) a v ⇨⇨ a |-> (v, vsmerge vs).
Proof.
  unfold pred_upd_w, pimpl; intros.
  destruct (m a) eqn:D.
  destruct p.
  destruct l.
  inversion H.
  destruct H; subst.
  destruct H0.
  rewrite upd_eq in H; auto.
  inversion H.
  unfold vsmerge; split; eauto.
  intros.
  specialize (H0 a').
  apply H0 in H1 as Hx.
  rewrite upd_ne in Hx; auto.
  inversion H.
Qed.

Lemma addr_is_in_find: forall a cs v m,
    MapUtils.AddrMap.Map.find a (CSMap cs) = Some v ->
    addr_is_in a (BUFCACHE.rep cs m).
Proof.
    intros.
    unfold addr_is_in, indomain; intros.
    unfold BUFCACHE.rep in *.
    destruct_lift H0.
    eapply BUFCACHE.addr_valid_mem_valid in H as Hx.
    2: eauto.
    deex.
    eapply MemPred.mem_pred_extract with (a:=a) in H0; eauto.
    unfold BUFCACHE.cachepred in H0 at 2.
    rewrite H in H0.
    destruct v_2;
    destruct_lift H0;
    apply sep_star_comm in H0;
    apply ptsto_subset_valid in H0;
    deex; eexists; eauto.
Qed.


       


(* Basic Commands *)

Theorem pimpl_secure:
  forall T (p : prog T) pre pre' post post',
  pre' =p=> pre ->
  post =p=> post' ->
  prog_secure p pre post ->
  prog_secure p pre' post'.
Proof.
  unfold prog_secure; intros.
  apply H in H4.
  specialize (H1 _ _ _ _ _ _ _ _ H2 H3 H4 H5).
  intuition; repeat deex.
  left.
  do 6 eexists; intuition eauto.
Qed.

Theorem read_secure':
  forall a pre,
  addr_is_in a pre ->
  prog_secure (Read a) pre pre.
Proof.
  unfold prog_secure, addr_is_in; intros.
   
  pose proof H0 as Hx.
  unfold sep_star in Hx. 
  rewrite sep_star_is in Hx. 
  unfold sep_star_impl in Hx.
  repeat deex.
  edestruct H; intros; eauto.
  
  pose proof H1 as Hx.
  unfold sep_star in Hx. 
  rewrite sep_star_is in Hx. 
  unfold sep_star_impl in Hx.
  repeat deex.
  inversion H8; inversion H12; subst.
  
  inv_exec.
  - (* Finished *)
     left.
     repeat eexists.
     + econstructor.
       econstructor.
       rewrite mem_union_comm; auto.
       rewrite mem_union_comm in H16; auto.
       erewrite mem_union_disjoint_sel in H16; eauto.
       apply mem_union_addr; eauto.
       rewrite mem_disjoint_comm; auto.
       rewrite mem_disjoint_comm; auto.
     + eauto.
     + eauto.
     + eauto.
  - (* Failed *)
    apply mem_union_none_sel in H9.
    destruct H9.
    rewrite H5 in H9; inversion H9.
  - (* Crashed *)
    right.
    repeat eexists; eauto.
Qed.

Theorem read_secure:
  forall a vs,
  prog_secure (Read a) (a|->vs) (a|->vs).
Proof.
  intros.
  apply read_secure'.
  apply addr_is_in_id.
Qed.

  
Theorem write_secure':
  forall a v pre,
  addr_is_in a pre ->
  prog_secure (Write a v) pre (pred_upd_w pre a v).
Proof.
  unfold prog_secure, addr_is_in, pred_upd_w; intros.

  pose proof H0 as Hx.
  unfold sep_star in Hx. 
  rewrite sep_star_is in Hx. 
  unfold sep_star_impl in Hx.
  repeat deex.
  edestruct H; intros; eauto.
  
  pose proof H1 as Hx.
  unfold sep_star in Hx. 
  rewrite sep_star_is in Hx. 
  unfold sep_star_impl in Hx.
  repeat deex.
  inversion H8; inversion H12; subst.
  
  inv_exec.
  - (* Finished *)
     left.
     repeat eexists.
     + econstructor.
       econstructor.
       rewrite mem_union_comm; auto.
       rewrite mem_union_comm in H21; auto.
       erewrite mem_union_disjoint_sel in H21; eauto.
       apply mem_union_addr; eauto.
       rewrite mem_disjoint_comm; auto.
       rewrite mem_disjoint_comm; auto.
     + eapply diskIs_sep_star_upd. 2: eauto. eauto.
     + eapply diskIs_sep_star_upd. 2: eauto. eauto.
     + rewrite upd_eq; auto.
       rewrite upd_repeat.
       rewrite upd_nop; auto.
       erewrite <- mem_union_disjoint_sel; eauto.
       rewrite mem_union_comm; eauto.
       rewrite mem_disjoint_comm; auto.
       rewrite mem_disjoint_comm; auto.
  - (* Failed *)
    apply mem_union_none_sel in H14.
    destruct H14.
    rewrite H5 in H9; inversion H9.
  - (* Crashed *)
    right.
    repeat eexists; eauto.
Qed.

Theorem write_secure:
  forall a v vs,
  prog_secure (Write a v) (a |-> vs) (a |-> (v, vsmerge vs)).
Proof.
  intros.
  eapply pimpl_secure; [eauto | |].
  2: apply write_secure'.
  apply pred_upd_w_pimpl.
  apply addr_is_in_id.
Qed.

Theorem bind_secure:
  forall T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) pre post1 post2,
  prog_secure p1 pre post1 ->
  (forall x, prog_secure (p2 x) post1 post2) ->
  prog_secure (Bind p1 p2) pre post2.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* p1 Finished *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H11).
    intuition; repeat deex; try congruence.
    inversion H4; subst.
    specialize (H0 r _ _ _ _ _ _ _ _ H5 H6 H8 H14).
    intuition; repeat deex.
    + left.
      do 6 eexists; intuition eauto.
    + right.
      do 4 eexists; intuition eauto.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
    right.
    inversion H4; subst.
    do 4 eexists; intuition.
    constructor.
    eauto.
    eauto.
    eauto.
Qed.

Theorem frame_secure:
  forall T (p : prog T) pre post F,
  prog_secure p pre post ->
  prog_secure p (F * pre)%pred (F * post)%pred.
Proof.
  unfold prog_secure; intros.
  eapply diskIs_sep_star_split in H2; repeat deex; intuition.
  rewrite H6 in H0.
  rewrite H6 in H1.
  apply sep_star_assoc in H0.
  apply sep_star_assoc in H1.
  specialize (H _ _ _ _ _ _ _ _ H0 H1 H2 H3).
  intuition; repeat deex.
  - left.
    apply sep_star_assoc in H7.
    apply sep_star_assoc in H8.
    rewrite (diskIs_sep_star_combine _ _ H4 H10) in H7; destruct_lift H7.
    rewrite (diskIs_sep_star_combine _ _ H4 H10) in H8; destruct_lift H8.
    do 6 eexists; intuition eauto.
  - right.
    apply sep_star_assoc in H7.
    apply sep_star_assoc in H9.
    assert ((diskIs mc) mc) by congruence.
    rewrite (diskIs_sep_star_combine _ _ H4 H5) in H7; destruct_lift H7.
    rewrite (diskIs_sep_star_combine _ _ H4 H5) in H9; destruct_lift H9.
    do 4 eexists; intuition eauto.
Qed.

Lemma alertmodified_secure_frame:
  forall F,
  prog_secure (AlertModified) F F.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  left.
  do 6 eexists; intuition.
  eauto.
  eauto.
  eauto.
Qed.


Theorem ret_secure:
  forall T (x : T),
  prog_secure (Ret x) emp emp.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  left.
  do 6 eexists; intuition.
  eauto.
  eauto.
  eauto.
Qed.

Lemma ret_secure_frame:
  forall T (x : T) F,
  prog_secure (Ret x) F F.
Proof.
  intros.
  eapply pimpl_secure.
  3: eapply frame_secure.
  3: apply ret_secure.
  all: cancel.
Qed.

Lemma ret_secure_frame_impl_l:
  forall T (x : T) F F',
  F =p=> F' ->
  prog_secure (Ret x) F F'.
Proof.
  intros.
  eapply pimpl_secure.
  eauto.
  2: apply ret_secure_frame.
  eauto.
Qed.

Import BUFCACHE.

Module V1.
Theorem cache_writeback_secure:
  forall a cs m,
  prog_secure (writeback a cs) (rep cs m) (rep cs m \/ exists w, (pred_upd_w (rep cs m) a w)).
Proof.
   unfold writeback in *; simpl in *; intros.
   destruct (MapUtils.AddrMap.Map.find a (CSMap cs)) eqn:D; simpl in *.
   - destruct p; simpl in *.
      destruct b; simpl in *.
      + eapply bind_secure; [ apply write_secure'; eauto | intros; apply ret_secure_frame_impl_l; cancel].
          eapply addr_is_in_find; eauto.
      + apply ret_secure_frame_impl_l; cancel.
  - apply ret_secure_frame_impl_l; cancel.
Qed.


Theorem cache_evict_secure:
  forall a cs m,
  prog_secure (evict a cs) (rep cs m) (rep cs m \/ exists w, (pred_upd_w (rep cs m) a w)).
Proof.
  unfold evict in *; simpl in *; intros.
  eapply bind_secure; [ apply cache_writeback_secure; eauto | intros ].
  destruct (MapUtils.AddrMap.Map.find a (CSMap x)) eqn:D; simpl in *.
  apply ret_secure_frame.
  apply ret_secure_frame.
Qed.

Theorem cache_maybe_evict_secure:
  forall m cs,
  prog_secure (maybe_evict cs) (rep cs m) (rep cs m \/ exists a w, (pred_upd_w (rep cs m) a w)).
Proof.
  unfold maybe_evict in *; simpl in *; intros.
  destruct (lt_dec (CSCount cs) (CSMaxCount cs)); simpl.
  - apply ret_secure_frame_impl_l; cancel.
  -  destruct (MapUtils.AddrMap.Map.find 0 (CSMap cs)) eqn:D.
      + eapply bind_secure; intros.
      
          * assert (A: {| CSMap := CSMap cs;
                                 CSMaxCount := CSMaxCount cs;
                                 CSCount := CSCount cs;
                                 CSEvict := CSEvict cs |} = cs).
             destruct cs; simpl; eauto.
             rewrite A; apply cache_evict_secure.
          * apply ret_secure_frame_impl_l; cancel.
      + destruct (MapUtils.AddrMap.Map.elements (CSMap cs)) eqn:D0.
          * eapply ret_secure_frame_impl_l; cancel.
          * destruct p; simpl in *.
             eapply bind_secure.
             ** eapply cache_evict_secure.
            ** intros; apply ret_secure_frame_impl_l; cancel.
Qed.

Transparent read.
Theorem cache_read_secure:
  forall a m cs,
  addr_is_in a (rep cs m) ->
  prog_secure (read a cs) (rep cs m) (rep cs m \/ exists a w, (pred_upd_w (rep cs m) a w))%pred.
Proof.
    unfold read in *; simpl in *; intros.
    eapply bind_secure; [ apply cache_maybe_evict_secure |  intros ].
    destruct (MapUtils.AddrMap.Map.find a (CSMap x)) eqn:D.
    - destruct p; apply ret_secure_frame.
    - eapply bind_secure; [ apply alertmodified_secure_frame| intros].
      eapply bind_secure; [apply read_secure' | intros; apply ret_secure_frame_impl_l; cancel].
      
      unfold addr_is_in; intros.
      destruct H0.
      eauto.
      destruct_lift H0.
      unfold pred_upd_w in *.
      destruct (m0 dummy) eqn:D0.
      destruct p.
      destruct l.
      inversion H0.
      destruct H0; subst.
      apply H in H1.
      destruct (addr_eq_dec a dummy).
      subst.
      eexists; eauto.
      eapply indomain_upd_ne; eauto.
      inversion H0.
Qed.

Transparent write.
Theorem cache_write_secure:
  forall a v m cs,
  prog_secure (write a v cs) (rep cs m) (rep cs m \/ exists a w, (pred_upd_w (rep cs m) a w))%pred.
Proof.
  unfold write in *; simpl in *; intros.
  eapply bind_secure; [ apply cache_maybe_evict_secure |  intros ].
  destruct (MapUtils.AddrMap.Map.find a (CSMap x)) eqn:D;
  eapply ret_secure_frame.
Qed.

Transparent sync.
Theorem cache_sync_secure:
  forall a cs m,
  prog_secure (sync a cs) (rep cs m) (rep cs m \/ exists w, (pred_upd_w (rep cs m) a w)).
Proof.
  unfold sync in *; simpl in *; intros.
  eapply bind_secure; [ apply cache_writeback_secure |  intros; apply ret_secure_frame ].
Qed.
End V1.

Module V2.
Theorem cache_writeback_secure:
  forall a cs vs,
  prog_secure (writeback a cs) (a|->vs) (a|-> vs \/ exists v, a|-> (v, vsmerge vs))%pred.
Proof.
  unfold writeback in *; simpl in *; intros.
  destruct (MapUtils.AddrMap.Map.find a (CSMap cs)) eqn:D; simpl in *.
  - destruct p; simpl in *.
    destruct b; simpl in *.
    + eapply bind_secure; 
      [ apply write_secure; eauto | 
        intros; apply ret_secure_frame_impl_l; cancel].
    + apply ret_secure_frame_impl_l; cancel.
  - apply ret_secure_frame_impl_l; cancel.
Qed.

Theorem cache_evict_secure:
  forall a cs vs,
  prog_secure (evict a cs) (a|->vs) (a|-> vs \/ exists v, a|-> (v, vsmerge vs))%pred.
Proof.
  unfold evict in *; simpl in *; intros.
  eapply bind_secure; [ apply cache_writeback_secure; eauto | intros ].
  destruct (MapUtils.AddrMap.Map.find a (CSMap x)) eqn:D; simpl in *.
  apply ret_secure_frame.
  apply ret_secure_frame.
Qed.
End V2.



Inductive prog_secure_strict: forall T AT AEQ V, prog T -> @pred AT AEQ V -> @pred AT AEQ V -> Prop :=
| PSRet : forall T AT AEQ V (v: T), 
      @prog_secure_strict T AT AEQ V (Ret v) emp emp
| PSRead : forall V a (vs: V),
      @prog_secure_strict _ _ addr_eq_dec _ (Read a) (a|->vs) (a|->vs)
| PSWrite : forall a v vs,
      @prog_secure_strict _ _ addr_eq_dec _ (Write a v) (a |-> vs)%pred (a |-> (v, vsmerge vs))%pred
| PSBind : forall AT AEQ V T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) (pre post1 post2: @pred AT AEQ V),
      prog_secure_strict p1 pre post1 ->
      (forall x, prog_secure_strict (p2 x) post1 post2) ->
      prog_secure_strict (Bind p1 p2) pre post2
| PSImpl : forall T AT AEQ V (p : prog T) (pre pre' post post': @pred AT AEQ V),
      pre' =p=> pre ->
      post =p=> post' ->
      prog_secure_strict p pre post ->
      prog_secure_strict p pre' post'
| PSFrame : forall T AT AEQ V (p : prog T) (pre post F: @pred AT AEQ V),
  prog_secure_strict p pre post ->
  prog_secure_strict p (F * pre)%pred (F * post)%pred.

Hint Constructors prog_secure_strict.



Module TwoLevel.

Module L1.
  (* Memory represented as an array of indices *)
  Record array_rep := {
    Data : list valuset
  }.
  
  Definition rep (arr: array_rep) : @pred addr addr_eq_dec _ := 
      arrayN (@ptsto addr _ _) 0 (Data arr).
  
  Definition read_data arr i def:=
    if lt_dec i (length (Data arr)) then
      v <- Read i; Ret v
    else
      Ret def.

  Definition write_data arr i v def:=
    if lt_dec i (length (Data arr)) then
      _ <- Write i v; 
      let vs := selN (Data arr) i def in
      Ret ({| Data:= updN (Data arr) i (v, vsmerge vs) |})
    else
      Ret arr.
End L1.

Module L2.
Import L1.

  Variable file_size: nat. 
  Hypothesis file_size_nonzero: file_size <> 0.
  Record file := { 
     Data: list valuset
     }.
  Definition file_rep:= list file.
  
  Definition rep (fr: file_rep) := (arrayN  (@ptsto addr _ _) 0 fr * [[ forall f, In f fr -> length (Data f) = file_size ]])%pred.
  
  Definition upd_file (fr: file_rep) fn bn vs fdef:= 
          let file :=  (selN fr fn fdef) in
          updN fr fn  {| Data:= (updN (Data file) bn vs) |}.

  Definition read_from_file arr (fr: file_rep) fn bn fdef vsdef:=
    if lt_dec fn (length fr) then
      let file := selN fr fn fdef in
      if lt_dec bn (length (Data file)) then
        vs <- read_data arr (file_size * fn + bn) vsdef; 
        Ret (arr, vs)
      else
        Ret (arr, vsdef)
    else
      Ret (arr, vsdef).
  
  Definition write_to_file arr fr fn bn v fdef vsdef:=
    if lt_dec fn (length fr) then
      let file := selN fr fn fdef in
      if lt_dec bn (length (Data file)) then
        arr' <- write_data arr (file_size * fn + bn) v vsdef; 
        let vs := selN (Data file) bn vsdef in
        Ret (arr', upd_file fr fn bn (v, vsmerge vs) fdef)
      else
        Ret (arr, fr)
    else
      Ret (arr, fr).
  
  Definition arr2file arr : (@mem addr addr_eq_dec file) :=
  fun a => let fc := firstn file_size (skipn (file_size * a) (L1.Data arr)) in
           match fc with
           | nil => None
           | _ => Some {| Data := fc |}
           end.           

  Definition equiv (pd: pred) (pu: pred) :=
   forall md arr,
      L1.rep arr md
      -> pd md
      -> pu (arr2file arr).
      
      
  Inductive prog_secure T (p: prog T) pre post :=
  | STD :
      prog_secure_strict p pre post
      -> prog_secure p pre post
  | REL : forall pre' post',
      equiv pre' pre
      -> equiv post' post
      -> prog_secure_strict p pre' post'
      -> prog_secure p pre post.
            
End L2.

Lemma ret_secure_strict_frame : forall T AT AEQ V (v: T) (F: @pred AT AEQ V) ,
    prog_secure_strict (Ret v) F F.
Proof.
  intros; eapply PSImpl.
  3: eapply PSFrame.
  3: eauto.
  cancel.
  cancel.
Qed.

Lemma ret_secure_strict_frame_pimpl : forall T AT AEQ V (v: T) (F F': @pred AT AEQ V) ,
    F =p=> F' ->
    prog_secure_strict (Ret v) F F'.
Proof.
  intros; eapply PSImpl.
  3: eapply PSFrame.
  3: eauto.
  cancel.
  cancel.
Qed.

Hint Resolve ret_secure_strict_frame.
Hint Resolve ret_secure_strict_frame_pimpl.

Theorem read_data_secure_strict:
  forall V arr i (v: V) def,
  @prog_secure_strict _ _ addr_eq_dec _ (L1.read_data arr i def) (i|-> v) (i|-> v).
Proof.
  intros.
  unfold L1.read_data.
  destruct (lt_dec i (length (L1.Data arr))); eauto.
Qed.

Theorem write_data_secure_strict:
  forall arr i v vs def,
  @prog_secure_strict _ _ addr_eq_dec _ (L1.write_data arr i v def)(i|-> vs) (i|-> vs \/ i|-> (v, vsmerge vs)).
Proof.
  intros.
  unfold L1.write_data.
  destruct (lt_dec i (length (L1.Data arr))); eauto.
  econstructor; eauto.
  intros; apply ret_secure_strict_frame_pimpl; cancel.
  apply ret_secure_strict_frame_pimpl; cancel.
Qed.

Hint Resolve read_data_secure_strict.
Hint Resolve write_data_secure_strict.


Theorem read_from_file_secure_strict:
  forall arr fr fn bn fdef vsdef (f: L2.file) Ff,
      L2.rep fr (L2.arr2file arr)
      -> (Ff * fn |-> f)%pred (list2nmem fr)
      -> L2.prog_secure (L2.read_from_file arr fr fn bn fdef vsdef) (fn|-> f)%pred (fn|-> f)%pred.
Proof.
    intros.
    unfold L2.rep in *.
    (* apply list2nmem_array_mem_eq in H0; subst.
    rewrite <- H0 in H. *)

    unfold L2.read_from_file.
    destruct (lt_dec fn (length fr)); try solve [econstructor; eauto].
    destruct (lt_dec bn (length (L2.Data fr ⟦ fn ⟧))); try solve [econstructor; eauto].
    
    eapply L2.REL.
    
    - instantiate (1:= arrayN (ptsto (V:=valuset)) (L2.file_size * fn) (L2.Data f)).
    
    unfold L2.equiv, L1.rep, L2.rep; intros m arr' Hr1 Hu.
    apply list2nmem_array_mem_eq in Hr1; subst.
    destruct_lift H.
    apply emp_star; apply sep_star_comm; apply mem_except_ptsto.
    unfold L2.arr2file.
    destruct (firstn L2.file_size (skipn (L2.file_size * fn) (L1.Data arr'))) eqn:D.
     + apply length_zero_iff_nil in D.
       rewrite firstn_length in D.
       destruct (lt_dec (length (skipn (L2.file_size * fn) (L1.Data arr'))) L2.file_size).
       * rewrite min_r in D; try omega.
         assert (A: (skipn (L2.file_size * fn) (L1.Data arr') = nil)).
         apply length_zero_iff_nil; auto.
         apply emp_star in Hu; apply arrayN_list2nmem in Hu.
         rewrite A in *; simpl in *.
         rewrite firstn_nil in Hu.
         eapply list2nmem_sel in H0; subst.
         rewrite H0 in *.
         apply length_zero_iff_nil in Hu; rewrite Hu in *; omega.
         repeat constructor; assumption.
       * rewrite min_l in D; try omega.
         exfalso; apply L2.file_size_nonzero; auto.
     + rewrite <- D in *.
       apply emp_star in Hu; eapply arrayN_list2nmem in Hu.
       destruct_lift H.
       specialize (H3 f).
       rewrite H3 in Hu.
       rewrite <- Hu; destruct f; simpl; auto.
       eapply in_selN in l.
       eapply list2nmem_sel in H0; subst.
       rewrite H0 in *; eauto.
       repeat constructor; assumption.
     + unfold emp; intros.
       destruct (addr_eq_dec fn a); subst.
       apply mem_except_eq.
       rewrite mem_except_ne; auto.
       assert (list2nmem (list2nmem (L1.Data arr')))
       destruct (lt_dec a fn).
       
       unfold L2.arr2file.
       destruct (firstn L2.file_size (skipn (L2.file_size * a) (L1.Data arr'))) eqn:D; auto.
         + apply length_zero_iff_nil in D.
           rewrite firstn_length in D.
           destruct (lt_dec (length (skipn (L2.file_size * fn) (L1.Data arr'))) L2.file_size).
           * rewrite min_r in D; try omega.
             assert (A: (skipn (L2.file_size * fn) (L1.Data arr') = nil)).
             apply length_zero_iff_nil; auto.
             apply emp_star in Hu; apply arrayN_list2nmem in Hu.
             rewrite A in *; simpl in *.
             rewrite firstn_nil in Hu.
             eapply list2nmem_sel in H0; subst.
             rewrite H0 in *.
             apply length_zero_iff_nil in Hu; rewrite Hu in *; omega.
             repeat constructor; assumption.
           * rewrite min_l in D; try omega.
             exfalso; apply L2.file_size_nonzero; auto.
       
     unfold L2.arr2file.
       destruct (firstn L2.file_size (skipn (L2.file_size * a') (L1.Data arr'))) eqn:D; auto.
       eapply nth_error_In.
       Search nth_error.
       apply ptsto_valid' in H0.
       unfold nth_error, list2nmem in *.
       Search list2nmem selN.
    Locate "|->?".
    Search exis ptsto.
    eexists; eapply list2nmem_array_exis.
    Search arrayN_ex ptsto.
    apply list2nmem_array_pick.
    rewrite <- Hr2 in Hu; clear Hr2.
    destruct Hu.
    unfold L2.arr2file in *; simpl in *.
    destruct (firstn L2.file_size (skipn (L2.file_size * fn) (L1.Data arr'))) eqn:D.
    inversion H1.
    eapply list2nmem_sel_inb.

    eapply L2.REL; [ | | econstructor; eauto].
    
    econstructor.
    unfold list2nmem.
    erewrite selN_map.
    Search selN length.
    destruct (firstn L2.file_size (skipn (L2.file_size * a) (L1.Data arr0))) eqn:D.
Admitted.

Theorem read_log_secure:
  forall arr i v def,
  prog_secure (L1.read_log arr i def)(i|-> v) (i|-> v).
Proof.
  intros.
  unfold L1.read_log.
  destruct (lt_dec i (length (L1.Log arr))).
  eapply bind_secure.
  apply read_secure.
  intros; apply ret_secure_frame.
  apply ret_secure_frame.
Qed.

Theorem write_log_secure:
  forall arr i v vs def,
  prog_secure (L1.write_log arr i v def)(i|-> vs) (i|-> vs \/ i|-> (v, vsmerge vs)).
Proof.
  intros.
  unfold L1.write_log.
  destruct (lt_dec i (length (L1.Log arr))).
  eapply bind_secure.
  apply write_secure.
  intros; apply ret_secure_frame_impl_l; cancel.
  apply ret_secure_frame_impl_l; cancel.
Qed.

Theorem read_data_secure:
  forall arr i v def,
  prog_secure (L1.read_data arr i def)((i+length(L1.Log arr))|-> v) ((i+length(L1.Log arr))|-> v).
Proof.
  intros.
  unfold L1.read_data.
  destruct (lt_dec i (length (L1.Data arr))).
  eapply bind_secure.
  apply read_secure.
  intros; apply ret_secure_frame.
  apply ret_secure_frame.
Qed.

Theorem write_data_secure:
  forall arr i v vs def,
  prog_secure (L1.write_data arr i v def)((i+length(L1.Log arr))|-> vs) ((i+length(L1.Log arr))|-> vs \/ (i+length(L1.Log arr))|-> (v, vsmerge vs)).
Proof.
  intros.
  unfold L1.write_data.
  destruct (lt_dec i (length (L1.Data arr))).
  eapply bind_secure.
  apply write_secure.
  intros; apply ret_secure_frame_impl_l; cancel.
  apply ret_secure_frame_impl_l; cancel.
Qed.






End TwoLevel.



