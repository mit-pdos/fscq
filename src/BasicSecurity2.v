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

Set Implicit Arguments.

(** * Some helpful [prog] combinators and proofs *)

Lemma sync_invariant_possible_sync : forall (F: rawpred) (m: rawdisk),
    F m ->
    sync_invariant F ->
    possible_sync m =p=> F.
Proof.
  unfold sync_invariant; eauto.
Qed.

Hint Resolve sync_invariant_possible_sync.

Definition pred_upd_w (pre: pred) (a: addr) (v: valu) : pred :=
  fun (m: @mem _ addr_eq_dec valuset) => 
    match m a with
    | None => False
    | Some vs => let (v', ovs) := vs in
                          match ovs with
                          | nil => False
                          | h :: t => v = v' /\ pre (upd m a (h, t))
                          end
    end.                  

Lemma definition_is_ok: forall pre a v vs m,
m a = Some vs -> pre m <-> pred_upd_w pre a v (upd m a (v, vsmerge vs)).
Proof.
    unfold pred_upd_w; simpl; intros.
    - unfold vsmerge; destruct vs; simpl.
    rewrite upd_eq; auto.
    rewrite upd_repeat.
    rewrite upd_nop; auto.
    split; intros; auto.
    destruct H0; auto.
Qed.


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

Definition addr_is_in {AT AEQ V} (a: AT) (pre: pred):=
  forall (m: @mem AT AEQ V), pre m -> indomain a m.

Theorem read_secure:
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
         admit. (* Possible to prove from H2 H3 H4 H7 H11 H16 *)
     + eauto.
     + eauto.
     + eauto.
  - (* Failed *)
    exfalso.
    admit. (* Possible to prove from H4 H10 *)
  - (* Crashed *)
    right.
    repeat eexists; eauto.
  Unshelve.
  constructor.
Admitted.
  
Theorem write_secure:
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
         admit. (* Possible to prove from H2 H3 H4 H7 H11 H16 *)
     + eapply diskIs_sep_star_upd. 2: eauto. eauto.
     + eapply diskIs_sep_star_upd. 2: eauto. eauto.
     + rewrite upd_eq; auto.
         rewrite upd_repeat.
         rewrite upd_nop; auto.
         admit. (* Possible to solve from H4 H5 H21 *)
  - (* Failed *)
    exfalso.
    admit. (* Possible to prove from H4 H10 *)
  - (* Crashed *)
    right.
    repeat eexists; eauto.
Admitted.

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

Lemma addr_is_in_find: forall a cs v m,
    MapUtils.AddrMap.Map.find a (CSMap cs) = Some v ->
    addr_is_in a (rep cs m).
Proof.
    intros.
    unfold addr_is_in, indomain; intros.
    unfold rep in *.
    destruct_lift H0.
    eapply addr_valid_mem_valid in H as Hx.
    2: eauto.
    deex.
    eapply MemPred.mem_pred_extract with (a:=a) in H0; eauto.
    unfold cachepred in H0 at 2.
    rewrite H in H0.
    destruct v_2;
    destruct_lift H0;
    apply sep_star_comm in H0;
    apply ptsto_subset_valid in H0;
    deex; eexists; eauto.
Qed.

Theorem cache_writeback_secure:
  forall a cs m,
  prog_secure (writeback a cs) (rep cs m) (rep cs m \/ exists w, (pred_upd_w (rep cs m) a w)).
Proof.
   unfold writeback in *; simpl in *; intros.
   destruct (MapUtils.AddrMap.Map.find a (CSMap cs)) eqn:D; simpl in *.
   - destruct p; simpl in *.
      destruct b; simpl in *.
      + eapply bind_secure; [ apply write_secure; eauto | intros; apply ret_secure_frame_impl_l; cancel].
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
      eapply bind_secure; [apply read_secure | intros; apply ret_secure_frame_impl_l; cancel].
      
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






















