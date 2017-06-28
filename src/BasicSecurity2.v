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

Definition pred_upd_w (pre: @pred addr addr_eq_dec _) (a: addr) (v: valu):=
  fun m => forall (m': @Mem.mem addr addr_eq_dec _), 
  exists vs, m' a = Some vs -> m = Mem.upd m' a (v, vsmerge vs) -> pre m' . 

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
  forall (m: @Mem.mem AT AEQ V), pre m -> indomain a m.

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
     + intros.
         assert (A: m4 = m').
         * apply functional_extensionality; intros.
            destruct (addr_eq_dec a x1);
            subst. rewrite H5; rewrite H3; eauto.
            erewrite <- Mem.upd_ne.
            rewrite H9.
            apply Mem.upd_ne.
            all: omega.
         * subst; eauto.
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

Transparent BUFCACHE.read.

Theorem cache_writeback_secure:
  forall a cs m,
  addr_is_in a (BUFCACHE.rep cs m) ->
  prog_secure (BUFCACHE.writeback a cs) (BUFCACHE.rep cs m) 
                                                                    (BUFCACHE.rep cs m \/ exists w, (pred_upd_w (BUFCACHE.rep cs m) a w)).
Proof.
   unfold BUFCACHE.writeback in *; simpl in *; intros.
   destruct (MapUtils.AddrMap.Map.find a (CSMap cs)) eqn:D; simpl in *.
   - destruct p; simpl in *.
      destruct b; simpl in *.
      + eapply bind_secure.
          * apply write_secure; eauto.
          * intros.
             apply ret_secure_frame_impl_l; cancel.
      + apply ret_secure_frame_impl_l; cancel.
  - apply ret_secure_frame_impl_l; cancel.
Qed.

Theorem cache_evict_secure:
  forall a cs m,
  addr_is_in a (BUFCACHE.rep cs m) ->
  prog_secure (BUFCACHE.evict a cs) (BUFCACHE.rep cs m) 
                                                            (BUFCACHE.rep cs m \/ exists w, (pred_upd_w (BUFCACHE.rep cs m) a w)).
Proof.
  unfold BUFCACHE.evict in *; simpl in *; intros.
  eapply bind_secure.
  - apply cache_writeback_secure; eauto.
  - intros.
    destruct (MapUtils.AddrMap.Map.find a (CSMap x)) eqn:D; simpl in *.
    apply ret_secure_frame.
    apply ret_secure_frame.
Qed.

Theorem cache_maybe_evict_secure:
  forall m cs,
  prog_secure (BUFCACHE.maybe_evict cs) (BUFCACHE.rep cs m) 
                                                                     (BUFCACHE.rep cs m \/ exists a w, (pred_upd_w (BUFCACHE.rep cs m) a w)).
Proof.
  unfold BUFCACHE.maybe_evict in *; simpl in *; intros.
  destruct (lt_dec (CSCount cs) (CSMaxCount cs)); simpl.
  - apply ret_secure_frame_impl_l; cancel.
  -  destruct (MapUtils.AddrMap.Map.find 0 (CSMap cs)) eqn:D.
      + eapply bind_secure.
      
          * assert (A: {| CSMap := CSMap cs;
                                 CSMaxCount := CSMaxCount cs;
                                 CSCount := CSCount cs;
                                 CSEvict := CSEvict cs |} = cs).
             destruct cs; simpl; eauto.
             rewrite A; apply cache_evict_secure.
             unfold addr_is_in; intros.
             unfold indomain.
             admit. (* XXX *)
          * intros; apply ret_secure_frame_impl_l; cancel.
      + destruct (MapUtils.AddrMap.Map.elements (CSMap cs)) eqn:D0.
          * eapply ret_secure_frame_impl_l; cancel.
          * destruct p; simpl in *.
             eapply bind_secure.
             ** eapply cache_evict_secure.
                 unfold addr_is_in; intros.
                 unfold indomain.
                 admit. (* XXX *)
            ** intros; apply ret_secure_frame_impl_l; cancel.
Admitted.

Theorem cache_read_secure:
  forall a m cs,
  addr_is_in a (BUFCACHE.rep cs m) ->
  prog_secure (BUFCACHE.read a cs) (BUFCACHE.rep cs m) 
                                                            (BUFCACHE.rep cs m \/ exists a w, (pred_upd_w (BUFCACHE.rep cs m) a w)).
Proof.
    unfold BUFCACHE.read in *; simpl in *; intros.
    eapply bind_secure; [ apply cache_maybe_evict_secure |  intros ].
    destruct (MapUtils.AddrMap.Map.find a (CSMap x)) eqn:D.
    - destruct p; apply ret_secure_frame.
    - eapply bind_secure; [ apply alertmodified_secure_frame| intros].
      eapply bind_secure; [apply read_secure | intros; apply ret_secure_frame].
      unfold addr_is_in; intros.
      destruct H0.
      eauto.
      destruct_lift H0.
      admit. (* XXX *)
Admitted.
    
    destruct (lt_dec (CSCount cs) (CSMaxCount cs)); simpl.
  - apply ret_secure_frame_impl_l; cancel.
  -  destruct (MapUtils.AddrMap.Map.find 0 (CSMap cs)) eqn:D.
      + eapply bind_secure.
      
          * assert (A: {| CSMap := CSMap cs;
                                 CSMaxCount := CSMaxCount cs;
                                 CSCount := CSCount cs;
                                 CSEvict := CSEvict cs |} = cs).
             destruct cs; simpl; eauto.
             rewrite A; apply cache_evict_secure.
             unfold addr_is_in; intros.
             unfold indomain.
             admit. (* XXX *)
          * intros; apply ret_secure_frame_impl_l; cancel.
      + destruct (MapUtils.AddrMap.Map.elements (CSMap cs)) eqn:D0.
          * eapply ret_secure_frame_impl_l; cancel.
          * destruct p; simpl in *.
             eapply bind_secure.
             ** eapply cache_evict_secure.
                 unfold addr_is_in; intros.
                 unfold indomain.
                 admit. (* XXX *)
            ** intros; apply ret_secure_frame_impl_l; cancel.
Admitted.





























