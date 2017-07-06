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

Definition prog_secure T (p : prog T) (pre : pred) (post : pred):=
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

Module TwoLevel.
Module L1.

  (* Memory represented as an array of indices *)
  
  Record array_rep := {
    Log : list valuset;
    Data : list valuset
  }.
  
  Definition rep (arr: array_rep) : @pred addr addr_eq_dec _ :=
    (arrayN (@ptsto addr _ _) 0 (Log arr) * arrayN (@ptsto addr _ _) (length (Log arr)) (Data arr))%pred.

  Definition read_log arr i def:=
    if lt_dec i (length (Log arr)) then
      v <- Read i; Ret v
    else
      Ret def.

  Definition write_log arr i v def:=
    if lt_dec i (length (Log arr)) then
      _ <- Write i v; 
      let vs := selN (Log arr) i def in
      Ret ({| Log:= updN (Log arr) i (v, vsmerge vs); Data:= (Data arr) |})
    else
      Ret arr.
  
  Definition read_data arr i def:=
    if lt_dec i (length (Data arr)) then
      v <- Read (i + (length (Log arr))); Ret v
    else
      Ret def.

  Definition write_data arr i v def:=
    if lt_dec i (length (Data arr)) then
      _ <- Write (i + (length (Log arr))) v; 
      let vs := selN (Data arr) i def in
      Ret ({| Log:= Log arr; Data:= updN (Data arr) i (v, vsmerge vs) |})
    else
      Ret arr.

End L1.

Module L2.
Import L1.

  Variable file_size: nat. 
  Record file := { 
     Meta: list valuset;
     Data: list valuset
     }.
  Definition file_rep:= list file.
  
  Definition rep (fr: file_rep) := arrayN  (@ptsto addr _ _) 0 fr.
  
  Definition upd_file (fr: file_rep) fn bn vs fdef:= 
          let file :=  (selN fr fn fdef) in
          updN fr fn  {| 
                                Meta:= Meta file;
                                Data:= (updN (Data file) bn vs)
                            |}.

  Definition read_from_file arr (fr: file_rep) fn bn vsdef:=
    if lt_dec fn (length fr) then
      if lt_dec bn file_size then
        vs <- read_data arr (file_size * fn + bn) vsdef; 
        Ret (arr, vs)
      else
        Ret (arr, vsdef)
    else
      Ret (arr, vsdef).
  
  Definition write_to_file arr fr fn bn v fdef vsdef:=
    if lt_dec fn (length fr) then
      let file := selN fr fn fdef in
      if lt_dec bn file_size then
        arr' <- write_data arr (file_size * fn + bn) v vsdef; 
        let vs := selN (Data file) bn vsdef in
        Ret (arr', upd_file fr fn bn (v, vsmerge vs) fdef)
      else
        Ret (arr, fr)
    else
      Ret (arr, fr).
  
End L2.


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




Module NewDef.
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
  @prog_secure_strict _ _ addr_eq_dec _ (L1.read_data arr i def)((i+length(L1.Log arr))|-> v) ((i+length(L1.Log arr))|-> v).
Proof.
  intros.
  unfold L1.read_data.
  destruct (lt_dec i (length (L1.Data arr))); eauto.
Qed.

Theorem write_data_secure_strict:
  forall arr i v vs def,
  @prog_secure_strict _ _ addr_eq_dec _ (L1.write_data arr i v def)((i+length(L1.Log arr))|-> vs) ((i+length(L1.Log arr))|-> vs \/ (i+length(L1.Log arr))|-> (v, vsmerge vs)).
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
  forall arr fr fn bn vsdef (f: L2.file),
      @prog_secure_strict _ _ addr_eq_dec _ (L2.read_from_file arr fr fn bn vsdef) (fn|-> f) (fn|-> f).
Proof.
    intros.
    unfold L2.read_from_file.
    destruct (lt_dec fn (length fr)); eauto.
    destruct (lt_dec bn L2.file_size); eauto.
    econstructor; eauto.
Admitted.

End NewDef.


End TwoLevel.



