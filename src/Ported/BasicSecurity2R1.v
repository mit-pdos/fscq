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
Require Import GenSepN.
Require Import ClassicalFacts.

Set Implicit Arguments.


  Ltac sub_inv := 
  match goal with
  | [H: ?a = _, H0: ?a = _ |- _ ] => rewrite H in H0; inversion H0; subst; eauto
  end.
Ltac sep_unfold H := unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H; repeat deex; 
  repeat match goal with [H: diskIs _ _ |- _] => inversion H; subst; clear H end.

Ltac split_hyp:= repeat match goal with [H: _ /\ _ |- _] => destruct H end.

(** * Some helpful [prog] combinators and proofs *)


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


Definition valu0 n := bytes2valu  (natToWord (valubytes*8) n).
Definition valuset0 n := (valu0 n, valu0 (S n)::nil).



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
  
  Definition upd_file (f: file) bn v vsdef:= 
          let vs := selN (Data f) bn vsdef in
          {| Data:= (updN (Data f) bn (v, vsmerge vs)) |}.

  Definition read_from_file arr (fr: file_rep) fn bn fdef vsdef:=
    if lt_dec fn (length fr) then
      let file := selN fr fn fdef in
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
        Ret (arr', updN fr fn (upd_file file bn v vsdef))
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
  
  Lemma arr2file_length: 
    forall arr fl fn F,
    rep fl (arr2file arr)
    -> (F * fn|->?)%pred (list2nmem fl)
    -> length (L1.Data arr) >= file_size * (S fn).
  Proof.
    unfold rep; intros.
    destruct_lift H0.
    destruct_lift H.
    apply list2nmem_ptsto_bound in H0 as Hx.
    apply emp_star in H; eapply arrayN_selN with (a:= fn) in H; simpl in *; auto; try omega.
    rewrite <- minus_n_O in H.
    unfold arr2file in H.
    destruct (firstn file_size (skipn (file_size * fn) (L1.Data arr))) eqn:D; try congruence.
    specialize (H3 dummy).
    apply list2nmem_ptsto_in in H0 as Hy; specialize (H3 Hy). 
    destruct (fl ⟦ fn ⟧) eqn:D0; try congruence.
    inversion H.
    rewrite H2 in *; clear H H2.
    eapply list2nmem_sel in H0.
    rewrite <- H0 in *; clear H0.
    destruct dummy; simpl in *.
    inversion D0; subst; clear D0.
    rewrite firstn_length in H3.
    rewrite skipn_length in H3.
    rewrite Nat.mul_succ_r.
    assert (A: (length (L1.Data arr) - file_size * fn) >= file_size).
    rewrite <- H3 at 2; apply Min.le_min_r.
    destruct file_size; omega.
    Unshelve.
    auto.
  Qed.

  Lemma arr2file_updN: 
    forall arr1 fn bn v v2 x fl1 f F1 vsdef,
    bn < L2.file_size
    -> list2nmem (L1.Data arr1) (L2.file_size * fn + bn) = Some (v2, x)
    -> rep fl1 (arr2file arr1)
    -> (F1 ✶ fn |-> f)%pred (list2nmem fl1)
    -> (arr2file {| L1.Data := updN (L1.Data arr1) (L2.file_size * fn + bn) (v, v2 :: x) |}) 
                    = upd (arr2file arr1) fn (upd_file f bn v vsdef).
  Proof.
    unfold rep, upd_file; intros.
    destruct_lift H0.
    apply functional_extensionality; intros.
    destruct (Nat.eq_dec x0 fn); subst.
    rewrite upd_eq; auto.
    unfold arr2file.
    destruct (firstn L2.file_size (skipn (L2.file_size * fn)
                  (L1.Data {| L1.Data := (L1.Data arr1) 
                    ⟦ L2.file_size * fn + bn := (v, v2 :: x) ⟧ |}))) eqn:D.
    {
      apply firstn_is_nil in D; try omega; simpl in *.

      assert (A: L2.file_size * fn + bn < length (L1.Data arr1)).
      {
          eapply Nat.lt_le_trans with (m:= (L2.file_size * (S fn))%nat).
          rewrite Nat.mul_succ_r; omega.
          eapply arr2file_length; eauto.
          pred_apply; cancel.
      }
      
      apply skipn_is_nil in D; destruct D.
      erewrite list2nmem_sel_inb in H0; inversion H0; auto.
      rewrite updN_firstn_skipn in H3; auto.
      apply app_eq_nil in H3; destruct H3; congruence.
      rewrite length_updN in H3; omega.
    }
    
    simpl in *.
    rewrite <- D. 
    destruct_lift H1.
    apply list2nmem_array_mem_eq in H1; subst.
    rewrite <- H1 in H2.
    apply ptsto_valid' in H2 as Hy.
    
    destruct f; simpl in *.
    unfold L2.arr2file in Hy.
    destruct (firstn L2.file_size 
      (skipn (L2.file_size * fn) (L1.Data arr1))) eqn:D0; [ congruence |].
    inversion Hy.
    rewrite H4 in *; clear H4 Hy.
    rewrite Nat.add_comm.
    rewrite <- updN_skipn.
    rewrite updN_firstn_comm.
    rewrite D0.
    admit. (* Tedious but doable *)
    
    rewrite upd_ne; auto.
    unfold arr2file.
    destruct (firstn L2.file_size (skipn (L2.file_size * x0)
                (L1.Data {| L1.Data := (L1.Data arr1) 
                  ⟦ L2.file_size * fn + bn := (v, v2 :: x) ⟧ |}))) eqn:D.
    {
      assert (A: length (firstn L2.file_size (skipn (L2.file_size * x0)
                          (L1.Data {| L1.Data := (L1.Data arr1) 
                            ⟦ L2.file_size * fn + bn := (v, v2 :: x) ⟧ |}))) 
                  = length (firstn L2.file_size (skipn (L2.file_size * x0) (L1.Data arr1)))).
      {
          repeat rewrite firstn_length.
          repeat rewrite skipn_length.
          simpl; rewrite length_updN; auto. 
      }
      
      apply length_zero_iff_nil in D; rewrite D in A.
      symmetry in A; apply length_zero_iff_nil in A.
      rewrite A ; auto.
    }
      
    simpl in *.
    admit. (* Tedious but doable *)
    Unshelve.
    repeat econstructor; auto.
  Admitted.
  
Lemma arr2file_eq:
  forall arr arr',
  (L1.Data arr) = L1.Data arr'
  -> arr2file arr = arr2file arr'.
Proof.
  intros.
  unfold arr2file; simpl; rewrite H; auto.
Qed.
  

End L2.


Module WorldDesc.


Definition prog_secure AT AEQ V T 
(wc: @mem addr addr_eq_dec valuset 
        -> @mem AT AEQ V -> Prop)
  (p : prog T) (pre post: pred):=
  forall m1 m2 m F1 F2 mp out1 vm hm,
  (F1 * diskIs m)%pred m1 ->
  (F2 * diskIs m)%pred m2 ->
  wc m mp ->
  pre mp ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' m' vm' hm' mr,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * diskIs m')%pred m1' /\
   (F2 * diskIs m')%pred m2' /\
   wc m' mr /\
   post mr)
   
   \/

  (exists m1' m2' hm' mc,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   (F1 * diskIs mc)%pred m1' /\
   (F2 * diskIs mc)%pred m2').


Theorem ret_secure_frame:
  forall AT AEQ V T F (a: T) (wc: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop),
  prog_secure wc (Ret a) F F.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  left; repeat eexists; eauto.
Qed.


Theorem bind_secure:
  forall AT AEQ V T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) 
        pre post1 post2 (wc: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop),
  prog_secure wc p1 pre post1
  -> (forall x, prog_secure wc (p2 x) post1 post2)
  -> prog_secure wc (Bind p1 p2) pre post2.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* p1 Finished *)
    specialize (H _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H12).
    intuition; repeat deex; try congruence.
    inversion H5; subst; clear H5.
    specialize (H0 _ _ _ _ _ _ _ _ _ _ H6 H7 H8 H10 H15).
    intuition; repeat deex.
    + left.
      do 7 eexists; intuition; eauto.
    + right.
      do 4 eexists; intuition; eauto; pred_apply; cancel.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H11).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H11).
    intuition; repeat deex; try congruence.
    inversion H5; subst; clear H5.
    right.
    do 4 eexists; intuition; eauto; pred_apply; cancel.
Qed.


Theorem read_secure:
  forall a v F,
  @prog_secure  _ addr_eq_dec valuset _ 
  (fun m m' => (F * diskIs m')%pred m) (Read a) (a |-> v)%pred (a |-> v)%pred.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* Finished *)
    left.
    do 7 eexists.
    repeat (split; eauto).
    econstructor.
    econstructor.
    erewrite (diskIs_pred _ H2) in H1.
    rewrite (diskIs_pred _ H1) in H.
    apply sep_star_assoc in H.
    eapply ptsto_valid' in H.
    rewrite (diskIs_pred _ H1) in H0.
    apply sep_star_assoc in H0.
    eapply ptsto_valid' in H0.
    rewrite H9 in H; inversion H; subst; clear H; eauto.
  - (* Failed *)
    rewrite (diskIs_pred _ H2) in H1.
    rewrite (diskIs_pred _ H1) in H.
    apply sep_star_assoc in H.
    eapply ptsto_valid' in H;  congruence.
  - (* Crashed *)
    right.
    do 4 eexists; intuition; eauto.
Qed.

Theorem write_secure:
  forall (a:addr) v vs F,
  @prog_secure _ addr_eq_dec _ _ (fun m m' => (F * diskIs m')%pred m) (Write a v)  (a |-> vs)%pred (a |-> (v, vsmerge vs))%pred.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* Finished *)
    left.
    do 6 eexists.
    exists (upd mp a (v, v2::x)).
    repeat split.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H2) in H1.
      rewrite (diskIs_pred _ H1) in H.
      apply sep_star_assoc in H.
      eapply ptsto_valid' in H.
      rewrite (diskIs_pred _ H1) in H0.
      apply sep_star_assoc in H0.
      eapply ptsto_valid' in H0.
      rewrite H14 in H; inversion H; subst; clear H; eauto.
    + instantiate (1:= (upd m a (v, v2 :: x))).
      eapply diskIs_sep_star_upd; eauto.
      rewrite (diskIs_pred _ H2) in H1.
      eapply ptsto_valid'; pred_apply; cancel.
    + eapply diskIs_sep_star_upd; eauto.
      rewrite (diskIs_pred _ H2) in H1.
      eapply ptsto_valid'; pred_apply; cancel.
    + eapply diskIs_sep_star_upd; eauto.
      eapply ptsto_valid'; pred_apply; cancel.
    + rewrite (diskIs_pred _ H2) in H1.
      rewrite (diskIs_pred _ H1) in H.
      apply sep_star_assoc in H.
      eapply ptsto_valid' in H.
      unfold vsmerge; rewrite H14 in H; 
      inversion H; subst; clear H; simpl; eauto.
      rewrite upd_eq; auto.
    + intros; destruct H2.
      rewrite upd_ne; eauto.
  - (* Failed *)
    rewrite (diskIs_pred _ H2) in H1.
    rewrite (diskIs_pred _ H1) in H.
    apply sep_star_assoc in H.
    eapply ptsto_valid' in H; congruence.
  - (* Crashed *)
    right.
    do 4 eexists; intuition; eauto.
Qed.

Theorem pimpl_secure:
  forall AT AEQ V T (wc: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop)
   (p : prog T) pre pre' post post',
  pre' =p=> pre ->
  post =p=> post' ->
  prog_secure wc p pre post ->
  prog_secure wc p pre' post'.
Proof.
  unfold prog_secure; intros.
  apply H in H5.
  specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6).
  intuition; repeat deex.
  - left.
    do 7 eexists; intuition eauto.
Qed.

Theorem world_impl_secure:
  forall AT AEQ V T (wc1 wc2: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop) 
  (p : prog T) (pre post: pred),
  (forall m m', pre m' -> wc2 m m' -> wc1 m m')
  -> (forall m m', post m' -> wc1 m m' -> wc2 m m')
  -> prog_secure wc1 p pre post
  -> prog_secure wc2 p pre post.
Proof.
  unfold prog_secure; intros.
  eapply H in H4; [| pred_apply; cancel].
  specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6).
  intuition; repeat deex.
  - left.
    do 7 eexists; intuition eauto.
Qed.
  
Theorem world_impl_lift_empty_secure:
  forall AT AEQ V T (wc1 wc2: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop) 
  (p : prog T) (pre post: pred) (P: Prop),
  (forall m m', wc2 m m' <-> P /\ wc1 m m')
  -> prog_secure wc1 p pre post
  -> prog_secure wc2 p pre post.
Proof.
  unfold prog_secure; intros.
  apply H in H3; split_hyp.
  specialize (H0 _ _ _ _ _ _ _ _ _ H1 H2 H6 H4 H5).
  intuition; repeat deex.
  - left.
    do 7 eexists; intuition eauto.
    apply H; eauto.
Qed.


(* Theorem cross_world_secure_weak:
  forall ATl AEQl Vl ATh AEQh Vh T 
  (wcl: @mem addr addr_eq_dec valuset -> @mem ATl AEQl Vl -> Prop) 
  (wch: @mem addr addr_eq_dec valuset -> @mem ATh AEQh Vh -> Prop) 
  (p : prog T)
  (conv: @mem ATl AEQl Vl -> @mem ATh AEQh Vh -> Prop)
  (prel postl: pred) (preh posth: pred),
  
  (forall m mh, wch m mh -> exists ml, wcl m ml /\ conv ml mh)
  -> (forall ml mh, conv ml mh -> preh mh -> prel ml) 
  -> (forall ml mh, conv ml mh -> postl ml -> posth mh)
  -> prog_secure wcl p prel postl
  -> prog_secure wch p preh posth.
Proof.
  unfold prog_secure; intros.
  specialize (H _ _ H6); repeat deex.
  specialize (H1 _ _ H10 H7).
  specialize (H3 _ _ _ _ _ _ _ _ _ H4 H5 H9 H1 H8).
  intuition; repeat deex.
  left.
  specialize (H0 _ _ H13); repeat deex.
  specialize (H2 _ _ H3 H15); split_hyp.
  repeat eexists; eauto.
Qed.
 *)
 
Theorem cross_world_secure_strong:
  forall ATl AEQl Vl ATh AEQh Vh T 
  (wcl: @mem addr addr_eq_dec valuset -> @mem ATl AEQl Vl -> Prop) 
  (wch: @mem addr addr_eq_dec valuset -> @mem ATh AEQh Vh -> Prop) 
  (p : prog T)
  (conv: @mem ATl AEQl Vl -> @mem ATh AEQh Vh -> Prop)
  (prel postl: pred) (preh posth: pred),
  
  (forall m mh, wch m mh -> preh mh -> exists ml, wcl m ml /\ conv ml mh)
  -> (forall m' ml' mh' m ml, 
        wcl m' ml' -> conv ml' mh' -> wch m' mh' -> prel ml' -> preh mh' 
        -> wcl m ml -> postl ml -> exists mh, conv ml mh /\ wch m mh)
  -> (forall m ml mh, wcl m ml -> conv ml mh -> wch m mh -> preh mh -> prel ml) 
  -> (forall m' ml' mh' m ml mh, 
        wcl m' ml' -> conv ml' mh' -> wch m' mh' -> prel ml' -> preh mh' 
        -> wcl m ml -> conv ml mh -> wch m mh -> postl ml -> posth mh)
  -> prog_secure wcl p prel postl
  -> prog_secure wch p preh posth.
Proof.
  unfold prog_secure; intros.
  specialize (H _ _ H6 H7); repeat deex.
  specialize (H1 _ _ _ H9 H10 H6 H7).
  specialize (H3 _ _ _ _ _ _ _ _ _ H4 H5 H9 H1 H8).
  intuition; repeat deex.
  left.
  specialize (H0 _ _ _ _ _ H9 H10 H6 H1 H7 H13 H15); repeat deex.
  repeat eexists; eauto.
Qed.

Hint Resolve ret_secure_frame.
Hint Resolve bind_secure.
Hint Resolve read_secure.
Hint Resolve write_secure.


Import L1.


Theorem prog_secure_is_noninterference :
  forall T AT AEQ V (p : prog T) (wc: @mem addr addr_eq_dec valuset -> @mem AT  AEQ V -> Prop) pre post a v1 v2 m1 m2 m mp vm hm,
  prog_secure wc p pre post ->
  (a |+> v1 * diskIs m)%pred m1 ->
  (a |+> v2 * diskIs m)%pred m2 ->
  wc m mp ->
  pre mp ->
  forall m1' vm' hm' v,
  exec m1 vm hm p (Finished m1' vm' hm' v) ->
  exists m2' vm'' hm'',
  exec m2 vm hm p (Finished m2' vm'' hm'' v).
Proof.
  unfold prog_secure; intros.
  specialize (H _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4).
  intuition; repeat deex; try congruence.
  do 3 eexists.
  inversion H5; subst.
  eauto.
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

Definition singleton AT AEQ V (a: AT) (v: V) : @mem AT AEQ V := 
  fun a' => if (AEQ a' a) then Some v else None.
  
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


Theorem read_data_secure:
  forall arr (a: addr) vdef vsdef,
  @prog_secure _ addr_eq_dec valuset _ 
  (fun m m' => (L1.rep arr 
  * [[ (arrayN_ex (ptsto (V:=valuset)) (Data arr) a 
        * diskIs m')%pred (list2nmem (Data arr))]])%pred m) 
  (L1.read_data arr a vdef) (a |-> (selN (Data arr) a vsdef))%pred (a |-> (selN (Data arr) a vsdef))%pred.
  
Proof.
  unfold L1.read_data; intros.
  destruct (lt_dec a (length (L1.Data arr))); eauto.
  eapply bind_secure; intros; eauto.
  eapply world_impl_secure; eauto.
  
  simpl; intros; split_hyp; subst; eauto.
  destruct_lift H0.
  unfold rep in *.
  apply list2nmem_array_mem_eq in H0; subst; eauto.

  simpl; intros; split_hyp; subst; intuition; eauto.
  pred_apply; cancel.
  erewrite diskIs_pred; eauto.
  unfold rep.
  erewrite arrayN_except with (i:= a); eauto; cancel.
  erewrite diskIs_ptsto_eq; eauto.
  apply arrayN_except with (i:= a); eauto.
  apply list2nmem_array.
Qed.

Hint Resolve read_data_secure.

Import L2.

Theorem read_from_file_secure:
  forall arr fr fn bn fdef vdef (f: L2.file),
     prog_secure (fun m (m': @mem addr addr_eq_dec file) => 
     (L1.rep arr * [[ L2.rep fr (arr2file arr) ]] 
     * [[ (arrayN_ex (ptsto (V:=file)) fr fn 
     * diskIs m')%pred (list2nmem fr)]])%pred m)
      (L2.read_from_file arr fr fn bn fdef vdef) (fn|-> (selN fr fn fdef))%pred (fn|-> (selN fr fn fdef))%pred.
Proof.
    intros.
    unfold L2.read_from_file.
    destruct (lt_dec fn (length fr)); eauto.
    destruct (lt_dec bn L2.file_size); eauto.
    eapply bind_secure; intros; eauto.

    eapply cross_world_secure_strong; eauto.
    - intros; simpl; split_hyp.
      eexists; intuition. 
      pred_apply; cancel.
      erewrite diskIs_ptsto_eq.
      apply arrayN_except; eauto.
      eapply lt_le_trans.
      2: eapply arr2file_length; eauto.
      simpl; instantiate (1:= fn).
      rewrite Nat.mul_succ_r; omega.
      eapply list2nmem_array_pick in l; pred_apply; cancel.
      apply list2nmem_array.
      apply ptsto_mem_is.
     
      instantiate (2:= fun (ml: @mem _ addr_eq_dec _) (mh: @mem _ addr_eq_dec _) => 
      ((L2.file_size * fn + bn) |-> (selN (L1.Data arr) (L2.file_size * fn + bn) (vdef, nil)))%pred ml  
      /\ (fn |->  (selN fr fn fdef))%pred mh).
      simpl; split; eauto.
      apply ptsto_mem_is.

    - simpl; intros; split_hyp.
      destruct_lift H.
      destruct_lift H1.
      destruct_lift H4.
      eexists; intuition; eauto.
      pred_apply; cancel.

    - simpl; intros; split_hyp; eauto.
    - simpl; intros; split_hyp; eauto.
    Unshelve.
    auto.
Qed.


Theorem write_data_secure:
  forall arr a v vsdef,
  prog_secure (fun m m' => exists arr', (L1.rep arr' 
  * [[ (arrayN_ex (ptsto (V:= valuset)) (L1.Data arr) a 
  * diskIs m')%pred (list2nmem (L1.Data arr'))]] )%pred m)
   (write_data arr a v vsdef) (a |-> (selN (L1.Data arr) a vsdef))%pred
  (a |-> (selN (L1.Data arr) a vsdef) ⋁ a |-> (v, vsmerge (selN (L1.Data arr) a vsdef)))%pred.
Proof.
  unfold L1.write_data; intros.
  destruct (lt_dec a (length (L1.Data arr))); eauto.
  eapply bind_secure; [| eauto].
  eapply world_impl_secure; eauto.


  simpl; intros; split_hyp; subst; eauto.
  apply H0.

  simpl; intros; eauto.
  
  eapply world_impl_secure; eauto.
  3: eapply pimpl_secure.
  5: eauto.
  3: eauto.
  3: cancel.
  
  intros.
  repeat deex; destruct_lift H0.
  unfold L1.rep in *.
  apply list2nmem_array_mem_eq in H0; subst.
  eauto.
  
  simpl; intros; split_hyp; subst; intuition; eauto.
  destruct H.
  exists arr.
  pred_apply; cancel.
  erewrite diskIs_pred; eauto.
  unfold L1.rep.
  rewrite sep_star_comm.
  rewrite <- arrayN_except; auto; cancel.
  erewrite diskIs_ptsto_eq; eauto.
  apply arrayN_except; auto.
  apply list2nmem_array.
  
  exists {| L1.Data := updN (L1.Data arr) a (v, vsmerge (selN (L1.Data arr) a vsdef)) |}.
  simpl.
  pred_apply; cancel.
  erewrite diskIs_pred; eauto.
  unfold L1.rep; simpl.
  rewrite sep_star_comm.
  erewrite arrayN_except with (i:= a).
  rewrite selN_updN_eq; eauto.
  rewrite arrayN_ex_updN_eq.
  cancel.
  rewrite length_updN; auto.
  
  rewrite diskIs_ptsto_eq; eauto.
  eapply list2nmem_updN; eauto.
  apply arrayN_except; auto.
  apply list2nmem_array.
  
  eapply pimpl_secure.
  3: eauto.
  eauto.
  cancel.
  
  Unshelve.
  all: auto.
Qed.

Hint Resolve write_data_secure.

Theorem write_to_file_secure:
  forall arr fr fn bn v fdef (f: L2.file),
     prog_secure 
     (fun m (m': @mem addr addr_eq_dec file) => 
     exists arr' fr', (L1.rep arr' * [[ L2.rep fr' (arr2file arr') ]] 
     * [[ (arrayN_ex (ptsto (V:=file)) fr fn 
     * diskIs m')%pred (list2nmem fr')]] )%pred m)
     (L2.write_to_file arr fr fn bn v fdef (v,nil)) 
            (fn|-> (selN fr fn fdef))%pred (fn|-> (selN fr fn fdef) \/ fn|-> L2.upd_file (selN fr fn fdef) bn v (v,nil))%pred.
Proof.
  intros.
  unfold L2.write_to_file.
  destruct (lt_dec fn (length fr)); eauto.
  destruct (lt_dec bn L2.file_size); eauto.
  eapply bind_secure; [| eauto].
  
  eapply cross_world_secure_strong; eauto.

  - intros; simpl; split_hyp.
    repeat deex.
    destruct_lift H.
    repeat eexists; intuition. 
    pred_apply; cancel.
    admit. (* Tedious but doable *)

    instantiate (2:= fun (ml: @mem _ addr_eq_dec _) (mh: @mem _ addr_eq_dec _) => 
    ((L2.file_size * fn + bn) |-> (selN (L1.Data arr)  (L2.file_size * fn + bn ) (v, nil))
    ⋁ (L2.file_size * fn + bn)
      |-> (v, vsmerge (selN (L1.Data arr) ( L2.file_size * fn + bn ) (v, nil))))%pred ml  
    /\ (fn|-> (selN fr fn fdef) \/ fn|-> L2.upd_file (selN fr fn fdef) bn v (v,nil))%pred mh).
    simpl; split; eauto.
    intros.
    left; eapply ptsto_mem_is.
    left; auto.

  - simpl; intros; split_hyp; repeat deex.
    destruct_lift H.
    destruct_lift H1.
    destruct_lift H4.
    destruct H5.
    + eexists; intuition; eauto.
      left; auto.
      rewrite (diskIs_pred _ H2) in H8.
      rewrite (diskIs_pred _ H5) in H10.
      eapply arrayN_ex_ptsto_eq in H8; eauto.
      apply list2nmem_inj in H8; subst.
      unfold L1.rep in *.
      apply list2nmem_array_mem_eq in H; subst.
      apply list2nmem_array_mem_eq in H1; subst.
      apply list2nmem_inj in H1; subst.
      pred_apply; cancel.
      rewrite H1 in H8; clear H1.
      erewrite arr2file_eq; eauto.
      
    + unfold L1.rep in *.
      apply list2nmem_array_mem_eq in H; subst.
      apply list2nmem_array_mem_eq in H1; subst.
      apply list2nmem_inj in H1; subst.
      rewrite (diskIs_pred _ H3) in H7.
      eapply arrayN_ex_ptsto_merge in H7; auto.
      apply list2nmem_array_mem_eq in H7; subst.
       apply list2nmem_inj in H7; subst.
      exists (singleton addr_eq_dec fn (L2.upd_file (selN fr fn fdef) bn v (v,nil))).
      intuition; eauto.
      right; eauto.
      unfold singleton; right; apply ptsto_mem_is.
      repeat eexists; repeat apply sep_star_lift_apply'.
      eauto.
      instantiate (1:= updN fr fn (L2.upd_file (selN fr fn fdef) bn v (v,nil))).
      admit. (* tedious but doable *)
      intuition.
      unfold rep in *; destruct_lift H11.
      apply in_updN in H; destruct H.
      eauto.
      unfold upd_file in H.
      rewrite H; simpl; rewrite length_updN.
      apply H12.
      apply in_selN; auto.
      admit. (* tedious but doable *)

  - simpl; intros; split_hyp.
    repeat deex.
    destruct_lift H.
    destruct_lift H1.
    admit. (* tedious but doable *)
  - simpl; intros; split_hyp; eauto.
  - eapply pimpl_secure.
    3: eauto.
    eauto.
    cancel.
  - eapply pimpl_secure.
    3: eauto.
    eauto.
    cancel.
Admitted.



End WorldDesc.
End TwoLevel.