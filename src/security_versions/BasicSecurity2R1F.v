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
  
  
  

End L2.











Module WorldDesc.


Definition prog_secure AT AEQ V T (wc: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop)
  (p : prog T) (pre post: pred):=
  forall m1 m2 m F F1 F2 mp out1 vm hm,
  (F1 * diskIs m)%pred m1 ->
  (F2 * diskIs m)%pred m2 ->
  wc m mp ->
  (F * pre)%pred mp ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' m' vm' hm' mr,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * diskIs m')%pred m1' /\
   (F2 * diskIs m')%pred m2' /\
   wc m' mr /\
   (F * post)%pred mr)
   
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
    specialize (H _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H12).
    intuition; repeat deex; try congruence.
    inversion H5; subst; clear H5.
    specialize (H0 _ _ _ _ _ _ _ _ _ _ _ H6 H7 H8 H10 H15).
    intuition; repeat deex.
    + left.
      do 7 eexists; intuition; eauto.
    + right.
      do 4 eexists; intuition; eauto; pred_apply; cancel.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H11).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H11).
    intuition; repeat deex; try congruence.
    inversion H5; subst; clear H5.
    right.
    do 4 eexists; intuition; eauto; pred_apply; cancel.
Qed.


Theorem read_secure:
  forall a v,
  @prog_secure  _ addr_eq_dec valuset _ diskIs (Read a) (a |-> v)%pred (a |-> v)%pred.
Proof.
  unfold prog_secure; intros.
  inversion H1; subst; clear H1.
  inv_exec.
  - (* Finished *)
    left.
    do 7 eexists.
    repeat (split; eauto).
    econstructor.
    econstructor.
    rewrite (diskIs_pred _ H2) in H.
    rewrite (diskIs_pred _ H2) in H0.
    apply sep_star_assoc in H0.
    apply sep_star_assoc in H.
    eapply ptsto_valid' in H0.
    eapply ptsto_valid' in H.
    rewrite H8 in H; inversion H; subst; clear H; eauto.
  - (* Failed *)
    exfalso.
    rewrite (diskIs_pred _ H2) in H.
    apply sep_star_assoc in H.
    destruct_lift H.
    inversion H9.
    eapply ptsto_valid' in H;  congruence.
  - (* Crashed *)
    right.
    do 4 eexists; intuition; eauto.
Qed.


Theorem write_secure:
  forall (a:addr) v vs,
  @prog_secure _ addr_eq_dec _ _ diskIs (Write a v)  (a |-> vs)%pred (a |-> (v, vsmerge vs))%pred.
Proof.
  unfold prog_secure; intros.
  inversion H1; subst; clear H1.
  inv_exec.
  - (* Finished *)
    left.
    do 6 eexists.
    exists (upd mp a (v, v2::x)).
    repeat split.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H2) in H.
      rewrite (diskIs_pred _ H2) in H0.
      apply sep_star_assoc in H.
      apply sep_star_assoc in H0.
      eapply ptsto_valid' in H.
      eapply ptsto_valid' in H0.
      rewrite H13 in H; inversion H; subst; clear H; eauto.
    +  eapply diskIs_sep_star_upd; eauto.
       eapply ptsto_valid'; pred_apply; cancel.
    +  eapply diskIs_sep_star_upd; eauto.
       eapply ptsto_valid'; pred_apply; cancel.
    + rewrite (diskIs_pred _ H2) in H.
      apply sep_star_assoc in H.
      eapply ptsto_valid' in H.
      rewrite H13 in H; inversion H; subst; clear H.
      unfold vsmerge; simpl.
      eapply ptsto_upd'; eauto.
  - (* Failed *)
    exfalso.
    rewrite (diskIs_pred _ H2) in H.
    destruct_lift H.
    eapply ptsto_valid' in H; congruence.
  - (* Crashed *)
    right.
    do 4 eexists; auto.
    repeat (split; eauto).
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
  rewrite H in H5.
  specialize (H1 _ _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6).
  intuition; repeat deex.
  - left.
    do 7 eexists; intuition eauto.
    rewrite <- H0; eauto.
Qed.

Theorem world_impl_secure:
  forall AT AEQ V T (wc1 wc2: @mem addr addr_eq_dec valuset -> @mem AT AEQ V -> Prop) 
  (p : prog T) (pre post: pred),
  (forall m m' F, (F * pre)%pred m' -> wc2 m m' -> wc1 m m')
  -> (forall m m' F, (F * post)%pred m' -> wc1 m m' -> wc2 m m')
  -> prog_secure wc1 p pre post
  -> prog_secure wc2 p pre post.
Proof.
  unfold prog_secure; intros.
  eapply H in H4; [| pred_apply; cancel].
  specialize (H1 _ _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6).
  intuition; repeat deex.
  - left.
    do 7 eexists; intuition eauto.
Qed.
  



Theorem cross_world_secure:
  forall ATl AEQl Vl ATh AEQh Vh T 
  (wl: @mem addr addr_eq_dec valuset -> @mem ATl AEQl Vl -> Prop) 
  (wh: @mem addr addr_eq_dec valuset -> @mem ATh AEQh Vh -> Prop) 
  (p : prog T)
  (conv: @mem ATl AEQl Vl -> @mem ATh AEQh Vh -> Prop)
  (prel postl: pred) (preh posth: pred),
  
  (forall m mh, wh m mh -> exists ml, wl m ml /\ conv ml mh)
  -> (forall m ml, wl m ml -> exists mh, conv ml mh /\ wh m mh)
  -> (forall ml mh F, conv ml mh -> 
      ((F * preh)%pred mh -> exists F', (F' * prel)%pred ml) /\
      (forall F', (F' * postl)%pred ml -> (F * posth)%pred mh))
  -> prog_secure wl p prel postl
  -> prog_secure wh p preh posth.
Proof.
  unfold prog_secure; intros.
  specialize (H _ _ H5); repeat deex.
  specialize (H1 _ _ F H9) as Hx; split_hyp.
  specialize (H H6); deex.
  specialize (H2 _ _ _ _ _ _ _ _ _ _ H3 H4 H8 H H7).
  intuition; repeat deex.
  left.
  specialize (H0 _ _ H14); repeat deex.
  specialize (H1 _ _ F H11); split_hyp.
  repeat eexists; eauto.
Qed.


Hint Resolve ret_secure_frame.
Hint Resolve bind_secure.
Hint Resolve read_secure.
(* Hint Resolve read_secure_eq.
Hint Resolve write_secure.
Hint Resolve world_frame_secure.
Hint Resolve world_frame_secure_lift_empty. *)

Import L1.


Definition mem_diff AT AEQ V (m1 m2: @mem AT AEQ V) :=
  fun a => if m2 a then None else m1 a.
  
  
Lemma list2nmem_mem_diff_diskIs:
  forall A (l: list A) m a def,
  a < length l
  -> (a |-> (selN l a def))%pred m
  -> (diskIs (mem_diff (list2nmem l) m) * diskIs m)%pred (list2nmem l).
Proof.
  intros.
  unfold_sep_star; repeat eexists; eauto.
  extensionality x.
  unfold mem_union, mem_diff.
  destruct (m x) eqn:D.
  destruct H0.
  destruct (addr_eq_dec a x); subst.
  rewrite <- D; rewrite H0; apply list2nmem_sel_inb; auto.
  apply H1 in n; congruence.
  destruct (list2nmem l x); auto.
  unfold mem_disjoint, mem_diff.
  unfold not; intros; repeat deex.
  destruct (m a0); congruence.
Qed.

Definition singleton AT AEQ V (a: AT) (v: V) : @mem AT AEQ V := 
  fun a' => if (AEQ a' a) then Some v else None.

Theorem read_data_secure:
  forall arr (a: addr) v vdef,
  @prog_secure _ addr_eq_dec valuset _ 
  diskIs (L1.read_data arr a vdef) (a |-> v)%pred (a |-> v)%pred.
Proof.
  unfold L1.read_data; intros.
  destruct (lt_dec a (length (L1.Data arr))); eauto.
(*   eapply bind_secure; eauto.
  eapply world_impl_secure; eauto.

  intros; split_hyp; subst; eauto.
  intros; split_hyp; subst; eauto.
  unfold rep in H; destruct H; subst.
  unfold singleton in H0.
  destruct H0.
  destruct (addr_eq_dec a a); try omega.
  inversion H0.
  eapply isolateN_fwd with (i:= a) in H; auto; simpl in *.
  pred_apply; cancel. *)
Qed.  

Hint Resolve read_data_secure.

Import L2.




Theorem read_from_file_secure':
  forall arr fr fn bn fdef vsdef (f: L2.file),
     prog_secure (fun m (m': @mem addr addr_eq_dec file) => (L1.rep arr * [[ L2.rep fr (arr2file arr)]])%pred m /\ m' = (list2nmem fr))
      (L2.read_from_file arr fr fn bn fdef vsdef) (fn|-> f)%pred (fn|-> f)%pred.
Proof.
    intros.
    unfold L2.read_from_file.
    destruct (lt_dec fn (length fr)); eauto.
    destruct (lt_dec bn L2.file_size); eauto.
    eapply bind_secure; eauto.
    eapply cross_world_secure; eauto.
    
    intros; simpl; split_hyp.
    eexists; intuition.
    instantiate (1:=(fun m (m': @mem addr addr_eq_dec file) => (L1.rep arr * [[ L2.rep fr (arr2file arr)]])%pred m /\ m' = (list2nmem fr))).
    simpl; eauto.
    
    simpl; intros.
    destruct H.
    intuition; eauto.
    
    simpl; intros.
    destruct H.
    intuition; eauto.
    rewrite H1; unfold singleton.
    apply ptsto_mem_is.
    
    simpl; intros.
    destruct H.
    rewrite H; unfold singleton.
    apply ptsto_mem_is.
Qed.

Theorem write_data_secure':
  forall arr fn bn a v vs vsdef,
  prog_secure (fun m m' => L1.rep arr m /\ m' = singleton addr_eq_dec a (selN (L1.Data arr) a vsdef))
   (write_data arr (L2.file_size * fn + bn) v vsdef) (a |-> vs)%pred
  (a |-> vs ⋁ a |-> (v, vsmerge vs))%pred.
Proof.
  unfold L1.write_data; intros.
  destruct (lt_dec (L2.file_size * fn + bn) (length (L1.Data arr))); eauto.
  eapply bind_secure; [| eauto].
  
  
  unfold prog_secure', L1.rep; intros.
  inv_exec.
  - left; repeat eexists; eauto.
    destruct_lift H1.
    pose proof H5 as Ha.
    unfold rep in H5; destruct_lift H5.
    apply list2nmem_ptsto_in in H2 as Hx; apply H6 in Hx.
    apply list2nmem_array_mem_eq in H1; subst.
    apply list2nmem_array_mem_eq in H3; subst.
    
    rewrite <- H3 in H2.
    apply ptsto_valid' in H2 as Hy.
    
    destruct_lift H0.
    pose proof H7 as Hb.
    unfold rep in H7; destruct_lift H7.
    apply list2nmem_array_mem_eq in H0; subst.
    apply list2nmem_array_mem_eq in H4; subst.
    rewrite <- H4 in H1.
    apply ptsto_valid' in H1 as Hz.
    
    unfold L2.arr2file in Hz.
    destruct (firstn L2.file_size (skipn (L2.file_size * fn) (L1.Data arr1))) eqn:D; [ congruence |].
    destruct f; inversion Hz.
    rewrite H5 in *; clear H5 Hz.
    unfold L2.arr2file in Hy.
    destruct (firstn L2.file_size (skipn (L2.file_size * fn) (L1.Data arr2))) eqn:D0; [ congruence |].
    inversion Hy.
    rewrite H5 in *; clear H5 Hy.
    
    
    assert (A: forall def, selN (firstn L2.file_size (skipn (L2.file_size * fn) (L1.Data arr1))) bn def = selN (L1.Data arr1) (L2.file_size * fn + bn) def).
    {
      intros.
      rewrite <- skipn_firstn_comm.
      erewrite selN_skip_first; eauto.
      omega.
    }
 
    assert (A0: forall def, selN (firstn L2.file_size (skipn (L2.file_size * fn) (L1.Data arr2))) bn def = selN (L1.Data arr2) (L2.file_size * fn + bn) def).
    {
      intros.
      rewrite <- skipn_firstn_comm.
      erewrite selN_skip_first; eauto.
      omega.
    }
    
    erewrite list2nmem_sel_inb in H13; auto.
    inversion H13.
    
    repeat econstructor.
    erewrite list2nmem_sel_inb; eauto.
    rewrite <- A0; rewrite D0; rewrite <- D; rewrite A; eauto.
    eapply Nat.lt_le_trans with (m:= L2.file_size * (S fn)).
    rewrite Nat.mul_succ_r; omega.
    eapply arr2file_length; eauto.
    rewrite <- H3; clear Ha; pred_apply; cancel.
    
    eapply Nat.lt_le_trans with (m:= L2.file_size * (S fn)).
    rewrite Nat.mul_succ_r; omega.
    eapply arr2file_length; eauto.
    rewrite <- H4; clear Hb; pred_apply; cancel.
    
    {
      destruct_lift H0.
      apply list2nmem_array_mem_eq in H0; subst.
      rewrite <- listupd_memupd.
      repeat apply sep_star_lift_apply'.
      instantiate (1:= {| L1.Data := (L1.Data arr1) 
          ⟦ L2.file_size * fn + bn := (v, v2 :: x) ⟧ |}); simpl.
      apply list2nmem_array.
      instantiate (1:= updN fl1 fn (upd_file f bn v vsdef)).
      
      erewrite arr2file_updN; eauto.
      unfold rep in H5; destruct_lift H5.
      apply list2nmem_array_mem_eq in H0; rewrite H0.
      rewrite <- listupd_memupd.
      apply list2nmem_array.
      eapply list2nmem_ptsto_bound; eauto.
      unfold rep in H5; destruct_lift H5; intros.
      apply in_updN in H3; destruct H3; eauto.
      unfold upd_file in H3; subst; simpl.
      rewrite length_updN.
      apply H5.
      eapply list2nmem_ptsto_in; eauto.
      admit. (* Tedious but provable *)
      eapply Nat.lt_le_trans with (m:= L2.file_size * (S fn)).
      rewrite Nat.mul_succ_r; omega.
      eapply arr2file_length; eauto.
      pred_apply; cancel.
    }
    
    {
      destruct_lift H1.
      apply list2nmem_array_mem_eq in H1; subst.
      rewrite <- listupd_memupd.
      repeat apply sep_star_lift_apply'.
      instantiate (1:= {| L1.Data := (L1.Data arr2) 
          ⟦ L2.file_size * fn + bn := (v, v2 :: x) ⟧ |}); simpl.
      apply list2nmem_array.
      instantiate (1:= updN fl2 fn (upd_file f bn v vsdef)).
      
      erewrite arr2file_updN; eauto.
      unfold rep in H5; destruct_lift H5.
      apply list2nmem_array_mem_eq in H1; rewrite H1.
      rewrite <- listupd_memupd.
      apply list2nmem_array.
      eapply list2nmem_ptsto_bound; eauto.
      admit. (* Tedious but provable *)
      unfold rep in H5; destruct_lift H5; intros.
      apply in_updN in H3; destruct H3; eauto.
      unfold upd_file in H3; subst; simpl.
      rewrite length_updN.
      apply H5.
      eapply list2nmem_ptsto_in; eauto.
      admit. (* Tedious but provable *)
      eapply Nat.lt_le_trans with (m:= L2.file_size * (S fn)).
      rewrite Nat.mul_succ_r; omega.
      eapply arr2file_length; eauto.
      pred_apply; cancel.
    }

  - destruct_lift H0.
    apply emp_star in H0; eapply arrayN_selN with (a:= (L2.file_size * fn + bn)) in H0.
    congruence.
    apply le_0_n.
    simpl.
    
    eapply Nat.lt_le_trans with (m:= L2.file_size * (S fn)).
    rewrite Nat.mul_succ_r; omega.
    eapply arr2file_length; eauto.
    pred_apply; cancel.
  - right; repeat eexists; eauto.
  - eapply ret_secure'_impl.
    2: eauto.
    cancel.
    Unshelve.
    all: repeat constructor; eauto.
  Admitted.


Theorem write_to_file_secure':
  forall arr fr fn bn v fdef vsdef (f: L2.file),
     prog_secure' (L2.write_to_file arr fr fn bn v fdef vsdef) 
            (fn|-> f)%pred (fn|-> f \/ fn|-> L2.upd_file f bn v vsdef)%pred.
Proof.
  intros.
  unfold L2.write_to_file.
  destruct (lt_dec fn (length fr)); eauto.
  destruct (lt_dec bn L2.file_size); eauto.
  eapply bind_secure'; [| eauto].
  apply write_data_secure'; auto.
  eapply ret_secure'_impl.
  2: eauto.
  cancel.
  eapply ret_secure'_impl.
  2: eauto.
  cancel.
Qed.

End Nickolai.
End TwoLevel.