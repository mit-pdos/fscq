Require Export SecurityDef.
Require Export PredCrash.

Set Implicit Arguments.

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
  (forall m m', wc2 m m'-> pre m'-> wc1 m m')
  -> (forall m m' m1 m1', wc1 m1 m1'-> wc2 m1 m1'-> pre m1'-> wc1 m m'-> post m'-> wc2 m m')
  -> prog_secure wc1 p pre post
  -> prog_secure wc2 p pre post.
Proof.
  unfold prog_secure; intros.
  specialize (H _ _ H4 H5).
  specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H H5 H6).
  intuition; repeat deex.
  specialize (H0 _ _ _ _ H H4 H5 H10 H12).
  left; do 7 eexists; intuition; eauto.
Qed.

(*   
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
 *)
 
Theorem cross_world_secure:
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

Theorem read_secure_subset:
  forall a v F,
  @prog_secure  _ addr_eq_dec valuset _ 
  (fun m m' => (F * diskIs m')%pred m) (Read a) (a |+> v)%pred (a |+> v)%pred.
Proof.
  unfold prog_secure; intros.
  unfold ptsto_subset in *; simpl.
  destruct_lift H2.
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
    rewrite H10 in H; inversion H; subst; clear H; eauto.
    pred_apply; cancel.
  - (* Failed *)
    rewrite (diskIs_pred _ H2) in H1.
    rewrite (diskIs_pred _ H1) in H.
    apply sep_star_assoc in H.
    eapply ptsto_valid' in H;  congruence.
  - (* Crashed *)
    right.
    do 4 eexists; intuition; eauto.
Qed.


Theorem write_secure_subset:
  forall (a:addr) v vs F,
  @prog_secure _ addr_eq_dec _ _ (fun m m' => (F * diskIs m')%pred m) (Write a v)  (a |+> vs)%pred (a |+> (v, vsmerge vs))%pred.
Proof.
  unfold prog_secure; intros.
  unfold ptsto_subset in *; simpl.
  destruct_lift H2.
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
      rewrite H15 in H; inversion H. 
      instantiate (1:= x).
      instantiate (1:= v2).
      subst; clear H; eauto.
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
      unfold vsmerge; rewrite H15 in H; 
      inversion H; subst; clear H; simpl; eauto.
      exists (vs_cur :: dummy).
      apply sep_star_lift_apply'.
      Search upd ptsto.
      apply emp_star; eapply ptsto_upd'; pred_apply; cancel.
      unfold incl; simpl; intros; destruct H; auto.
  - (* Failed *)
    rewrite (diskIs_pred _ H2) in H1.
    rewrite (diskIs_pred _ H1) in H.
    apply sep_star_assoc in H.
    eapply ptsto_valid' in H; congruence.
  - (* Crashed *)
    right.
    do 4 eexists; intuition; eauto.
Qed.

Theorem write_secure_impl_subset:
  forall (a:addr) v vs wc,
  (forall vs', @prog_secure _ addr_eq_dec _ _ wc (Write a v)  (a |-> vs')%pred (a |-> (v, vsmerge vs'))%pred) ->
  @prog_secure _ addr_eq_dec _ _ wc (Write a v)  (a |+> vs)%pred (a |+> (v, vsmerge vs))%pred.
Proof.
  unfold prog_secure in *; intros.
  unfold ptsto_subset in H3; destruct_lift H3.
  specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4).
  intuition; repeat deex.
  left.
  simpl; repeat eexists; eauto.
  simpl.
  pred_apply; cancel.
  unfold vsmerge; unfold incl; simpl; intros.
  destruct H5; eauto.
Qed.


Hint Resolve ret_secure_frame.
Hint Resolve bind_secure.
Hint Resolve read_secure.
Hint Resolve read_secure_subset.
Hint Resolve write_secure.
Hint Resolve write_secure_subset.
