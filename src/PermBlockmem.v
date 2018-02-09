Require Import Mem Pred List ListUtils Omega.
Require Import MapUtils.
Require Import FMapFacts.

Require Export PermProg.


Definition block_mem_subset (bm' bm: block_mem) :=
  forall h, (bm h = None -> bm' h = None) /\ (forall b, bm' h = Some b -> bm h = Some b).

Infix "c=" := block_mem_subset (at level 1, left associativity).

Lemma block_mem_subset_refl:
  forall bm, bm c= bm.
Proof.
  unfold block_mem_subset; intuition eauto.
Qed.

Lemma block_mem_subset_trans:
  forall bm bm' bm'',
    bm c= bm' ->
    bm' c= bm'' ->
    bm c= bm''.
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h); destruct H0;
  specialize (H h); destruct H; eauto.
Qed.

Lemma block_mem_subset_upd_none:
  forall bm bm' h v,
    bm h = None ->
    bm' c= bm ->
    bm' c= (upd bm h v).
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h0); destruct H0.
  destruct (handle_eq_dec h h0); subst; auto.
  rewrite upd_ne in H1; eauto.
  destruct (handle_eq_dec h h0); subst; auto.
  specialize (H0 H); congruence.
  rewrite upd_ne; eauto.
Qed.

Lemma block_mem_subset_upd_nop:
  forall bm bm' h v,
    bm h = Some v ->
    bm' c= bm ->
    bm' c= (upd bm h v).
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h0); destruct H0.
  destruct (handle_eq_dec h h0); subst; auto.
  rewrite upd_eq in H1; congruence.
  rewrite upd_ne in H1; eauto.
  destruct (handle_eq_dec h h0); subst; auto.
  specialize (H2 _ H1).
  rewrite H2 in H; inversion H; rewrite upd_eq; eauto.
  specialize (H2 _ H1).
  rewrite upd_ne; eauto.
Qed.

Lemma block_mem_subset_upd_irrel:
  forall bm bm' h v,
    bm' h = None ->
    bm' c= bm ->
    bm' c= (upd bm h v).
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h0); destruct H0.
  destruct (handle_eq_dec h h0); subst; auto.
  rewrite upd_ne in H1; eauto.
  destruct (handle_eq_dec h h0); subst; auto.
  congruence.
  rewrite upd_ne; eauto.
Qed.

Lemma block_mem_subset_extract_none:
  forall bm bm' h,
    bm h = None ->
    bm' c= bm ->
    bm' h = None.
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h); destruct H0; auto.
Qed.

Lemma block_mem_subset_extract_some:
  forall bm bm' h v,
    bm' h = Some v ->
    bm' c= bm ->
    bm h = Some v.
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h); destruct H0; auto.
Qed.

Hint Resolve block_mem_subset_refl block_mem_subset_upd_none
     block_mem_subset_upd_nop block_mem_subset_upd_irrel
     block_mem_subset_extract_none block_mem_subset_extract_some
     block_mem_subset_trans.



(* This portion is for extracting blocks with a list of handles 
 * Basically, list handle -> list tagged_block *)
Definition handle_valid (bm: block_mem) h := exists tb, bm h = Some tb.
Definition handles_valid bm hl:= Forall (handle_valid bm) hl.

Fixpoint extract_blocks (bm: block_mem) hl :=
  match hl with
  | nil => nil
  | h::t => match bm h with
           | None => extract_blocks bm t
           | Some tb => tb::extract_blocks bm t
           end
  end.

Lemma handles_valid_subset_trans:
  forall bm bm' l,
    handles_valid bm l ->
    bm c= bm' ->
    handles_valid bm' l.
Proof.
  unfold handles_valid, handle_valid; induction l; simpl; intros; auto.
  inversion H; subst.
  destruct H3.
  constructor; eauto.
Qed.

Lemma handles_valid_upd:
  forall bm l a v,
    handles_valid bm l ->
    handles_valid (upd bm a v) l.
Proof.
  unfold handles_valid, handle_valid; intros.
  apply Forall_forall; intros.
  eapply Forall_forall in H; eauto.
  destruct H.
  destruct (addr_eq_dec a x).
  eexists; apply upd_eq; eauto.
  eexists; rewrite upd_ne; eauto.
Qed.

Lemma handles_valid_rev_eq:
  forall bm l,
    handles_valid bm l ->
    handles_valid bm (rev l).
Proof.
  unfold handles_valid, handle_valid; intros.
  apply Forall_forall; intros.
  apply In_rev in H0.
  eapply Forall_forall in H; eauto.
Qed.

 Lemma handles_valid_app:
   forall hl1 hl2 bm,
     handles_valid bm (hl1++hl2) ->
     handles_valid bm hl1 /\ handles_valid bm hl2.
 Proof.
   unfold handles_valid; intros.
   split; [eapply forall_app_r; eauto
          | eapply forall_app_l; eauto ].
 Qed.

 Lemma handles_valid_cons:
   forall h hl bm,
     handles_valid bm (h::hl) ->
     handle_valid bm h /\ handles_valid bm hl.
 Proof.
   unfold handles_valid; intros.
   inversion H; eauto.
 Qed.


 
Lemma extract_blocks_length:
  forall bm l,
    handles_valid bm l ->
    length (extract_blocks bm l) = length l.
Proof.
  unfold handles_valid, handle_valid; induction l; simpl; intros; auto.
  destruct (bm a) eqn:D; simpl;
  inversion H; subst; auto.
  destruct H2; congruence.
Qed.

Lemma extract_blocks_app:
  forall l1 l2 bm,
    extract_blocks bm (l1 ++ l2) = extract_blocks bm l1 ++ extract_blocks bm l2.
Proof.
  induction l1; intros; simpl; auto.
  destruct (bm a).
  rewrite IHl1, app_comm_cons; auto.
  auto.
Qed.

Lemma extract_blocks_length_le:
  forall bm l,
    length (extract_blocks bm l) <= length l.
Proof.
  induction l; simpl in *; intros; eauto.
  destruct (bm a); simpl; omega.
Qed.

Lemma extract_blocks_length_lt:
  forall l h bm,
    List.In h l ->
    bm h = None ->
    length (extract_blocks bm l) < length l.
Proof.
  induction l; simpl in *; intros; intuition.
  subst; rewrite H0.
  pose proof (extract_blocks_length_le bm l); omega.
  specialize (IHl _ _ H1 H0).
  destruct (bm a); simpl; omega.
Qed.

Lemma extract_blocks_rev_length_eq:
  forall bm l,
    length (extract_blocks bm l) =
    length (extract_blocks bm (rev l)).
Proof.
  induction l; simpl; intuition.
  rewrite extract_blocks_app; simpl.
  destruct (bm a); simpl;
  rewrite IHl, app_length; simpl; omega.
Qed.

Lemma extract_blocks_upd_not_in:
  forall l h tb bm,
    ~List.In h l ->
    extract_blocks (upd bm h tb) l = extract_blocks bm l.
Proof.
  induction l; simpl in *; intros; intuition.
  rewrite upd_ne; auto.
  rewrite IHl; eauto.
Qed.

Lemma extract_blocks_selN:
  forall bm l a def deftb,
    handles_valid bm l ->
    a < length l ->
    bm (selN l a def) = Some (selN (extract_blocks bm l) a deftb).
Proof.
  unfold handles_valid, handle_valid;
  induction l; simpl; intros; try omega.
  destruct a0;
  destruct (bm a) eqn:D; simpl;
  inversion H; subst; auto;
  destruct H3; try congruence.
  apply IHl; auto; omega.
Qed.

Lemma extract_blocks_subset_trans:
  forall bm bm' hl,
    handles_valid bm hl ->
    bm c= bm' ->
    extract_blocks bm hl = extract_blocks bm' hl.
Proof.
  unfold block_mem_subset, handles_valid, handle_valid;
  induction hl; intros; simpl in *; auto.
  destruct (bm a) eqn:D; simpl;
  inversion H; subst; auto;
  destruct H3; try congruence.
  specialize (H0 a) as Hx; destruct Hx.
  erewrite H3; eauto.
  rewrite IHhl; eauto.
  congruence.
Qed.

Lemma extract_blocks_selN_inside:
  forall bm l a def deftb,
    handles_valid bm l ->
    a < length l ->
    selN (extract_blocks bm l) a deftb::nil = extract_blocks bm (selN l a def :: nil).
Proof.
  induction l; simpl; intros; try omega.
  destruct a0;
  destruct (bm a) eqn:D; simpl;
  inversion H; subst; auto;
  destruct H3; try congruence.
  erewrite IHl; try omega; simpl; auto.
Qed.

Lemma extract_blocks_firstn_length:
  forall bm l n,
    handles_valid bm l ->
    length (extract_blocks bm (firstn n l)) = length (firstn n l).
Proof.
  induction l; simpl; intros; try omega.
  rewrite firstn_nil; auto.
  destruct n; simpl; auto.
  destruct (bm a) eqn:D; simpl;
  inversion H; subst; auto;
  destruct H2; try congruence.
Qed.

Lemma extract_blocks_selN_some:
  forall l bm n v def1 def2,
    n < length l ->
    handles_valid bm l ->
    bm (selN l n def1) = Some v ->
    selN (extract_blocks bm l) n def2 = v.
Proof.
  induction l; simpl; intros; auto; try congruence.
  inversion H.
  inversion H0; subst.
  unfold handle_valid in *;
  destruct H4; rewrite H2; simpl; auto.
  destruct n; simpl; auto.
  rewrite H1 in H2; inversion H2; auto.
  eapply IHl; eauto; omega.
Qed.



(* extracting blocks for list of (T, handle) pairs
 * list (T * handle) -> list (T * tagged_block) *)

Definition handles_valid_list {T} bm (hl: list (T * handle)) :=
  handles_valid bm (map snd hl).

Definition extract_blocks_list {T} bm (hl:list (T * handle)) := 
  List.combine (map fst hl) (extract_blocks bm (map snd hl)).


Lemma handles_valid_list_subset_trans:
  forall T bm bm' l,
    @handles_valid_list T bm l ->
    bm c= bm' ->
    handles_valid_list bm' l.
Proof.
  unfold handles_valid_list; intros;
  eapply handles_valid_subset_trans; eauto.
Qed.

Lemma handles_valid_list_upd:
  forall T bm l a v,
    @handles_valid_list T bm l ->
    handles_valid_list (upd bm a v) l.
Proof.
  unfold handles_valid_list; intros.
  eapply handles_valid_upd; eauto.
Qed.

Lemma handles_valid_list_rev_eq:
  forall T bm l,
    @handles_valid_list T bm l ->
    handles_valid_list bm (rev l).
Proof.
  unfold handles_valid_list; intros.
  rewrite map_rev.
  eapply handles_valid_rev_eq; eauto.
Qed.

Lemma extract_blocks_list_subset_trans:
  forall T bm bm' hl,
    @handles_valid_list T bm hl ->
    bm c= bm' ->
    extract_blocks_list bm hl = extract_blocks_list bm' hl.
Proof.
  unfold block_mem_subset, handles_valid_list, extract_blocks_list;
  induction hl; intros; simpl in *; auto.
  apply handles_valid_cons in H; unfold handle_valid in H;
  destruct H; destruct H; rewrite H.
  specialize (H0 (snd a)) as Hx; destruct Hx.
  erewrite H3; eauto.
  rewrite IHhl; eauto.
Qed.




Import AddrMap Map MapFacts.

Definition handles_valid_map bm hmap:=
  handles_valid_list bm (elements hmap) .

Definition extract_block (bm: block_mem) h :=
  match bm h with
  | None => tagged_block0
  | Some tb => tb
  end.

Definition extract_blocks_map bm hm :=
  map (fun x => extract_block bm x) hm.

Lemma handles_valid_map_subset_trans:
  forall hmap bm bm',
    bm c= bm' ->
    handles_valid_map bm hmap ->
    handles_valid_map bm' hmap.
Proof.
  unfold handles_valid_map; intros.
  eapply handles_valid_list_subset_trans; eauto.
Qed.


Lemma handles_valid_map_equal:
  forall hmap hmap' bm,
    Map.Equal hmap hmap' ->
    handles_valid_map bm hmap ->
    handles_valid_map bm hmap'.
Proof.
  unfold handles_valid_map; intros.
  erewrite <- mapeq_elements; eauto.
Qed.

Lemma handles_valid_map_extract_some:
   forall vm a h bm,
     Map.find a vm = Some h ->
     handles_valid_map bm vm ->
     exists tb, bm h = Some tb.
 Proof.
   unfold Map.find, handles_valid_map, handles_valid_list;
   intro vm; destruct vm; generalize dependent this; induction this;
   simpl in *; intros; auto; try congruence.
   inversion is_bst; subst.
   unfold Map.elements, AddrMap_AVL.Raw.elements in *; simpl in *.
   rewrite AddrMap_AVL.Raw.Proofs.elements_app in H0.
   rewrite map_app in H0; apply handles_valid_app in H0.
   simpl in *; destruct H0, (OrderedTypeEx.Nat_as_OT.compare a k);
   inversion H1; unfold handle_valid in *; subst; destruct H4; eauto.
   inversion H; subst; eauto.
 Qed.

Lemma extract_blocks_map_equal:
  forall hmap hmap' bm,
    Map.Equal hmap hmap' ->
    Map.Equal (extract_blocks_map bm hmap) (extract_blocks_map bm hmap').
Proof.
  unfold extract_blocks_map; intros.
  apply MapFacts.map_m; eauto.
Qed.

Lemma empty_extract_blocks_map:
  forall hmap bm,
    Map.Empty hmap ->
    Map.Empty (extract_blocks_map bm hmap).
Proof.
  unfold Map.Empty, not; intros.
  apply MapFacts.map_mapsto_iff in H0;
  destruct H0; destruct H0; eauto.
Qed.

Lemma map_in_extract_blocks_map:
  forall hmap a bm,
    Map.In a (extract_blocks_map bm hmap) ->
    Map.In a hmap.
Proof.
  unfold extract_blocks_map; intros; eapply Map.map_2; eauto.
Qed.


Lemma map_find_extract_blocks_mem:
  forall hmap bm a h,
    find a hmap = Some h ->
    handles_valid_map bm hmap ->
    find a (extract_blocks_map bm hmap) =
    Some (extract_block bm h).
Proof.
  unfold handles_valid_map, handles_valid_list;
  intro hmap; destruct hmap.
  generalize dependent this;
  induction this; unfold Map.find, Map.elements in *; simpl in *;
  intros; try congruence.
  inversion is_bst; subst.
  unfold AddrMap_AVL.Raw.elements in H0; simpl in H0.
  repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in H0.
  rewrite app_nil_r, map_app in H0; simpl in H0.
  apply handles_valid_app in H0; intuition.
  apply handles_valid_cons in H2; intuition.
  destruct (OrderedTypeEx.Nat_as_OT.compare a k); intuition.
  inversion H; subst; auto.
Qed.

Lemma extract_blocks_map_extract_blocks_eq:
  forall hmap bm,
    handles_valid_map bm hmap ->
    List.map snd (elements (extract_blocks_map bm hmap)) =
    extract_blocks bm (List.map snd (elements hmap)).
Proof.
  unfold handles_valid_map, handles_valid_list;
  intro hmap; destruct hmap.
  generalize dependent this;
  induction this; simpl; intros; auto.
  inversion is_bst; subst.
  unfold Map.elements, AddrMap_AVL.Raw.elements in *; simpl in *.
  repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
  repeat rewrite app_nil_r, map_app in *; simpl in *.
  repeat (simpl; rewrite extract_blocks_app).
  simpl in *.
  apply handles_valid_app in H; intuition.
  apply handles_valid_cons in H1; intuition.
  unfold extract_block, handle_valid in *; destruct H3; rewrite H1.
  unfold AddrMap_AVL.Raw.elements; rewrite H, H2; auto.
Qed.      

Lemma map_find_In_elements:
  forall hmap a (h: handle),
    Map.find a hmap = Some h ->
    List.In h (List.map snd (Map.elements hmap)).
Proof.
  intro hmap; destruct hmap.
  generalize dependent this;
  induction this; unfold Map.find, Map.elements in *;
  simpl; intros; auto; try congruence.
  inversion is_bst; subst.
  unfold Map.elements, AddrMap_AVL.Raw.elements in *; simpl in *.
  repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *.
  repeat rewrite app_nil_r, map_app in *; simpl in *.
  simpl in *.
  apply in_or_app.
  destruct (OrderedTypeEx.Nat_as_OT.compare a k); try inversion H; subst; intuition.
  left; eapply H0; eauto.
  right; simpl; right; eapply H2; eauto.
Qed.

Lemma map_find_In_elements_none:
  forall hmap bm a,
    Map.find a hmap = None ->
    Map.find a (extract_blocks_map bm hmap) = None.
Proof.
  intro hmap; destruct hmap.
  generalize dependent this;
  induction this; unfold Map.find, Map.elements in *;
  simpl in *; intros; auto; try congruence.
  inversion is_bst; subst.
  destruct (OrderedTypeEx.Nat_as_OT.compare a k); try inversion H; subst;
  intuition eauto; congruence.
Qed.

Lemma extract_blocks_map_subset_trans:
  forall hmap bm bm',
    handles_valid_map bm hmap ->
    bm c= bm' ->
    Map.Equal (extract_blocks_map bm hmap)
              (extract_blocks_map bm' hmap).
Proof.
  unfold handles_valid_map, handles_valid_list;
  intros.
  unfold Map.Equal; intros.
  destruct (Map.find y hmap) eqn:D.
  repeat erewrite map_find_extract_blocks_mem; eauto.
  unfold extract_block.
  destruct (bm h) eqn:D0.
  erewrite block_mem_subset_extract_some; eauto.
  apply map_find_In_elements in D.
  unfold handles_valid, handle_valid  in *;
  rewrite Forall_forall in H.
  specialize (H _ D); destruct H; congruence.
  eapply handles_valid_subset_trans; eauto.
  repeat erewrite map_find_In_elements_none; eauto.
Qed.

Lemma map_add_extract_blocks_mem_comm:
  forall hmap bm a x,
    bm (snd a) = Some x ->
    Map.Equal (Map.add (fst a) x (extract_blocks_map bm hmap))
              (extract_blocks_map bm
                                  (Map.add (fst a) (snd a) hmap)).
Proof.
  intro hmap; destruct hmap.
  generalize dependent this;
  induction this;
  simpl in *; intros; auto; try congruence.
  unfold Map.Equal, Map.find; simpl; unfold extract_block;
  intros; destruct (OrderedTypeEx.Nat_as_OT.compare y (fst a)); try rewrite H; eauto.

  unfold Map.Equal in *; simpl in *; intros.
  unfold extract_blocks_map in *.
  rewrite MapFacts.map_o; unfold option_map.
  inversion is_bst; subst.
  destruct (OrderedTypeEx.Nat_as_OT.eq_dec (fst a) y).
  { (* fst a = y *)
    repeat rewrite MapFacts.add_eq_o; auto.
    unfold extract_block; rewrite H; auto.
  }
  { (* fst a <> y *) 
    repeat rewrite MapFacts.add_neq_o in *; auto.
    rewrite MapFacts.map_o; unfold option_map; auto.
  }
Qed.


  Lemma in_fst_snd_map_split:
    forall A B (l: list (A * B)) x y,
      List.In (x,y) l ->
      List.In x (List.map fst l) /\ List.In y (List.map snd l).
  Proof.
    induction l; simpl; intros; auto.
    destruct a; intuition; simpl in *.
    inversion H0; subst; auto.
    inversion H0; subst; auto.
    right; specialize (IHl x y H0); intuition.
    right; specialize (IHl x y H0); intuition.
  Qed.
  


Lemma in_fst:
    forall A B (l: list (A * B)) x y,
      List.In (x,y) l -> List.In x (List.map fst l).
  Proof.
    intros; apply in_fst_snd_map_split in H; intuition.
  Qed.



Lemma extract_blocks_list_KNoDup:
   forall a bm,
     handles_valid_list bm a ->
     KNoDup (extract_blocks_list bm a) ->
     KNoDup a.
 Proof.
   unfold KNoDup; induction a; simpl; intuition.
   inversion H; subst.
   unfold handle_valid in H3; destruct H3.
   unfold extract_blocks_list in *; simpl in *; rewrite H1 in *.
   inversion H0; subst.
   constructor; eauto.
   intuition.
   apply InA_alt in H2; destruct H2.
   destruct H2.
   destruct x0; inversion H2; simpl in *; subst.
   apply H5.
   apply In_KIn.
   rewrite map_fst_combine.
   eapply in_fst; eauto.
   rewrite extract_blocks_length; eauto.
   repeat rewrite map_length; eauto.
 Qed.





Definition handles_valid_nested {T} bm (hl: list (list (T * handle))) :=
  Forall (fun tl => handles_valid_list bm tl) hl.

Definition extract_blocks_nested {T} bm (hl: list (list (T * handle))) := 
  List.map (fun tl => extract_blocks_list bm tl) hl.

  Lemma handles_valid_nested_subset_trans:
    forall T ts bm bm',
      bm c= bm' ->
      @handles_valid_nested T bm ts ->
      handles_valid_nested bm' ts.
  Proof.
    unfold handles_valid_nested; intros.
    rewrite Forall_forall in *; intros;
    eapply handles_valid_subset_trans; eauto.
    apply H0; eauto.
  Qed.


  Lemma extract_blocks_nested_subset_trans:
    forall T ts bm bm',
      bm c= bm' ->
      @handles_valid_nested T bm ts ->
      extract_blocks_nested bm' ts =
      extract_blocks_nested bm ts.
  Proof.
    unfold handles_valid_nested, extract_blocks_nested; intros.
    apply map_ext_in; intros.
    rewrite Forall_forall in *; symmetry; 
    eapply extract_blocks_list_subset_trans; eauto.
  Qed.

Lemma extract_blocks_nested_length:
    forall T ts bm,
      length (@extract_blocks_nested T bm ts) = length ts.
  Proof.
    unfold extract_blocks_nested; intros.
    rewrite map_length; auto.
  Qed.

  Ltac solve_blockmem_subset:=
    match goal with
    | [|- block_mem_subset _ =p=> (fun _ : Mem.mem => _ c= _)] =>
      unfold pimpl; intros; solve_blockmem_subset
    | [|- _ c= _ ] =>
      auto; eapply block_mem_subset_trans;
      eauto; solve_blockmem_subset
    end.