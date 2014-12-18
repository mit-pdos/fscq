Require Import Eqdep_dec Arith Omega List.
Require Import Word WordAuto Pred Rec Pack Prog BasicProg Hoare SepAuto Array Log.

Set Implicit Arguments.

(**
 * A variant of array that packs multiple items into a single disk block.
 *)

Record xparams := {
  RAStart : addr;
  RALen : addr
}.

Section RECARRAY.

  Theorem list_selN_ext' : forall len T (a b : list T) default,
    length a = len
    -> length b = len
    -> (forall pos, pos < len -> selN a pos default = selN b pos default)
    -> a = b.
  Proof.
    induction len; intros; destruct a; destruct b; simpl in *; try congruence.
    f_equal.
    apply (H1 0).
    omega.
    eapply IHlen; [ omega | omega | ].
    intros.
    apply (H1 (S pos)).
    omega.
  Qed.

  Theorem list_selN_ext : forall T (a b : list T) default,
    length a = length b
    -> (forall pos, pos < length a -> selN a pos default = selN b pos default)
    -> a = b.
  Proof.
    intros. apply list_selN_ext' with (len:=length a) (default:=default); auto.
  Qed.

  (** XXX use [nth] *)
  Lemma nth_selN_eq : forall t n l (z:t), selN l n z = nth n l z.
  Proof.
    induction n; intros; destruct l; simpl; auto.
  Qed.

  Ltac nth_selN H := intros; repeat rewrite nth_selN_eq; apply H; assumption.

  Lemma in_selN : forall t n l (z:t), n < length l -> In (selN l n z) l.
  Proof.
    nth_selN nth_In.
  Qed.

  Lemma in_sel : forall t n l (z:t), wordToNat n < length l -> In (sel l n z) l.
  Proof.
    intros. apply in_selN; assumption.
  Qed.

  Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
    In x l \/ x = xn.
  Proof.
    induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
    destruct (IHn l x xn H); auto.
  Qed.

  Lemma in_upd : forall t n l x (xn:t), In x (upd l n xn) ->
    In x l \/ x = xn.
  Proof.
    intros. apply in_updN with (n:=wordToNat n); auto.
  Qed.

  Lemma Forall_upd : forall t P l n (v:t), Forall P l -> P v -> Forall P (upd l n v).
  Proof.
    intros. apply Forall_forall. intros v0 Hi. apply in_upd in Hi. destruct Hi.
    rewrite Forall_forall in H. apply H; assumption.
    subst. assumption.
  Qed.

  Lemma concat_length : forall T (l : list (list T)),
    length (fold_right (@app _) nil l) = fold_right plus 0 (map (@length _) l).
  Proof.
    induction l; auto.
    simpl; rewrite app_length; rewrite IHl; trivial.
  Qed.

  Lemma updN_selN_eq : forall T (l : list T) ix default,
    updN l ix (selN l ix default) = l.
  Proof.
    induction l; auto.
    intros. destruct ix. auto. simpl. rewrite IHl. trivial.
  Qed.

  Lemma upd_sel_eq : forall T (l : list T) ix default,
    upd l ix (sel l ix default) = l.
  Proof.
    unfold upd, sel. intros. apply updN_selN_eq.
  Qed.

  Lemma updN_app1 : forall t l l' (v:t) n,
    n < length l -> updN (l ++ l') n v = updN l n v ++ l'.
  Proof.
    (* copied from proof of app_nth1 *)
    induction l.
    intros.
    inversion H.
    intros l' d n.
    case n; simpl; auto.
    intros; rewrite IHl; auto with arith.
  Qed.

  Lemma updN_app2 : forall t l l' (v:t) n,
    n >= length l -> updN (l ++ l') n v = l ++ updN l' (n - length l) v.
  Proof.
    (* copied from proof of app_nth2 *)
    induction l.
    intros.
    simpl.
    rewrite <- minus_n_O; auto.
    intros l' d n.
    case n; simpl; auto.
    intros.
    inversion H.
    intros.
    rewrite IHl; auto with arith.
  Qed.

  Lemma updN_concat : forall t a b m l (v:t), b < m ->
    Forall (fun sl => length sl = m) l ->
    updN (fold_right (@app _) nil l) (b + a * m) v =
      fold_right (@app _) nil (updN l a (updN (selN l a nil) b v)).
  Proof.
    (* XXX this is almost exactly the same as selN_concat *)
    induction a; intros; destruct l; simpl; inversion H0.
    trivial.
    replace (b + 0) with b by omega. subst.
    rewrite updN_app1; auto.
    trivial.
    subst. remember (a * length l) as al. rewrite updN_app2 by omega.
    replace (b + (length l + al) - length l) with (b + al) by omega. subst.
    rewrite IHa; auto.
  Qed.

  Lemma selN_app1 : forall t l l' (d:t) n,
    n < length l -> selN (l ++ l') n d = selN l n d.
  Proof.
    nth_selN app_nth1.
  Qed.

  Lemma selN_app2 : forall t l l' (d:t) n,
    n >= length l -> selN (l ++ l') n d = selN l' (n - length l) d.
  Proof.
    nth_selN app_nth2.
  Qed.

  Lemma nested_selN_concat : forall t a b m l (z:t), b < m ->
    Forall (fun sl => length sl = m) l ->
    selN (selN l a nil) b z = selN (fold_right (app (A:=t)) nil l) (b + a * m) z.
  Proof.
    induction a; intros; destruct l; simpl; inversion H0.
    trivial.
    replace (b + 0) with b by omega. subst.
    rewrite selN_app1; auto.
    trivial.
    subst. remember (a * length l) as al. rewrite selN_app2 by omega.
    replace (b + (length l + al) - length l) with (b + al) by omega. subst.
    apply IHa; assumption.
  Qed.

  (** If we index into the concatenation of a list of length-[m] lists, it's
      the same as indexing into the [n % m]'th element of the [n / m]'th list *)
  Lemma nested_sel_divmod_concat : forall t l n m (z:t), m <> $0 ->
    Forall (fun sl => length sl = wordToNat m) l ->
    sel (sel l (n ^/ m) nil) (n ^% m) z = sel (fold_right (app (A:=t)) nil l) n z.
  Proof.
    intros. unfold sel. rewrite nested_selN_concat with (m:=wordToNat m).
    word2nat'. rewrite Nat.mul_comm. rewrite Nat.add_comm. rewrite <- Nat.div_mod.
    trivial. assumption. apply le_lt_trans with (m := wordToNat n). apply div_le; assumption.
    apply wordToNat_bound.
    apply lt_le_trans with (m := wordToNat m).
    apply Nat.mod_upper_bound; assumption.
    apply Nat.lt_le_incl; apply wordToNat_bound.
    word2nat'.
    apply Nat.mod_upper_bound; assumption.
    apply lt_le_trans with (m := wordToNat m).
    apply Nat.mod_upper_bound; assumption.
    apply Nat.lt_le_incl; apply wordToNat_bound.
    assumption.
  Qed.

  Theorem selN_list_eq' : forall A len (vs vs' : list A) default,
    length vs = len
    -> length vs' = len
    -> (forall i, i < len -> selN vs i default = selN vs' i default)
    -> vs = vs'.
  Proof.
    induction len.
    - destruct vs; destruct vs'; simpl; intros; try congruence.
    - destruct vs; destruct vs'; simpl; intros; try congruence.
      f_equal.
      apply (H1 0); omega.
      eapply IHlen; eauto.
      intros.
      apply (H1 (S i)); omega.
  Qed.

  Theorem selN_list_eq : forall A (vs vs' : list A) default,
    length vs = length vs'
    -> (forall i, i < length vs -> selN vs i default = selN vs' i default)
    -> vs = vs'.
  Proof.
    intros.
    eapply selN_list_eq'; [ apply eq_refl | auto | auto ].
  Qed.

  Theorem selN_updN_ne : forall vs n n' v, n < length vs
    -> n <> n'
    -> selN (updN vs n v) n' ($0 : valu) = selN vs n' ($0 : valu).
  Proof.
    induction vs; destruct n'; destruct n; simpl; intuition; try omega.
  Qed.

  Lemma concat_In :
    forall T ls (x : T), In x (fold_right (@app _) nil ls) -> exists l, In l ls /\ In x l.
  Proof.
    induction ls.
    intros. simpl in H. inversion H.
    simpl. intros x Hi. apply in_app_or in Hi. destruct Hi.
    exists a. tauto.
    apply IHls in H. destruct H. exists x0. tauto.
  Qed.

  Variable itemtype : Rec.type.
  Variable items_per_valu : addr.
  Variable items_per_valu_not_0 : items_per_valu <> $0.
  Definition item := Rec.data itemtype.
  Definition item_zero := @Rec.of_word itemtype $0.
  Definition blocktype : Rec.type := Rec.ArrayF itemtype (wordToNat items_per_valu).
  Definition block := Rec.data blocktype.
  Definition block_zero := @Rec.of_word blocktype $0.
  Variable blocksz_ok : valulen = Rec.len blocktype.

  Definition rep_block (b : block) : valu.
    rewrite blocksz_ok. refine (Rec.to_word b).
  Defined.

  Definition valu_to_block (v : valu) : block.
    rewrite blocksz_ok in v. refine (Rec.of_word v).
  Defined.

  Lemma rep_valu_id : forall b, Rec.well_formed b -> valu_to_block (rep_block b) = b.
    unfold valu_to_block, rep_block.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Pack.eq_rect_nat_double.
    rewrite <- eq_rect_eq_dec; [| apply eq_nat_dec ].
    apply Rec.of_to_id; assumption.
  Qed.

  Definition array_item_pairs (xp : xparams) (vs : list block) : pred :=
    ([[ length vs = wordToNat (RALen xp) ]] *
     [[ Forall Rec.well_formed vs ]] *
     array (RAStart xp) (map rep_block vs) $1)%pred.

  Definition array_item (xp : xparams) (vs : list item) :=
    (exists vs_nested, array_item_pairs xp vs_nested *
     [[ vs = fold_right (@app _) nil vs_nested ]])%pred.

  Theorem array_item_well_formed :
    forall xp vs m, array_item xp vs m -> Forall Rec.well_formed vs.
  Proof.
    intros; rewrite Forall_forall; simpl; intros.
    unfold array_item, array_item_pairs in *.
    destruct H. destruct_lift H. rewrite Forall_forall in H5.
    subst. apply concat_In in H0. destruct H0.
    eapply Forall_forall; [apply H5|]; apply H0.
  Qed.

  Theorem array_item_well_formed' :
    forall xp vs, array_item xp vs =p=> [[ Forall Rec.well_formed vs ]] * any.
  Proof.
    intros. apply lift_impl. apply array_item_well_formed.
  Qed.

  (** Get the [pos]'th item in the [block_ix]'th block *)
  Definition get_pair T lxp xp block_ix pos rx : prog T :=
    v <- LOG.read_array lxp (RAStart xp) block_ix $1 ;
    let ib := valu_to_block v in
    let i := sel ib pos item_zero in
    rx i.

  (** Update the [pos]'th item in the [block_ix]'th block to [i] *)
  Definition put_pair T lxp xp block_ix pos i rx : prog T :=
    v <- LOG.read_array lxp (RAStart xp) block_ix $1 ;
    let ib' := upd (valu_to_block v) pos i in
    let v' := rep_block ib' in
    ok <- LOG.write_array lxp (RAStart xp) block_ix $1 v' ;
    rx ok.

  Hint Rewrite map_length.
  Hint Rewrite seq_length.
  Hint Resolve wlt_lt.
  Hint Rewrite sel_map_seq using auto.
  Hint Rewrite rep_valu_id.


  Theorem get_pair_ok : forall lxp xp block_ix pos,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * array_item_pairs xp ilistlist)%pred m ]] *
           [[ (block_ix < RALen xp)%word ]] *
           [[ (pos < items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel (sel ilistlist block_ix nil) pos item_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} get_pair lxp xp block_ix pos.
  Proof.
    unfold get_pair.
    hoare.
    unfold array_item_pairs in *. cancel. autorewrite with core.
    unfold array_item_pairs in H3. destruct_lift H3.
    rewrite H7. auto.
    unfold array_item_pairs in H3. destruct_lift H3.
    subst. rewrite sel_map at 1. autorewrite with core. auto.
    rewrite Forall_forall in H12. apply H12.
    apply in_selN. rewrite H10. auto. rewrite H10. auto.
    unfold LOG.log_intact. cancel.
  Qed.


  Theorem put_pair_ok : forall lxp xp block_ix pos i,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * array_item_pairs xp ilistlist)%pred m ]] *
           [[ (block_ix < RALen xp)%word ]] *
           [[ (pos < items_per_valu)%word ]] *
           [[ Rec.well_formed i ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * array_item_pairs xp (upd ilistlist block_ix (upd (sel ilistlist block_ix nil) pos i)))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} put_pair lxp xp block_ix pos i.
  Proof.
    unfold put_pair.
    hoare_unfold LOG.unfold_intact.
    unfold array_item_pairs. cancel.
    autorewrite with core. auto.
    unfold array_item_pairs in H. destruct_lift H.
    rewrite H8. auto.
    unfold array_item_pairs. cancel.

    (* Coq bug 3815 or 3816? *)
    autorewrite with core. auto.
    unfold array_item_pairs in H. destruct_lift H.
    rewrite H11. auto.

    apply pimpl_or_r. right. unfold array_item_pairs in *.
    destruct_lift H. cancel.
    autorewrite with core.
    rewrite sel_map at 1. autorewrite with core. cancel.
    rewrite Forall_forall in H10. apply H10.
    apply in_selN. rewrite H8. auto.  rewrite H8. auto.
    autorewrite with core. auto.
    apply Forall_upd. assumption.
    split. autorewrite with core. rewrite Forall_forall in H10. apply H10.
    apply in_sel. rewrite H8. auto.
    apply Forall_upd. rewrite Forall_forall in H10. apply H10. apply in_sel. rewrite H8. auto.
    rewrite Forall_forall in H10.
    auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (get_pair _ _ _ _) _) => apply get_pair_ok : prog.
  Hint Extern 1 ({{_}} progseq (put_pair _ _ _ _ _) _) => apply put_pair_ok : prog.

  Definition get T lxp xp inum rx : prog T :=
    i <- get_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu);
    rx i.

  Definition put T lxp xp inum i rx : prog T :=
    ok <- put_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu) i;
    rx ok.

  Theorem get_ok : forall lxp xp inum,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * array_item xp ilist)%pred m ]] *
           [[ (inum < RALen xp ^* items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel ilist inum item_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} get lxp xp inum.
  Proof.
    unfold get, array_item.

    intros.
    eapply pimpl_ok2. eauto with prog.

    intros.
    norm.
    cancel.
    (* Something about type coersions is making [assumption] take forever.. *)
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    pred_apply; instantiate (a2:=l); cancel.
    apply wdiv_lt_upper_bound; [auto | rewrite wmult_comm; assumption].

    apply wmod_upper_bound; auto.
    step.
    subst.
    unfold array_item_pairs in H. unfold rep_block in H.
    destruct_lift H.
    apply nested_sel_divmod_concat; auto.
    eapply Forall_impl; [| apply H8].
    intro a. simpl. tauto.
    step.
  Qed.


  Theorem upd_divmod : forall (l : list block) (pos : addr) (v : item),
    Forall Rec.well_formed l
    -> Array.upd (fold_right (@app _) nil l) pos v =
       fold_right (@app _) nil (Array.upd l (pos ^/ items_per_valu)
         (Array.upd (sel l (pos ^/ items_per_valu) nil) (pos ^% items_per_valu) v)).
  Proof.
    intros. unfold upd.
    rewrite <- updN_concat with (m := wordToNat items_per_valu).
    word2nat'. rewrite Nat.mul_comm. rewrite Nat.add_comm. rewrite <- Nat.div_mod.
    trivial. assumption. apply le_lt_trans with (m := wordToNat pos). apply div_le; assumption.
    apply wordToNat_bound.
    apply lt_le_trans with (m := wordToNat items_per_valu).
    apply Nat.mod_upper_bound; assumption.
    apply Nat.lt_le_incl; apply wordToNat_bound.
    word2nat'.
    apply Nat.mod_upper_bound; assumption.
    apply lt_le_trans with (m := wordToNat items_per_valu).
    apply Nat.mod_upper_bound; assumption.
    apply Nat.lt_le_incl; apply wordToNat_bound.
    rewrite Forall_forall in *; intros; apply H; assumption.
  Qed.

  Theorem put_ok : forall lxp xp inum i,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * array_item xp ilist)%pred m ]] *
           [[ (inum < RALen xp ^* items_per_valu)%word ]] *
           [[ Rec.well_formed i ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * array_item xp (upd ilist inum i))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} put lxp xp inum i.
  Proof.
    unfold put, array_item.
    intros. eapply pimpl_ok2. eauto with prog.
    intros.
    norm.
    cancel.
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    split.
    split; [constructor |].
    pred_apply. instantiate (a2:=l); cancel.
    apply wdiv_lt_upper_bound; [auto | rewrite wmult_comm; assumption].
    apply wmod_upper_bound; auto.
    assumption.
    step.
    apply pimpl_or_r. right.
    norm.
    cancel.
    split; [constructor |].
    split; [constructor |].
    pred_apply. cancel.

    apply upd_divmod.

    repeat match goal with
    | [ H: context[array_item_pairs _ _] |- _ ] =>
      unfold array_item_pairs in H; destruct_lift H
    end.
    auto.
    step.
  Qed.
End RECARRAY.

Hint Extern 1 ({{_}} progseq (get _ _ _ _ _ _) _) => apply get_ok : prog.
Hint Extern 1 ({{_}} progseq (put _ _ _ _ _ _ _) _) => apply put_ok : prog.

(* If two arrays are in the same spot, their contents have to be equal *)
Hint Extern 0 (okToUnify (array_item ?a ?b ?c ?xp _) (array_item ?a ?b ?c ?xp _)) =>
  unfold okToUnify; constructor : okToUnify.
