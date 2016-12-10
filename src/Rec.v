Require Import Arith List String Omega Bool.
Require Import Word.
Require Import Eqdep_dec.
Require Import Array.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import ListUtils.
Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Module Rec.

  Inductive type :=
    | WordF : nat -> type
    | ArrayF : type -> nat -> type
    | RecF : list (string * type) -> type.

  Definition rectype := list (string * type).

  (** Better induction principle *)
  Fixpoint type_rect_nest
      (P : type -> Type)
      (Q : rectype -> Type)
      (wordc : forall n, P (WordF n))
      (arrayc : forall t, P t -> forall n, P (ArrayF t n))
      (recc : forall rt : rectype, Q rt -> P (RecF rt))
      (nilc : Q nil)
      (consc : forall n t rt, P t -> Q rt -> Q ((n,t)::rt))
      (t : type) : P t :=
    match t as t0 return (P t0) with
    | WordF n => wordc n
    | ArrayF t' n => arrayc t' (type_rect_nest P Q wordc arrayc recc nilc consc t') n
    | RecF rt => recc rt (list_rect Q nilc (fun p r =>
        let (n, t') as p return (Q r -> Q (p :: r)) := p
        in consc n t' r (type_rect_nest P Q wordc arrayc recc nilc consc t')) rt)
    end.


  Fixpoint data (t : type) : Type :=
    match t with
    | WordF l => word l
    | ArrayF t' _ => list (data t')
    | RecF rt =>
      (fix recdata (t : list (string * type)) : Type :=
        match t with
        | [] => unit
        | (_, ft) :: t' => data ft * recdata t'
        end%type) rt
    end.

  Definition recdata ft := data (RecF ft).

  Fixpoint len (t : type) : nat :=
    match t with
    | WordF l => l
    | ArrayF t' l => l * len t'
    | RecF rt =>
      (fix reclen (t : rectype) : nat :=
        match t with
        | [] => 0
        | (_, ft) :: t' => len ft + reclen t'
        end) rt
    end.

  Fixpoint well_formed {t : type} : data t -> Prop :=
    match t as t return (data t -> Prop) with
    | WordF _ => fun _ => True
    | ArrayF _ l => fun v => Datatypes.length v = l /\ Forall well_formed v
    | RecF rt =>
      (fix well_formed' {rt : rectype} : data (RecF rt) -> Prop :=
        match rt as rt return (data (RecF rt) -> Prop) with
        | [] => fun _ => True
        | (_, ft) :: t' => fun r =>
          let (r0, r') := r in well_formed r0 /\ well_formed' r'
        end) rt
    end.

  Theorem firstn_well_formed : forall (ft:type) n1 n2 w,
    @well_formed (ArrayF ft (n1+n2)) w ->
    @well_formed (ArrayF ft n1) (firstn n1 w).
  Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    rewrite firstn_length_l; omega.
    rewrite Forall_forall; intros.
    apply in_firstn_in in H2.
    rewrite Forall_forall in H1.
    apply H1.
    assumption.
  Qed.

  Theorem firstn_l_well_formed : forall (ft:type) n n' w,
    n <= n' ->
    @well_formed (ArrayF ft n') w ->
    @well_formed (ArrayF ft n) (firstn n w).
  Proof.
    intros.
    unfold well_formed in *.
    inversion H0.
    split.
    rewrite firstn_length_l; omega.
    rewrite Forall_forall in *; intros.
    eapply H2.
    eapply in_firstn_in; eauto.
  Qed.

  Theorem skipn_well_formed : forall (ft:type) n1 n2 w,
    @well_formed (ArrayF ft (n1+n2)) w ->
    @well_formed (ArrayF ft n2) (skipn n1 w).
  Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    rewrite skipn_length; omega.
    rewrite Forall_forall; intros.
    apply in_skipn_in in H2.
    rewrite Forall_forall in H1.
    apply H1.
    assumption.
  Qed.

  Theorem tl_well_formed : forall (ft:type) n d w,
    @well_formed (ArrayF ft (S n)) (d::w) ->
    @well_formed (ArrayF ft n) w.
  Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    simpl in *.
    omega.
    rewrite Forall_forall in *; intros.
    apply H1.
    constructor; assumption.
  Qed.

  Theorem empty_well_formed : forall (ft:type) w,
    List.length w = 0 ->
    @well_formed (ArrayF ft 0) w.
  Proof.
    intros.
    unfold well_formed.
    split; auto.
    apply length_nil in H.
    subst.
    auto.
  Qed.

  Inductive field_in : rectype -> string -> Prop :=
  | FE : forall t n ft, field_in ((n, ft) :: t) n
  | FS : forall t n n' ft, field_in t n -> field_in ((n', ft) :: t) n.

  Lemma empty_field_in : forall n, ~(field_in nil n).
  Proof.
    intros n f. inversion f.
  Qed.

  Lemma field_in_next : forall t n n' ft, n' <> n -> field_in ((n',ft) :: t) n -> field_in t n.
  Proof.
    intros t n n' ft ne f. inversion f; subst.
    contradiction ne. reflexivity.
    apply H3.
  Qed.

  Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : type :=
    match t as t return (field_in t n -> type) with
    | nil => fun f => match (empty_field_in f) with end
    | (n0, ft0)::_ => fun f =>
      match (string_dec n0 n) with
      | left _ => ft0
      | right ne => field_type (field_in_next ne f)
      end
    end f.

  Fixpoint recget {t : rectype} {n : string} (p : field_in t n) (r : recdata t) : data (field_type p) :=
    match t as t return (recdata t -> forall f : field_in t n, data (field_type f)) with
    | [] => fun _ f => match (empty_field_in f) with end
    | (n0, ft0) :: t' =>
      fun r f =>
      match (string_dec n0 n) as s
        return (data
            match s with
            | left _ => ft0
            | right ne => field_type (field_in_next ne f)
            end)
      with
      | left _ => (fst r)
      | right ne => recget (field_in_next ne f) (snd r)
      end
    end r p.

  Fixpoint recset {t : rectype} {n : string} (p : field_in t n) (r : recdata t) (v : data (field_type p)) {struct t} : recdata t.
    destruct t. contradiction (empty_field_in p).
    destruct p0 as [n0 ft0].
    simpl in v.
    destruct (string_dec n0 n) as [eq|neq]; constructor.
    apply v. apply (snd r).
    apply (fst r). apply (recset t n (field_in_next neq p) (snd r) v).
  Defined.
  (* TODO: define recset without tactics (somewhat messy) *)

  Theorem set_get_same : forall t n p r v, @recget t n p (recset p r v) = v.
  Proof.
    induction t; intros.
    contradiction (empty_field_in p).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl. destruct (string_dec n0 n).
    trivial. apply IHt.
  Qed.

  Theorem set_get_other : forall t n1 p1 n2 p2 r v, n1 <> n2 ->
    recget p1 r = @recget t n1 p1 (@recset t n2 p2 r v).
  Proof.
    induction t; intros n1 p1 n2 p2 r v neq.
    contradiction (empty_field_in p1).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl.
    destruct (string_dec n0 n2); destruct (string_dec n0 n1);
      subst; trivial.
    contradiction neq. auto.
    apply IHt. assumption.
  Qed.

  Fixpoint fieldp (t : rectype) (n : string) : option (field_in t n) :=
    match t as t return (option (field_in t n)) with
    | [] => None
    | (n0, l0) :: t' =>
      match (string_dec n0 n) with
      | left e =>
          eq_rec_r
            (fun n1 => option (field_in ((n1, l0) :: t') n))
            (Some (FE t' n l0)) e
      | right _ =>
        match (fieldp t' n) with
        | Some f => Some (FS n0 l0 f)
        | None => None
        end
      end
    end.

  Definition recget' {t : rectype} (n : string) (r : recdata t) :=
    match fieldp t n as fp
          return (match fp with 
                    | Some p => data (field_type p)
                    | None => True
                  end) with
      | Some p => recget p r
      | None => I
    end.

  Definition recset' {t : rectype} (n : string) (r : recdata t) :=
    match fieldp t n as fp
          return (recdata t -> match fp with
                    | Some p => data (field_type p) -> recdata t
                    | None => True
                  end) with
      | Some p => fun r v => recset p r v
      | None => fun _ => I
    end r.

  Fixpoint to_word {ft : type} : data ft -> word (len ft) :=
    match ft as ft return (data ft -> word (len ft)) with
    | WordF n => fun v => v
    | ArrayF ft0 n as ft =>
      (fix arrayf2word n v :=
        match n as n0 return (data (ArrayF ft0 n0) -> word (len (ArrayF ft0 n0))) with
        | 0 => fun _ => $0
        | S n0 => fun v =>
          match v with
          | nil => $0
          | v0 :: v' => combine (to_word v0) (arrayf2word n0 v')
          end
        end v) n
    | RecF t =>
      (fix rec2word {t : rectype} (r : recdata t) : word (len (RecF t)) :=
        match t as t return recdata t -> word (len (RecF t)) with
        | nil => fun _ => $0
        | (_, _) :: _ => fun r =>
          let (v, r') := r in combine (to_word v) (rec2word r')
        end r) t
    end.

  Fixpoint of_word {ft : type} : word (len ft) -> data ft :=
    match ft as ft return (word (len ft) -> data ft) with
    | WordF n => fun w => w
    | ArrayF ft0 n as ft =>
      (fix word2arrayf n w :=
        match n as n return (word (len (ArrayF ft0 n)) -> data (ArrayF ft0 n)) with
        | 0 => fun _ => []
        | S n' => fun w0 =>
          (of_word (split1 (len ft0) _ w0)) ::
          (word2arrayf n' (split2 (len ft0) _ w0))
        end w) n
    | RecF t =>
      (fix word2rec (t : rectype) (w : word (len (RecF t))) : recdata t :=
        match t as t return word (len (RecF t)) -> recdata t with
        | nil => fun _ => tt
        | (_, ft) :: t' => fun w =>
          (of_word (split1 (len ft) (len (RecF t')) w), 
           word2rec t' (split2 (len ft) (len (RecF t')) w))
        end w) t
  end.

  Theorem to_of_id : forall ft w, to_word (@of_word ft w) = w.
  Proof.
    einduction ft using type_rect_nest; simpl.
    reflexivity.
    induction n.
    auto.
    intro w. simpl in *. rewrite IHn. rewrite IHt. apply combine_split.
    apply IHt.
    intro w. rewrite word0. trivial.
    simpl. intro w.
    rewrite IHt. rewrite IHt0. apply combine_split.
  Qed.

  Hint Rewrite to_of_id.

  Theorem of_to_id : forall ft v, well_formed v -> of_word (@to_word ft v) = v.
  Proof.
    einduction ft using type_rect_nest.
    reflexivity.
    induction n; intros v H; simpl in v.
    destruct H. destruct v; try discriminate. reflexivity.
    simpl in *. destruct H. destruct v; try discriminate.
    rewrite split1_combine. rewrite split2_combine.
    inversion H0. subst. rewrite IHt by assumption. rewrite IHn by auto. trivial.
    2: instantiate (1 := fun rt => forall v,
      (fix well_formed' {rt : rectype} : data (RecF rt) -> Prop :=
        match rt as rt return (data (RecF rt) -> Prop) with
        | [] => fun _ => True
        | (_, ft) :: t' => fun r =>
          let (r0, r') := r in well_formed r0 /\ well_formed' r'
        end) rt v ->
      (fix word2rec (t : rectype) (w : word (len (RecF t))) : recdata t :=
        match t as t return word (len (RecF t)) -> recdata t with
        | nil => fun _ => tt
        | (_, ft) :: t' => fun w =>
          (of_word (split1 (len ft) (len (RecF t')) w),
           word2rec t' (split2 (len ft) (len (RecF t')) w))
        end w)
        rt
        ((fix rec2word {t : rectype} (r : recdata t) : word (len (RecF t)) :=
          match t as t return recdata t -> word (len (RecF t)) with
          | nil => fun _ => WO
          | (_, _) :: _ => fun r =>
            let (v, r') := r in combine (to_word v) (rec2word r')
          end r) rt v) = v).
    apply IHt.
    simpl. intros v t. destruct v. trivial.
    simpl. intro v. destruct v. intro Hrl. destruct Hrl.
    rewrite split1_combine. rewrite split2_combine.
    rewrite IHt0 by assumption. rewrite IHt by assumption. trivial.
  Qed.

  Theorem to_eq : forall ft a b,
    @to_word ft a = @to_word ft b ->
    well_formed a ->
    well_formed b ->
    a = b.
  Proof.
    intros.
    rewrite <- Rec.of_to_id with (v := a) by auto.
    rewrite <- Rec.of_to_id with (v := b) by auto.
    congruence.
  Qed.

  Theorem of_eq : forall ft a b,
    @of_word ft a = @of_word ft b ->
    a = b.
  Proof.
    intros.
    rewrite <- Rec.to_of_id with (w := a).
    rewrite <- Rec.to_of_id with (w := b).
    congruence.
  Qed.

  Lemma of_word_empty : forall t n w,
    n = 0 ->
    @of_word (ArrayF t n) w = nil.
  Proof.
    intros.
    generalize w.
    rewrite H.
    intros.
    simpl in w0.
    apply length_nil.
    reflexivity.
  Qed.

  Theorem of_word_length : forall ft w, well_formed (@of_word ft w).
  Proof.
    einduction ft using type_rect_nest.
    simpl. trivial.
    simpl. induction n.
    split; trivial.
    intro w.
    edestruct IHn.
    split. simpl. rewrite H. trivial.
    simpl. constructor. apply IHt. assumption.
    apply IHt.
    simpl. trivial.
    simpl. intro w. split.
    apply IHt. apply IHt0.
  Qed.

  Theorem of_word_well_formed : forall (ft:type) w,
    well_formed (@of_word ft w).
  Proof.
    apply of_word_length.
  Qed.

  Theorem array_of_word_length : forall ft n w,
    List.length (@of_word (ArrayF ft n) w) = n.
  Proof.
    induction n; intros; simpl.
    reflexivity.
    f_equal.
    apply IHn.
  Qed.


  Theorem to_word_append_any: forall sz l n l2,
    Datatypes.length l > n -> @to_word (ArrayF (WordF sz) n) (app l l2) = @to_word (ArrayF (WordF sz) n) l.
  Proof.
    simpl.
    induction l; simpl; induction n; intros; auto; try omega.
    f_equal.
    apply IHl.
    omega.
  Qed.

  Theorem to_word_append_zeroes: forall sz l n m,
    @to_word (ArrayF (WordF sz) n) (app l (repeat $0 m)) = @to_word (ArrayF (WordF sz) n) l.
  Proof.
    simpl.
    induction l; simpl; induction n; intros; auto.
    + induction m; simpl; auto.
      induction n; try rewrite IHn;
      apply combine_wzero.
    + f_equal.
      apply IHl.
  Qed.

  Arguments of_word : simpl never.
  Arguments to_word : simpl never.


  (**
   * Efficient implementations for fetching or updating a single element from a
   * [word (len (ArrayF ft len))], without decoding/encoding the whole word to
   * and from the corresponding [list (data ft)].
   *)

  Definition middle (low mid high : nat) (w : word (low + (mid + high))) : word mid :=
    split1 mid high (split2 low (mid+high) w).

  Lemma word_selN_helper : forall idx l lenft, idx < l ->
    l * lenft = idx * lenft + (lenft + (l * lenft - lenft - idx * lenft)).
  Proof.
    intros.
    rewrite plus_assoc.
    rewrite Nat.add_sub_assoc.
    rewrite <- plus_assoc.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag; rewrite <- plus_n_O.
    rewrite Nat.add_sub_assoc.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag; rewrite <- plus_n_O.
    reflexivity.
    replace (lenft) with (1 * lenft) at 1 by omega.
    apply Nat.mul_le_mono_r; omega.
    replace (lenft) with (1 * lenft) at 3 by omega.
    rewrite <- Nat.mul_sub_distr_r.
    apply Nat.mul_le_mono_r; omega.
  Qed.

  Definition word_selN {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l))) : word (len ft).
    refine (if lt_dec idx l then _ else $0).
    refine (middle (idx * len ft) (len ft) (l * len ft - len ft - idx * len ft) _).
    replace (idx * len ft + (len ft + (l * len ft - len ft - idx * len ft))) with (l * len ft).
    exact w.
    apply word_selN_helper.
    apply l0.
  Defined.

  Theorem word_selN_equiv : forall ft l idx w def, idx < l ->
    of_word (@word_selN ft l idx w) = selN (of_word w) idx def.
  Proof.
    induction l; intros; try omega.
    unfold of_word in *; fold (@of_word ft) in *.
    destruct idx; simpl.
    - f_equal. clear IHl.
      unfold word_selN, middle.

      destruct (lt_dec 0 (S l)); [|omega].
      generalize (word_selN_helper (len ft) l0).
      replace (S l * len ft - len ft - 0 * len ft) with (l * len ft) by lia.
      simpl; intros.
      erewrite <- eq_rec_eq.
      reflexivity.

    - rewrite <- IHl by omega; clear IHl.
      f_equal.
      unfold word_selN.
      destruct (lt_dec (S idx) (S l)); try omega.
      destruct (lt_dec idx l); try omega.

      unfold middle.

      generalize (word_selN_helper (len ft) l0).
      generalize (word_selN_helper (len ft) l1).
      replace (S l * len ft - len ft - S idx * len ft)
        with (l * len ft - len ft - idx * len ft) by lia.
      generalize (l * len ft - len ft - idx * len ft).

      intros.
      f_equal.
      generalize dependent e0.
      generalize dependent e.
      generalize (len ft + n); clear n.
      generalize dependent w; simpl.
      generalize (idx * len ft).
      generalize (l * len ft); clear H l0 l1 l def idx.
      generalize (len ft); clear ft.
      intros.

      assert (n + n0 = n + (n1 + n2)) as e0' by omega.
      replace ((eq_rec (n + n0) (fun n => word n) w (n + n1 + n2) e0))
        with (match plus_assoc _ _ _ in _ = N return word N with
              | refl_equal => (eq_rec (n+n0) (fun n => word n) w (n+(n1+n2)) e0')
              end).

      rewrite <- split2_iter.
      f_equal.
      generalize dependent e0'; clear e0.
      rewrite <- e; intros.
      repeat rewrite <- eq_rec_eq.
      reflexivity.

      destruct (Nat.add_assoc n n1 n2).
      destruct e0.
      repeat rewrite <- eq_rec_eq.
      reflexivity.
  Qed.


  Lemma word_updN_helper1 : forall idx l lenft, idx < l ->
    lenft + (l * lenft - idx * lenft - lenft) = l * lenft - idx * lenft.
  Proof.
    intros.

    rewrite Nat.add_sub_assoc. rewrite plus_comm. rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag. omega.

    rewrite <- Nat.mul_sub_distr_r. replace (lenft) with (1 * lenft) at 1 by omega.
    apply Nat.mul_le_mono_r; omega.
  Qed.

  Lemma word_updN_helper2 : forall idx l lenft, idx < l ->
    idx * lenft + (l * lenft - idx * lenft) = l * lenft.
  Proof.
    intros.

    rewrite Nat.add_sub_assoc. rewrite plus_comm. rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag. omega.

    apply Nat.mul_le_mono_r; omega.
  Qed.

  Definition word_updN {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l)))
                                             (v : word (len ft)) : word (len (ArrayF ft l)).
    refine (if lt_dec idx l then _ else w); simpl in *.

    replace (l * len ft) with (idx * len ft + (l * len ft - idx * len ft))
      in * by (apply word_updN_helper2; assumption).
    remember (split1 (idx * len ft) (l * len ft - idx * len ft) w) as low; clear Heqlow.
    refine (combine low _).

    replace (l * len ft - idx * len ft) with (len ft + (l * len ft - idx * len ft - len ft))
      in * by (apply word_updN_helper1; assumption).
    rewrite plus_assoc in *.

    remember (split2 (idx * len ft + len ft) (l * len ft - idx * len ft - len ft) w) as hi; clear Heqhi.
    refine (combine v hi).
  Defined.

  Theorem word_updN_oob : forall ft l idx w v, idx >= l ->
    @word_updN ft l idx w (to_word v) = w.
  Proof.
    unfold word_updN; simpl; intros.
    destruct (lt_dec idx l); auto.
    exfalso; omega.
  Qed.

  Theorem word_updN_equiv : forall ft l idx w v, idx < l ->
    @word_updN ft l idx w (to_word v) = @to_word (ArrayF ft l) (updN (of_word w) idx v).
  Proof.
    simpl; intros.
    unfold word_updN.
    destruct (lt_dec idx l); try omega; clear H.

    unfold eq_rec_r, eq_rec.
    rewrite eq_rect_word_offset.
    repeat rewrite eq_rect_nat_double.

    generalize (word_updN_helper1 (len ft) l0).
    generalize (word_updN_helper2 (len ft) l0).

    generalize dependent l.
    induction idx; simpl; intros.
    - destruct l; try omega.
      unfold of_word; fold (@of_word ft).
      unfold to_word; fold (@to_word ft).
      replace ((fix word2arrayf (n : nat) (w0 : word (n * len ft)) {struct n} : 
         list (data ft) :=
           match n as n0 return (word (len (ArrayF ft n0)) -> data (ArrayF ft n0)) with
           | 0 => fun _ : word (len (ArrayF ft 0)) => []
           | S n' =>
               fun w1 : word (len (ArrayF ft (S n'))) =>
               of_word (split1 (len ft) (n' * len ft) w1)
               :: word2arrayf n' (split2 (len ft) (n' * len ft) w1)
           end w0) l (split2 (len ft) (l * len ft) w))
        with (@of_word (ArrayF ft l) (split2 (len ft) (l * len ft) w)) by reflexivity.
      simpl.

      repeat rewrite eq_rect_nat_double.
      rewrite eq_rect_combine.
      f_equal.
      rewrite eq_rect_split2.
      rewrite eq_rect_nat_double.
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
      match goal with
      | [ |- _ = ?r ] =>
        replace (r)
          with (@to_word (ArrayF ft l) (of_word (split2 (len ft) (len (ArrayF ft l)) w)))
          by reflexivity
      end.
      rewrite to_of_id.
      reflexivity.

    - destruct l; try omega.
      unfold of_word; fold (@of_word ft). fold Init.Nat.mul. fold len.
      unfold to_word; fold (@to_word ft). fold Init.Nat.mul. fold len.
      fold recdata. fold data.
      match goal with
      | [ |- _ = match updN (_ :: ?x) _ _ with | nil => _ | v0 :: v' => _ end ] =>
        replace (x) with (@of_word (ArrayF ft l) (split2 (len ft) (l * len ft) w)) by reflexivity
      end.
      simpl.

      rewrite to_of_id.
      assert (idx < l) as Hidx by omega.
      specialize (IHidx l (split2 (len ft) (l * len ft) w) Hidx).
      clear l0.

      generalize dependent e; generalize dependent e0. simpl.
      replace (len ft + l * len ft - (len ft + idx * len ft))
        with (len ft + (l * len ft - len ft - idx * len ft)) by
        ( rewrite Nat.sub_add_distr;
          rewrite minus_plus;
          rewrite <- word_updN_helper1 by omega;
          lia ).
      intros.
      rewrite eq_rect_combine.
      rewrite eq_rect_split2.
      repeat rewrite eq_rect_nat_double.

      repeat match goal with
      | [ |- context[(eq_trans ?a ?b)] ] =>
        generalize (eq_trans a b); intros
      end.
      clear e0.

      rewrite <- combine_split with (sz1:=len ft) (sz2:=idx * len ft)
        (w:=(split1 (len ft + idx * len ft) (len ft + (l * len ft - len ft - idx * len ft))
        (eq_rect (len ft + l * len ft) (fun y : nat => word y) w
           (len ft + idx * len ft + (len ft + (l * len ft - len ft - idx * len ft))) 
           (eq_sym e)))).
      assert (len ft + (idx * len ft + (len ft + (l * len ft - len ft - idx * len ft))) =
              len ft + idx * len ft + (len ft + (l * len ft - len ft - idx * len ft)))
        as Hassoc by lia.
      rewrite (combine_assoc _ _ _ Hassoc).
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      rewrite eq_rect_combine.
      f_equal.

      rewrite split1_iter with (Heq:=eq_sym Hassoc).
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      generalize dependent (eq_trans (eq_sym e) (eq_sym Hassoc)).
      replace (idx * len ft + (len ft + (l * len ft - len ft - idx * len ft)))
        with (l * len ft) by lia.
      intros.
      rewrite <- (eq_rect_eq_dec eq_nat_dec). reflexivity.

      unfold to_word in IHidx; fold (@to_word ft) in IHidx; simpl in IHidx.
      fold data in IHidx. fold len in IHidx. fold Init.Nat.mul in IHidx.
      erewrite <- IHidx.

      repeat rewrite eq_rect_split2.
      assert (len ft + (idx * len ft + len ft + (l * len ft - idx * len ft - len ft)) =
        len ft + (idx * len ft + len ft) + (l * len ft - idx * len ft - len ft))
        as Hs2iter by lia.
      rewrite split2_iter with (Heq:=Hs2iter).
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.

      rewrite <- eq_rect_combine.
      rewrite eq_rect_nat_double.

      repeat match goal with
      | [ |- context[eq_sym ?a] ] => generalize (eq_sym a); intros
      | [ |- context[eq_trans ?a ?b] ] => generalize (eq_trans a b); intros
      | [ |- context[eq_rect_split2_helper ?a ?b] ] => generalize (eq_rect_split2_helper a b); intros
      end; clear.

      generalize dependent idx; intro idx.
      replace (l * len ft - idx * len ft - len ft)
        with (l * len ft - len ft - idx * len ft) by lia.
      intros.
      f_equal; clear.
      f_equal; clear.

      erewrite split1_split2.
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      f_equal; clear.

      assert (len ft + (l * len ft - len ft - idx * len ft) = l * len ft - idx * len ft)
        as Hr by lia.
      generalize dependent e0; generalize dependent e7.
      rewrite Hr.
      intros.
      f_equal; clear.
      f_equal; clear.
      apply UIP_dec; exact eq_nat_dec.

      f_equal; clear.
      generalize dependent idx; intro idx.
      replace (len ft + (idx * len ft + len ft))
        with (len ft + idx * len ft + len ft) by lia.
      intros.
      f_equal; clear.
      f_equal; clear.
      apply UIP_dec; exact eq_nat_dec.
      apply UIP_dec; exact eq_nat_dec.
      Grab Existential Variables.
      rewrite plus_assoc; reflexivity.
      lia.
      lia.
  Qed.

  Definition word_mask (l n : nat) (idx : nat) : word (l * n).
    destruct l eqn:H.
    exact (wzero 0).
    exact (wlshift (combine (wones n) (wzero (n0 * n))) (idx * n)).
  Defined.

  Definition word_selN_shift (l n : nat) (idx : nat) (w : word (l * n)) : word n.
    destruct l eqn:H.
    exact (wzero n).
    exact (split1 n (n0 * n) (wrshift w (idx * n))).
  Defined.

  Definition word_updN_shift (l n : nat) (idx : nat) (w : word (l * n))
                                             (v : word n) : word (l * n).
    destruct l eqn:H.
    exact w.
    set (v' := zext v (n0 * n)).
    set (mask := word_mask (S n0) n idx).
    set (shift := n * idx).
    set (newmask := wlshift v' shift).
    exact ((w ^& (wnot mask)) ^| newmask).
  Defined.


  Fact word_shift_helper1 : forall n idx off, n + (idx + off) * n = (idx + 1 + off) * n.
  Proof. intros. lia. Qed.

  Fact word_shift_helper2 : forall n l, l > 0 -> n + (l - 1) * n = l * n.
  Proof. intros. destruct l; simpl; try rewrite <- minus_n_O; omega. Qed.

  Fact word_shift_helper3 : forall a b c, a * c + (c + b * c) = (a + 1 + b) * c.
  Proof. intros. lia. Qed.

  Fact word_shift_helper4 : forall a b c, (a + 1 + b) * c = a * c + c + b * c.
  Proof. intros. lia. Qed.

  Theorem word_selN_shift_gt_0 : forall idx off n w,
    word_selN_shift (idx + 1 + off) n idx w = split1 n ((idx + off) * n)
      (eq_rect _ word (wrshift w (idx * n)) _ (eq_sym (word_shift_helper1 n idx off))).
  Proof.
    intros idx off n.
    assert (idx + 1 + off = S (idx + off)) as H by omega.
    generalize_proof.
    rewrite H.
    intros.
    eq_rect_simpl.
    reflexivity.
  Qed.

  Theorem eq_rect_combine_dist3 : forall a b c (w : word ((a + 1 + b) * c)),
    let H := word_shift_helper3 a b c in
    let H1 := word_shift_helper4 a b c in
    let w' := eq_rect ((a + 1 + b) * c) word w _ (eq_sym H) in
    let w'' := eq_rect ((a + 1 + b) * c) word w _ H1 in
    w = eq_rect _ word (combine
      (split1 (a * c) _ w')
      (combine
        (middle (a * c) c (b * c) w')
        (split2 (a * c + c) (b * c) w''))) _ H.
  Proof.
    intros.
    generalize dependent H1.
    generalize dependent w.
    generalize dependent H.
    intros H.
    rewrite <- H.
    intros.
    subst w' w''.
    eq_rect_simpl.
    unfold middle.
    rewrite <- combine_split with (w := w).
    repeat f_equal; rewrite combine_split; auto.
    erewrite <- eq_rect_word_match.
    rewrite combine_end.
    reflexivity.
  Qed.

  Fact eq_rect_both_helper : forall T (x y z : T), x = y -> z = y -> z = x.
  Proof. intros. subst. reflexivity. Qed.

  Theorem eq_rect_both : forall x y z (H1 : x = z) (H2 : y = z) wa wb,
    wa = eq_rect y word wb x (eq_rect_both_helper H1 H2) -> eq_rect x word wa z H1 = eq_rect y word wb z H2.
  Proof.
    intros. subst.
    eq_rect_simpl.
    reflexivity.
   Qed.

  Fact split1_eq_rect_combine_partial_helper : forall a b c d (H : a + c = a + b + d), c = b + d.
  Proof. intros. omega. Qed.

  Theorem split1_eq_rect_combine_partial : forall a b c d H (wa : word a) (wc : word c),
    split1 (a + b) d
      (eq_rect (a + c) word (combine wa wc) (a + b + d) H) =
        combine wa (split1 b d (eq_rect _ word wc _ (split1_eq_rect_combine_partial_helper a b c d H))).
  Proof.
    intros a b c d H.
    assert (c = b + d) by omega; subst c.
    intros.
    erewrite <- split1_combine; f_equal.
    eq_rect_simpl.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    rewrite combine_split.
    reflexivity.
  Qed.

  Fact combine_eq_rect_combine_helper : forall a b c d, a + b = c -> a + (b + d) = c + d.
  Proof. intros. omega. Qed.

  Fact combine_eq_rect_combine : forall a b c d H (wa : word a) (wb : word b) (wa' : word d),
    combine (eq_rect (a + b) word (combine wa wb) c H) wa' =
    eq_rect _ word (combine wa (combine wb wa')) _ (combine_eq_rect_combine_helper a b d H).
  Proof.
    intros a b c d H.
    subst c.
    intros.
    eq_rect_simpl.
    erewrite combine_assoc, eq_rect_word_match.
    reflexivity.
  Qed.

  Fact split2_eq_rect_combine : forall a b c H (wa : word a) (wc : word c),
    split2 a b (eq_rect (a + c) word (combine wa wc) (a + b) H) =
    eq_rect c word wc b (plus_reg_l c b a H).
  Proof.
    intros a b c H.
    assert (c = b) by omega; subst.
    intros.
    eq_rect_simpl.
    apply split2_combine.
  Qed.

  Theorem word_selN_shift_eq_middle : forall idx off n w,
    @word_selN_shift (idx + 1 + off) n idx w = middle (idx * n) n (off * n)
      (eq_rec _ word w _ (eq_sym (word_shift_helper3 idx off n))).
  Proof.
    intros.
    eq_rect_simpl.
    rewrite word_selN_shift_gt_0.
    generalize_proof.
    replace ((idx + off) * n) with (idx * n + off * n) by lia.
    intros HH.
    unfold wrshift.
    eq_rect_simpl.
    erewrite combine_eq_rect2.
    rewrite eq_rect_combine_dist3 with (w := w); eq_rect_simpl.
    erewrite combine_eq_rect_combine; eq_rect_simpl.
    erewrite split2_eq_rect_combine; eq_rect_simpl.
    repeat erewrite combine_assoc, eq_rect_word_match; eq_rect_simpl.
    unfold middle.
    repeat progress (rewrite eq_rect_combine ||
                     rewrite split1_combine  ||
                     rewrite split2_combine).
    reflexivity.
    Grab Existential Variables.
    all : lia.
  Qed.

  Theorem word_selN_shift_equiv : forall ft l idx w, idx < l ->
    @word_selN ft l idx w = @word_selN_shift l (len ft) idx w.
  Proof.
    intros.
    generalize dependent w.
    remember (l - idx - 1) as off.
    assert (l = (idx + 1+ off)) by omega.
    subst l.
    intros w.
    unfold word_selN.
    destruct lt_dec; try omega.
    erewrite word_selN_shift_eq_middle.
    generalize dependent (word_selN_helper (len ft) l).
    replace ((idx + 1 + off) * len ft - len ft - idx * len ft) with (off * len ft) by lia.
    intros HH.
    f_equal.
    apply eq_rect_both; eq_rect_simpl.
    reflexivity.
  Qed.

  Definition word_selN' {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l)))
    : word (len ft) := @word_selN_shift l (len ft) idx w.

  Theorem word_selN'_equiv : forall ft l idx w def, idx < l ->
    of_word (@word_selN' ft l idx w) = selN (of_word w) idx def.
  Proof.
    intros.
    unfold word_selN'.
    rewrite <- word_selN_shift_equiv; auto.
    apply word_selN_equiv; auto.
  Qed.


  Theorem word_updN_shift_l_gt_0 : forall idx off n w v,
    @word_updN_shift (idx + 1 + off) n idx w v = w ^& wnot (word_mask (idx + 1 + off) n idx) ^| wlshift (
      eq_rect _ word (zext v ((idx + off) * n)) _ (word_shift_helper1 n idx off)) (idx * n).
  Proof.
    unfold word_updN_shift.
    intros idx off n.
    generalize dependent (word_shift_helper1 n idx off).
    replace (idx + 1 + off) with (S (idx + off)) by omega.
    intros.
    eq_rect_simpl.
    f_equal.
    f_equal.
    apply mult_comm.
  Qed.

  Theorem word_mask_l_gt_0 : forall l n idx (H : l > 0),
    @word_mask l n idx = wlshift (eq_rect _ word (combine (wones n) (wzero ((l - 1) * n))) _
      (word_shift_helper2 n H))
      (idx * n).
  Proof.
    unfold word_mask; destruct l; auto; intros.
    erewrite combine_eq_rect2.
    repeat f_equal.
    generalize_proof.
    intros HH; rewrite HH; auto.
    Grab Existential Variables.
    simpl; rewrite <- minus_n_O.
    reflexivity.
  Qed.

  Theorem wnot_word_mask_l_gt_0 : forall off n idx,
    wnot (@word_mask (idx + 1 + off) n idx) = eq_rec _ word (
    combine (wones (idx * n)) (combine (wzero n) (wones (off * n)))) ((idx + 1 + off) * n)
      (word_shift_helper3 idx off n).
  Proof.
    intros off n idx.
    generalize dependent (word_shift_helper3 idx off n).
    replace (idx + 1 + off) with (S (idx + off)) by omega.
    intros H.
    unfold word_mask.
    rewrite wnot_wlshift.
    eq_rect_simpl.
    erewrite split1_eq_rect_eq1; f_equal.
    eq_rect_simpl.
    rewrite split1_eq_rect_combine_partial; f_equal.
    rewrite wnot_combine, wnot_ones.
    rewrite split1_eq_rect_combine_partial; f_equal.
    erewrite wzero_dist, wzero_rev, <- combine_wzero.
    repeat rewrite wnot_eq_rect.
    eq_rect_simpl.
    rewrite wnot_combine, split1_combine.
    apply wnot_zero.
    Grab Existential Variables.
    all : lia.
  Qed.

  Lemma wand_wnot_word_mask_w : forall idx off n w,
    let H := word_shift_helper3 idx off n in
    let w' := eq_rect _ word w (idx * n + (n + off * n)) (eq_sym H) in
    let w'' := eq_rect _ word w (idx * n + n + off * n) (word_shift_helper4 idx off n) in
    w ^& wnot (word_mask (idx + 1 + off) n idx) = eq_rec _ word (
      combine (split1 (idx * n) _ w') (combine (wzero n) (split2 (idx * n + n) _ w''))) _ H.
  Proof.
    intros.
    erewrite eq_rect_combine_dist3 with (w := w).
    erewrite wnot_word_mask_l_gt_0 by omega.
    unfold wand.
    unfold eq_rec.
    erewrite <- eq_rect_bitwp'; f_equal.
    repeat erewrite <- combine_bitwp; f_equal.
    - rewrite wand_comm, wand_wones.
      reflexivity.
    - rewrite wand_comm, wand_wzero.
      rewrite wand_comm, wand_wones.
      reflexivity.
  Qed.

  Theorem word_updN_shift_abs : forall off idx n w v,
    let H := word_shift_helper3 idx off n in
    let H1 := word_shift_helper4 idx off n in
    let w' := eq_rec _ word w _ (eq_sym H) in
    let w'' := eq_rec _ word w _ H1 in
    @word_updN_shift (idx + 1 + off) n idx w v = eq_rec _ word (
      combine (split1 (idx * n) (n + off * n) w')
      (combine v (split2 (idx * n + n) (off * n) w''))) _ H.
  Proof.
    intros.
    assert ((idx + 1 + off) * n = idx * n + n + off * n) as Hc by lia.
    erewrite eq_rect_combine_dist3 with (w := w).
    erewrite word_updN_shift_l_gt_0.
    erewrite wand_wnot_word_mask_w.
    unfold wlshift, zext.
    eq_rect_simpl.
    rewrite split1_combine.
    rewrite eq_rect_combine_assoc'.
    rewrite split2_combine.
    unfold wor.
    rewrite eq_rect_bitwp_1.
    f_equal.
    replace (eq_rect ((idx + 1 + off) *n) word (split1 _ (idx * n) _) _ _)
      with (combine (wzero (idx * n)) (combine v (wzero (off * n)))).
    - repeat rewrite <- combine_bitwp.
      repeat rewrite wor_wzero.
      repeat try (rewrite wor_comm, wor_wzero).
      reflexivity.
    - erewrite split1_eq_rect_eq1.
      repeat (eq_rect_simpl; erewrite split1_eq_rect_combine_partial; f_equal).
      erewrite wzero_dist, wzero_rev, <- combine_wzero.
      eq_rect_simpl.
      symmetry; apply split1_combine.
    Grab Existential Variables.
    all : lia.
  Qed.

  Fact word_updN_abs_helper : forall idx off, idx < idx + 1 + off.
  Proof. intros. omega. Qed.

  Theorem word_updN_abs : forall idx off ft w v,
    let H := word_shift_helper3 idx off (len ft) in
    let H1 := word_shift_helper4 idx off (len ft) in
    let w' := eq_rec _ word w _ (eq_sym H) in
    let w'' := eq_rec _ word w _ H1 in
    @word_updN ft (idx + 1 + off) idx w v = eq_rec _ word (
      combine (split1 (idx * len ft) (len ft + off * len ft) w')
        (combine v (split2 (idx * len ft + len ft) (off * len ft) w''))) _ H.
  Proof.
    unfold word_updN; simpl.
    intros.
    destruct lt_dec; try omega.
    repeat eexists.
    eq_rect_simpl; apply eq_rect_both.
    rewrite eq_rect_word_offset; eq_rect_simpl.
    rewrite eq_rect_combine; f_equal.
    + erewrite eq_rect_split1_eq2.
      eq_rect_simpl; f_equal.
      apply eq_rect_both.
      eq_rect_simpl; reflexivity.
    + apply eq_rect_both.
      rewrite eq_rect_combine.
      rewrite eq_rect_split2.
      eq_rect_simpl.
      repeat (try reflexivity; f_equal; eq_rect_simpl; try apply eq_rect_both).
    Grab Existential Variables.
    all : simpl; lia.
  Qed.

  Theorem word_updN_shift_equiv : forall l idx ft w v, idx < l ->
    @word_updN_shift l (len ft) idx w v = @word_updN ft l idx w v.
  Proof.
    intros l idx ft w v H.
    remember (l - idx - 1) as off.
    assert (l = idx + 1 + off) by omega.
    subst l.
    erewrite word_updN_shift_abs by auto.
    erewrite word_updN_abs.
    repeat f_equal.
  Qed.

  Definition word_updN' {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l)))
            (v : word (len ft)) : word (len (ArrayF ft l)) := @word_updN_shift l (len ft) idx w v.

  Theorem word_updN'_equiv : forall ft l idx w v, idx < l ->
    @word_updN' ft l idx w (to_word v) = @to_word (ArrayF ft l) (updN (of_word w) idx v).
  Proof.
    intros.
    unfold word_updN'.
    rewrite word_updN_shift_equiv; auto.
    apply word_updN_equiv; auto.
  Qed.

  Program Fixpoint word_concat {ft : type} (items : list (word (len ft)))
    : word ((len ft) * (List.length items)) :=
    match items with
    | nil => $0
    | m :: rest => combine m (@word_concat ft rest)
    end.
  Next Obligation.
  abstract nia.
  Defined.

  Theorem of_word_zero_list : forall ft n,
    @Rec.of_word (ArrayF ft n) $0 = repeat (Rec.of_word $0) n.
  Proof.
    induction n; simpl; auto.
    rewrite <- IHn; clear IHn.
    unfold of_word at 1 3.
    rewrite split1_zero.
    rewrite split2_zero.
    reflexivity.
  Qed.

  Lemma len_add' : forall t n m,
    len (ArrayF t n) + len (ArrayF t m) = len (ArrayF t (n+m)).
  Proof.
    intros.
    simpl.
    nia.
  Qed.

  Lemma combine_0 : forall (v: word 0) n (w: word n),
    combine v w = w.
  Proof.
    intros.
    shatterer.
  Qed.

  Definition len_add {t n m}
    (v:word (len (ArrayF t n) + len (ArrayF t m))) : word (len (ArrayF t (n+m))).
    rewrite len_add' in v.
    exact v.
  Defined.

  Definition len_split {t n m}
    (v:word (len (ArrayF t (n+m)))) : word (len (ArrayF t n) + len (ArrayF t m)).
    rewrite <- len_add' in v.
    exact v.
  Defined.

  Lemma of_word_cons : forall t n (w: word (len (ArrayF t (S n)))),
    of_word w = (of_word (split1 (len t) (n * len t) w)) ::
      (@of_word (ArrayF t n) (split2 (len t) (n * len t) w)).
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem combine_app' : forall (t:type) (n m:nat) H
    (v : word (len (ArrayF t n))) (w : word (len (ArrayF t m))),
    app (of_word v) (of_word w) = of_word (eq_rect (len (ArrayF t n) + len (ArrayF t m))
      (fun n => word n)
      (combine v w)
      (len (ArrayF t (n+m))) H).
  Proof.
    intros.
    induction n.
    simpl.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    rewrite combine_0; reflexivity.
    simpl len in *.
    rewrite of_word_cons.
    simpl.
    erewrite IHn.
    rewrite of_word_cons.

    rewrite <- combine_split with (sz1:=len t) (sz2:=n * len t) (w := v).
    f_equal.
    rewrite split1_combine.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite eq_rect_combine.
    rewrite split1_combine.
    reflexivity.

    rewrite split2_combine.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite eq_rect_combine.
    rewrite split2_combine.
    f_equal.

    Grab Existential Variables.
    all: omega.
  Qed.

  Theorem combine_app : forall (t:type) (n m:nat)
    (v : word (len (ArrayF t n))) (w : word (len (ArrayF t m))),
    app (of_word v) (of_word w) = of_word (len_add (combine v w)).
  Proof.
    intros.
    unfold len_add.
    apply combine_app'.
  Qed.

  Theorem cons_to_word : forall (t:type) (n:nat)
    d v,
    @to_word (ArrayF t (S n)) (d :: v) =
      combine (to_word d) (@to_word (ArrayF t n) v).
  Proof.
    intros.
    inversion t; auto.
  Qed.

  Theorem split1_firstn : forall t n m
    (w: word (len (ArrayF t (n+m)))) Heq,
    firstn n (of_word w) =
      of_word (split1 (len (ArrayF t n)) (len (ArrayF t m))
        (eq_rect _ word w _ Heq)).
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.

    simpl plus in *.
    rewrite of_word_cons.
    simpl.
    rewrite of_word_cons.
    unfold eq_rec_r in *.
    f_equal.
    erewrite split1_iter.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    simpl in *.
    f_equal.
    erewrite eq_rect_split1_eq2.
    f_equal.
    erewrite IHn.
    rewrite eq_rect_split2.
    erewrite split1_split2.
    repeat f_equal.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    unfold eq_rec.
    f_equal.
    apply proof_irrelevance.

    Grab Existential Variables.
    all: try omega.
    simpl.
    nia.
  Qed.

  Theorem split2_skipn : forall t n m
    (w: word (len (ArrayF t (n+m)))) Heq,
    skipn n (of_word w) =
      of_word (split2 (len (ArrayF t n)) (len (ArrayF t m))
       (eq_rect _ word w _ Heq)).
  Proof.
    intros.
    induction n.
    simpl.
    unfold eq_rec_r.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    reflexivity.

    simpl plus in *.
    rewrite of_word_cons.
    simpl.

    unfold eq_rec_r in *.
    erewrite IHn.
    rewrite eq_rect_split2.
    erewrite split2_iter.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    unfold eq_rec.
    repeat f_equal.
    apply proof_irrelevance.

    Grab Existential Variables.
    omega.
    simpl; nia.
  Qed.

End Rec.

Notation "r :-> n" := (Rec.recget' n r) (at level 20).
Notation "r :=> n := v" := (Rec.recset' n r v) (at level 80).

Notation "r .⟦ n ⟧" := (Rec.recget' n r) (at level 8).
Notation "r .⟦ n := v ⟧" := (Rec.recset' n r v) (at level 8).


(**
 * This [compute_rec] convtactic allows us to do partial evaluation
 * of [recget] and [recset] so that extracted code does not deal
 * with ASCII string names of fields at runtime.  To use it, define
 * terms with something like:
 *
 *   Definition xx := Eval compute_rec in yy.
 *
 * where [yy] may contain calls to [recget] and [recset].
 *)

Declare Reduction compute_rec :=
  cbv [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind].

Tactic Notation "rec_cbv" "in" hyp(H) :=
  cbv [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in H;
  cbn [fst snd] in H.

Tactic Notation "rec_cbv" :=
  cbv [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind];
  cbn [fst snd].

Ltac rec_simpl :=
  repeat match goal with
  | [ H: context [ Rec.recget' ] |- _ ] => rec_cbv in H
  | [ H: context [ Rec.recset' ] |- _ ] => rec_cbv in H
  | [ |- context [ Rec.recget' ] ] => rec_cbv
  | [ |- context [ Rec.recset' ] ] => rec_cbv
  end.

