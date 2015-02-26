Require Import Arith List String Omega Bool.
Require Import Word.
Require Import Eqdep_dec.
Require Import Array.
Require Import Psatz.

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
    simpl in v. simpl. destruct (string_dec n0 n2); destruct (string_dec n0 n1); subst.
    rewrite e0 in neq. contradiction neq. trivial.
    trivial.
    trivial.
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

  Theorem of_to_id : forall ft v, well_formed v -> of_word (@to_word ft v) = v.
  Proof.
    einduction ft using type_rect_nest.
    reflexivity.
    induction n; intros v H; simpl in v.
    destruct H. destruct v; try discriminate. reflexivity.
    simpl in *. destruct H. destruct v; try discriminate.
    rewrite split1_combine. rewrite split2_combine.
    inversion H0. subst. rewrite IHt by assumption. rewrite IHn by auto. trivial.
    instantiate (Q := fun rt => forall v,
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

  Lemma combine_zeroes: forall sz1 sz2 w,
    w = natToWord sz2 0 -> combine (natToWord sz1 0) w = natToWord (sz1 + sz2) 0.
  Proof.
    induction sz1.
    intros; auto.
    intros; simpl. rewrite IHsz1; auto.
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
    + destruct m; simpl; auto.
      rewrite combine_zeroes; auto.
      fold repeat.
      induction n; auto.
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
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
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
      repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
      reflexivity.

      destruct (Nat.add_assoc n n1 n2).
      destruct e0.
      repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
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
    refine (if lt_dec idx l then _ else $0); simpl in *.

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

End Rec.

Notation "r :-> n" := (Rec.recget' n r) (at level 20).
Notation "r :=> n := v" := (Rec.recset' n r v) (at level 80).

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
  cbn [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym].

Ltac rec_simpl :=
  cbn [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym] in *.
