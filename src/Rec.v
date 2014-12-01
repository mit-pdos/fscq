Require Import Arith List String Omega. 
Require Import Word.

Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Module Rec.

  Inductive type :=
    | WordF : nat -> type
    | ArrayF : type -> nat -> type
    | RecF : list (string * type) -> type.

  Definition rectype := list (string * type).

  (* Better induction principle *)
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

  Fixpoint list_all {A : Type} (P : A -> Prop) (xs : list A) : Prop :=
    match xs with
    | [] => True
    | x :: x' => P x /\ list_all P x'
    end.

  Fixpoint has_right_length {t : type} : data t -> Prop :=
    match t as t return (data t -> Prop) with
    | WordF _ => fun _ => True
    | ArrayF _ l => fun v => Datatypes.length v = l /\ list_all has_right_length v
    | RecF rt =>
      (fix has_right_lengths {rt : rectype} : data (RecF rt) -> Prop :=
        match rt as rt return (data (RecF rt) -> Prop) with
        | [] => fun _ => True
        | (_, ft) :: t' => fun r =>
          let (r0, r') := r in has_right_length r0 /\ has_right_lengths r'
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
      let (v, r') := r in
      match (string_dec n0 n) as s
        return (data
            match s with
            | left _ => ft0
            | right ne => field_type (field_in_next ne f)
            end)
      with
      | left _ => v
      | right ne => recget (field_in_next ne f) r'
      end
    end r p.

  Fixpoint recset {t : rectype} {n : string} (p : field_in t n) (r : recdata t) (v : data (field_type p)) {struct t} : recdata t.
    destruct t. contradiction (empty_field_in p).
    destruct p0 as [n0 ft0]. destruct r as [v0 r'].
    simpl in v.
    destruct (string_dec n0 n) as [eq|neq]; constructor.
    apply v. apply r'.
    apply v0. apply (recset t n (field_in_next neq p) r' v).
  Defined.
  (* TODO: define recset without tactics (somewhat messy) *)

  Theorem set_get_same : forall t n p r v, @recget t n p (recset p r v) = v.
  Proof.
    induction t; intros.
    contradiction (empty_field_in p).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl. destruct (string_dec n0 n).
    trivial. apply IHt.
  Defined.

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
        | 0 => fun _ => WO
        | S n0 => fun v =>
          match v with
          | nil => $0
          | v0 :: v' => combine (to_word v0) (arrayf2word n0 v')
          end
        end v) n
    | RecF t =>
      (fix rec2word {t : rectype} (r : recdata t) : word (len (RecF t)) :=
        match t as t return recdata t -> word (len (RecF t)) with
        | nil => fun _ => WO
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

  Theorem of_to_id : forall ft v, has_right_length v -> of_word (@to_word ft v) = v.
  Proof.
    einduction ft using type_rect_nest.
    reflexivity.
    induction n; intros v H; simpl in v.
    destruct H. destruct v; try discriminate. reflexivity.
    simpl in *. destruct H. destruct v; try discriminate.
    rewrite split1_combine. rewrite split2_combine.
    destruct H0. rewrite IHt by assumption. rewrite IHn by auto. trivial.
    instantiate (Q := fun rt => forall v,
      (fix has_right_lengths {rt : rectype} : data (RecF rt) -> Prop :=
        match rt as rt return (data (RecF rt) -> Prop) with
        | [] => fun _ => True
        | (_, ft) :: t' => fun r =>
          let (r0, r') := r in has_right_length r0 /\ has_right_lengths r'
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

  Theorem of_word_length : forall ft w, has_right_length (@of_word ft w).
  Proof.
    einduction ft using type_rect_nest.
    simpl. trivial.
    simpl. induction n.
    unfold list_all. split; trivial.
    intro w.
    edestruct IHn.
    split. simpl. rewrite H. trivial.
    simpl. split. apply IHt. assumption.
    apply IHt.
    simpl. trivial.
    simpl. intro w. split.
    apply IHt. apply IHt0.
  Qed.

  Arguments of_word : simpl never.
  Arguments to_word : simpl never.
End Rec.

Notation "r :-> n" := (Rec.recget' n r) (at level 20).
Notation "r :=> n := v" := (Rec.recset' n r v) (at level 80).

(*
Definition inodetype : Rec.rectype := [("free", Rec.WordF 1); ("len", Rec.WordF 16); ("block0", Rec.WordF 16)].
Definition inode1 : Rec.recdata inodetype := ($1, ($11, ($1677, tt))).
Parameter inode2 : Rec.recdata inodetype.
Definition foo := Eval compute in inode2 :-> "len".
Definition foo2 := Eval compute in inode2 :=> "len" := $17.
*)
