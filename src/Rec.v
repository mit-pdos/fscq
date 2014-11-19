Require Import Arith List String Omega. 
Require Import Word.

Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Module Rec.

  Inductive fieldtype :=
    | WordF : nat -> fieldtype
    | ArrayF : fieldtype -> nat -> fieldtype.

  Fixpoint fielddata (t : fieldtype) : Type :=
    match t with
    | WordF l => word l
    | ArrayF t' _ => list (fielddata t')
    end.

  Fixpoint fieldlen (t : fieldtype) : nat :=
    match t with
    | WordF l => l
    | ArrayF t' l => l * fieldlen t'
    end.

  Definition rectype := list (string * fieldtype).

  Fixpoint recdata (t : rectype) : Type := 
    match t with
    | [] => unit
    | (_, ft) :: t' => fielddata ft * recdata t'
    end%type.

  Fixpoint reclen (t : rectype) : nat :=
    match t with
    | [] => 0
    | (_, ft) :: t' => fieldlen ft + reclen t'
    end.

  Fixpoint list_all {A : Type} (P : A -> Prop) (xs : list A) : Prop :=
    match xs with
    | [] => True
    | x :: x' => P x /\ list_all P x'
    end.

  Fixpoint has_right_length {ft : fieldtype} : fielddata ft -> Prop :=
    match ft as ft return (fielddata ft -> Prop) with
    | WordF _ => fun _ => True
    | ArrayF ft0 l => fun v => Datatypes.length v = l /\ list_all has_right_length v
    end.

  Fixpoint has_right_lengths {t : rectype} : recdata t -> Prop :=
    match t as t return (recdata t -> Prop) with
    | [] => fun _ => True
    | (_, ft) :: t' => fun r =>
      let (r0, r') := r in has_right_length r0 /\ has_right_lengths r'
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

  Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : fieldtype :=
    match t as t return (field_in t n -> fieldtype) with
    | nil => fun f => match (empty_field_in f) with end
    | (n0, ft0)::_ => fun f =>
      match (string_dec n0 n) with
      | left _ => ft0
      | right ne => field_type (field_in_next ne f)
      end
    end f.

  Fixpoint recget {t : rectype} {n : string} (p : field_in t n) (r : recdata t) : fielddata (field_type p) :=
    match t as t return (recdata t -> forall f : field_in t n, fielddata (field_type f)) with
    | [] => fun _ f => match (empty_field_in f) with end
    | (n0, ft0) :: t' =>
      fun r f =>
      let (v, r') := r in
      match (string_dec n0 n) as s
        return (fielddata
            match s with
            | left _ => ft0
            | right ne => field_type (field_in_next ne f)
            end)
      with
      | left _ => v
      | right ne => recget (field_in_next ne f) r'
      end
    end r p.

  Fixpoint recset {t : rectype} {n : string} (p : field_in t n) (r : recdata t) (v : fielddata (field_type p)) {struct t} : recdata t.
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
                    | Some p => fielddata (field_type p)
                    | None => True
                  end) with
      | Some p => recget p r
      | None => I
    end.

  Definition recset' {t : rectype} (n : string) (r : recdata t) :=
    match fieldp t n as fp
          return (recdata t -> match fp with
                    | Some p => fielddata (field_type p) -> recdata t
                    | None => True
                  end) with
      | Some p => fun r v => recset p r v
      | None => fun _ => I
    end r.

  Fixpoint field2word {ft : fieldtype} : fielddata ft -> word (fieldlen ft) :=
    match ft as ft return (fielddata ft -> word (fieldlen ft)) with
    | WordF n => fun v => v
    | ArrayF ft0 n as ft =>
      (fix arrayf2word n v :=
        match n as n0 return (fielddata (ArrayF ft0 n0) -> word (fieldlen (ArrayF ft0 n0))) with
        | 0 => fun _ => WO
        | S n0 => fun v =>
          match v with
          | nil => $0
          | v0 :: v' => combine (field2word v0) (arrayf2word n0 v')
          end
        end v) n
    end.

  Fixpoint rec2word {t : rectype} (r : recdata t) : word (reclen t) :=
    match t as t return recdata t -> word (reclen t) with
    | nil => fun _ => WO
    | (_, _) :: _ => fun r =>
      let (v, r') := r in combine (field2word v) (rec2word r')
    end r.

  Fixpoint word2field {ft : fieldtype} : word (fieldlen ft) -> fielddata ft :=
    match ft as ft return (word (fieldlen ft) -> fielddata ft) with
    | WordF n => fun w => w
    | ArrayF ft0 n as ft =>
      (fix word2arrayf n w :=
        match n as n return (word (fieldlen (ArrayF ft0 n)) -> fielddata (ArrayF ft0 n)) with
        | 0 => fun _ => []
        | S n' => fun w0 =>
          (word2field (split1 (fieldlen ft0) _ w0)) ::
          (word2arrayf n' (split2 (fieldlen ft0) _ w0))
        end w) n
    end.

  Fixpoint word2rec (t : rectype) (w : word (reclen t)) : recdata t :=
    match t as t return word (reclen t) -> recdata t with
    | nil => fun _ => tt
    | (_, ft) :: t' => fun w =>
      (word2field (split1 (fieldlen ft) (reclen t') w), 
       word2rec t' (split2 (fieldlen ft) (reclen t') w))
    end w.

  Theorem word2field2word : forall ft w, field2word (@word2field ft w) = w.
  Proof.
    induction ft; intro w.
    reflexivity.
    induction n.
    auto.
    simpl in w. simpl. simpl in IHn. rewrite IHn. rewrite IHft. apply combine_split.
  Qed.

  Theorem word2rec2word : forall t w, rec2word (word2rec t w) = w.
  Proof.
    induction t. auto.
    intro w. destruct a as [n l]. simpl.
    rewrite IHt. rewrite word2field2word. apply combine_split.
  Qed.

  Theorem field2word2field : forall ft v, has_right_length v -> word2field (@field2word ft v) = v.
  Proof.
    induction ft; intro v.
    reflexivity.
    induction n; intro H; simpl in v.
    destruct H. destruct v. reflexivity. discriminate.
    simpl. simpl in IHn. destruct H. destruct v. discriminate.
    rewrite split1_combine. rewrite split2_combine.
    destruct H0.
    rewrite IHft by assumption. rewrite IHn by auto. reflexivity.
  Qed.

  Theorem rec2word2rec : forall t r, has_right_lengths r -> word2rec t (rec2word r) = r.
  Proof.
    induction t; intros r H.
    destruct r. reflexivity.
    destruct a as [n l]. destruct r. simpl.
    rewrite split1_combine. rewrite split2_combine.
    destruct H. rewrite field2word2field by assumption. rewrite IHt by assumption.
    reflexivity.
  Qed.

  Theorem word2field_length : forall ft w, has_right_length (@word2field ft w).
  Proof.
    induction ft; intro w.
    simpl. trivial.
    split. induction n. reflexivity.
    simpl. simpl in IHn. auto.
    induction n; simpl.
    trivial.
    split. apply IHft. apply IHn.
   Qed.

  Theorem word2rec_length : forall t w, has_right_lengths (@word2rec t w).
  Proof.
    induction t; intro w.
    simpl. trivial.
    destruct a. simpl. split.
    apply word2field_length. apply IHt.
  Qed.

  Arguments word2rec : simpl never.
  Arguments rec2word : simpl never.
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
