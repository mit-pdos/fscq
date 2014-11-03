Require Import Arith List String Omega. 
Require Import Pred.
Require Import Word.

Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Module Rec.
  
  Definition rectype := list (string * nat).
  
  Fixpoint recdata (t : rectype) : Type := 
    match t with
    | nil => unit
    | (_, l) :: t' => word l * recdata t'
    end%type.

  Fixpoint reclen (t : rectype) : nat :=
    match t with
    | nil => 0
    | (_, l) :: t' => l + reclen t'
    end.

  Inductive field_in : rectype -> string -> Prop :=
  | FE : forall t n l, field_in ((n, l) :: t) n
  | FS : forall t n n' l, field_in t n -> field_in ((n', l) :: t) n.

  Lemma empty_field_in : forall n, ~(field_in nil n).
  Proof.
    intros n f. inversion f.
  Qed.

  Lemma field_in_next : forall t n n' l, n' <> n -> field_in ((n',l) :: t) n -> field_in t n.
  Proof.
    intros t n n' l ne f. inversion f; subst.
    contradiction ne. reflexivity.
    apply H3.
  Qed.

  Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : nat :=
    match t as t return (field_in t n -> nat) with
    | nil => fun f => match (empty_field_in f) with end
    | (n0, l0)::_ => fun f =>
      match (string_dec n0 n) with
      | left _ => l0
      | right ne => field_type (field_in_next ne f)
      end
    end f.

  Fixpoint recget (t : rectype) (n : string) (r : recdata t) (p : field_in t n) : word (field_type p) :=
    match t as t return (recdata t -> forall f : field_in t n, word (field_type f)) with
    | [] => fun _ f => match (empty_field_in f) with end
    | (n0, l0) :: t' =>
      fun r f =>
      let (v, r') := r in
      match (string_dec n0 n) as s
        return (word
            match s with
            | left _ => l0
            | right ne => field_type (field_in_next ne f)
            end)
      with
      | left _ => v
      | right ne => recget r' (field_in_next ne f)
      end
    end r p.

(*
  Fixpoint recset (t : rectype) (n : string) (r : recdata t) (p : field_in t n) (v : word (field_type p)) : recdata t.
    destruct p; destruct r.
    + constructor. apply v. assumption.
    + constructor.
      apply u.
      apply recset with (n := n) (p := p).
      apply r.
      apply v.
  Defined.
  
  Print recset.
  *)
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
                    | Some p => word (field_type p)
                    | None => True
                  end) with
      | Some p => recget r p
      | None => I
    end.
  Notation "r :-> n" := (recget' n r) (at level 80).

  (* TODO 
  Definition recset' {t : rectype} {w : nat} (n : string) (r : recdata t) (v : word w) :=
    match fieldp t n as fp
          return (match fp with 
                    | Some p =>
                      match N.eq_dec w (field_type t n p) (*TODO*) with
                        | recdata t
                        |   
                    | None => True
                  end) with
      | Some p => recset r p v
      | None => I
    end.
*)

  Fixpoint rec2word {t : rectype} (r : recdata t) : word (reclen t) :=
    match t as t return recdata t -> word (reclen t) with
    | nil => fun _ => WO
    | (_, _) :: _ => fun r =>
      let (v, r') := r in combine v (rec2word r')
    end r.

  Fixpoint word2rec (t : rectype) (w : word (reclen t)) : recdata t :=
    match t as t return word (reclen t) -> recdata t with
    | nil => fun _ => tt
    | (_, l) :: t' => fun w =>
      (split1 l (reclen t') w, word2rec t' (split2 l (reclen t') w))
    end w.

  Theorem rec2word_word2rec : forall t w, rec2word (word2rec t w) = w.
    induction t. auto.
    intro w. destruct a as [n l]. simpl.
    rewrite IHt. apply combine_split.
  Qed.

  Theorem word2rec_rec2word : forall t r, word2rec t (rec2word r) = r.
    induction t; intro r.
    destruct r. reflexivity.
    destruct a as [n l]. destruct r. simpl.
    rewrite split1_combine. rewrite split2_combine. rewrite IHt.
    reflexivity.
  Qed.

  Definition inodetype : rectype := [("free", 1); ("len", 16); ("block0", 16)].
  Definition inode1 : recdata inodetype := ($1, ($11, ($1677, tt))).
  Parameter inode2 : recdata inodetype.
  Definition foo := Eval compute in inode2 :-> "len".
End Rec.
