Require Import Arith List String Omega. 
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.

Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Module Rec.
  
  Definition rectype := list (string * nat).
  
  Fixpoint recdata (t : rectype) : Type := 
    match t with
      | nil => unit
      | (_, n) :: t' => word n * recdata t'
    end%type.

  Inductive field_in : rectype -> string -> Prop :=
  | FE : forall t n w, field_in ((n, w) :: t) n
  | FS : forall t n n' w, field_in t n -> field_in ((n',w) :: t) n.

  Lemma empty_field_in : forall n, ~(field_in nil n).
  Proof.
    intros n f. inversion f.
  Qed.

  Lemma field_in_next : forall t n n' w, n' <> n -> field_in ((n',w) :: t) n -> field_in t n.
  Proof.
    intros t n n' w ne f. inversion f; subst.
    contradiction ne. reflexivity.
    apply H3.
  Qed.

  Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : nat :=
    match t as t return (field_in t n -> nat) with
    | nil => fun f => match (empty_field_in f) with end
    | (n0, w0)::_ => fun f =>
      match (string_dec n0 n) with
      | left _ => w0
      | right ne => field_type (field_in_next ne f)
      end
    end f.

  Fixpoint recget (t : rectype) (n : string) (r : recdata t) (p : field_in t n) : word (field_type p) :=
    match t as t return (recdata t -> forall f : field_in t n, word (field_type f)) with
    | [] => fun _ f => match (empty_field_in f) with end
    | (n0, w0) :: t' =>
      fun r f =>
      let (v, r') := r in
      match (string_dec n0 n) as s
        return (word
            match s with
            | left _ => w0
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
    | (n0, w0) :: t' =>
      match (string_dec n0 n) with
      | left e =>
          eq_rec_r
            (fun n1 => option (field_in ((n1, w0) :: t') n))
            (Some (FE t' n w0)) e
      | right _ =>
        match (fieldp t' n) with
        | Some f => Some (FS n0 w0 f)
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
  
  Notation "r :-> n" := (recget' n r) (at level 80).
  
  Definition inodetype : rectype := [("free", 1); ("len", 16); ("block0", 16)].
  Definition inode1 : recdata inodetype := ($1, ($11, ($1677, tt))).
  Parameter inode2 : recdata inodetype.
  Definition foo := Eval compute in inode2 :-> "len".
  Extraction Language Haskell.
  Extraction foo.
End Rec.
