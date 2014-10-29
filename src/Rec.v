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
  
  Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : nat.
    destruct t.
    contradiction empty_field_in with (n := n).
    destruct p.
    destruct (string_dec s n).
    apply n0.
    apply (field_type t n). apply field_in_next with (n' := s) (w := n0); assumption.
  Defined.
  
  Fixpoint recget (t : rectype) (n : string) (r : recdata t) (p : field_in t n) : word (field_type p).
    destruct t.
    contradiction empty_field_in with (n := n).
    destruct p0.
    simpl in r.
    destruct r.
    simpl.
    destruct (string_dec s n).
    apply w.
    apply (recget t n r).
  Defined.

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
  Definition fieldp (t : rectype) (n : string) : option (field_in t n).
    induction t as [| p t'].
    apply None.
    destruct p as [n0 w0].
    destruct (string_dec n0 n).
    rewrite e.
    apply Some.
    constructor.
    destruct IHt'.
    constructor.
    constructor.
    assumption.
    apply None.
  Defined.

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
