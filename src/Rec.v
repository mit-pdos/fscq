Require Import Arith List String Omega. 
(*Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.*)

Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

Module Rec.
  
  Inductive vec : Type -> nat -> Type :=
  | V0 : forall t, vec t 0
  | VS : forall t, t -> forall n, vec t n -> vec t (S n).
  
  Inductive un : nat -> Type :=
  | U0 : un 0
  | US : forall n, un n -> un (S n).
  
  Definition rectype := list (string * nat).
  
  Fixpoint recdata (t : rectype) : Type := 
    match t with
      | nil => unit
      | (_, n) :: t' => un n * recdata t'
    end%type.
  
  Fixpoint mkun n : un n :=
    match n with
      | 0 => U0
      | S n => US (mkun n)
    end.
  
  (* TODO should be Prop *)
  Inductive field_in : rectype -> string -> Type :=
  | FE : forall t n w, field_in ((n, w) :: t) n
  | FS : forall t n n' w, field_in t n -> field_in ((n',w) :: t) n.
  
  Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : nat :=
    match f with
      | FE _ _ w => w
      | FS _ _ _ _ f => field_type f
    end.
  
  Fixpoint recget (t : rectype) (n : string) (r : recdata t) (p : field_in t n) : un (field_type p).
    destruct p.
    destruct r.    
    + assumption.
    + apply recget with (t := t) (n := n).
      destruct r.
      assumption.
  Defined.

  Fixpoint recset (t : rectype) (n : string) (r : recdata t) (p : field_in t n) (v : un (field_type p)) : recdata t.
    destruct p; destruct r.
    + constructor. apply v. assumption.
    + constructor.
      apply u.
      apply recset with (n := n) (p := p).
      apply r.
      apply v.
  Defined.
  
  Print recset.
  
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
                    | Some p => un (field_type p)
                    | None => True
                  end) with
      | Some p => recget r p
      | None => I
    end.
  
  (* TODO 
  Definition recset' {t : rectype} {w : nat} (n : string) (r : recdata t) (v : un w) :=
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
  Definition inode1 : recdata inodetype := (mkun 1, (mkun 16, (mkun 16, tt))).

  Definition foo : un 16 := inode1 :-> "len".
End Rec.
