(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Dependent list types presented in Chapter 9 *)

Require Import Arith List CpdtTactics.

Set Implicit Arguments.

Section ilist.
  Variable A : Type.

  Inductive ilist : nat -> Type :=
  | INil : ilist O
  | ICons : forall n, A -> ilist n -> ilist (S n).

  Definition hd n (ls : ilist (S n)) :=
    match ls in ilist n' return match n' with
                                  | O => unit
                                  | S _ => A
                                end with
      | INil => tt
      | ICons _ x _ => x
    end.
  Definition tl n (ls : ilist (S n)) :=
    match ls in ilist n' return match n' with
                                  | O => unit
                                  | S n => ilist n
                                end with
      | INil => tt
      | ICons _ _ ls' => ls'
    end.

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
      | INil => fun idx =>
        match idx in fin n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | ICons _ x ls' => fun idx =>
        match idx in fin n' return (fin (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.

  Section everywhere.
    Variable x : A.

    Fixpoint everywhere (n : nat) : ilist n :=
      match n with
        | O => INil
        | S n' => ICons x (everywhere n')
      end.
  End everywhere.

  Section singleton.
    Variables x default : A.

    Fixpoint singleton (n m : nat) : ilist n :=
      match n with
        | O => INil
        | S n' =>
          match m with
            | O => ICons x (everywhere default n')
            | S m' => ICons default (singleton n' m')
          end
      end.
  End singleton.

  Section map2.
    Variable f : A -> A -> A.

    Fixpoint map2 n (il1 : ilist n) : ilist n -> ilist n :=
      match il1 in ilist n return ilist n -> ilist n with
        | INil => fun _ => INil
        | ICons _ x il1' => fun il2 => ICons (f x (hd il2)) (map2 il1' (tl il2))
      end.
  End map2.

  Section fold.
    Variable B : Type.
    Variable f : A -> B -> B.
    Variable i : B.

    Fixpoint foldr n (il : ilist n) : B :=
      match il with
        | INil => i
        | ICons _ x il' => f x (foldr il')
      end.
  End fold.
End ilist.

Implicit Arguments INil [A].
Implicit Arguments First [n].

Section imap.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint imap n (il : ilist A n) : ilist B n :=
    match il with
      | INil => INil
      | ICons _ x il' => ICons (f x) (imap il')
    end.
End imap.

