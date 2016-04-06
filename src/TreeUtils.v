Require Import List Arith Omega Bool.
Require Import ListUtils MapUtils.
Require Import DecidableType OrderedType OrderedTypeEx FMapList.

Import ListNotations.

Set Implicit Arguments.


Module Type TreeSig.

  Declare Module KeyT : OrderedType.
  Declare Module TagT : DecidableType.

  Parameter file  : Type.

End TreeSig.


Module Tree (TS : TreeSig).

  Import TS.

  Module Map := FMapList.Raw KeyT.

  Definition key := KeyT.t.
  Definition key_dec := KeyT.eq_dec.

  Definition inum := TagT.t.
  Definition inum_dec := TagT.eq_dec.
  Definition ieq := TagT.eq.
  Definition ieqb i1 i2 :=
    if (inum_dec i1 i2) then true else false.

  Inductive tree :=
  | TFile : inum -> file -> tree
  | TDir  : inum -> Map.t tree -> tree.

  Definition dirents := Map.t tree.

  Definition Inum (t : tree) :=
    match t with
    | TFile i _ => i
    | TDir  i _ => i
    end.

  Definition IsDir (t : tree) :=
    match t with
     | TFile _ _ => False
     | TDir _ _ => True
    end.

  Definition IsFile (t : tree) :=
    match t with
     | TFile _ _ => True
     | TDir _ _ => False
    end.

  Definition dir_file_dec : forall t, { IsDir t } + { IsFile t }.
  Proof.
    destruct t; simpl; tauto.
  Defined.

  Definition isdir_dec : forall t, { IsDir t } + { ~ IsDir t }.
  Proof.
    destruct t; simpl; tauto.
  Defined.


  Fixpoint equal (t : tree) (t' : tree) :=
    let fix subdir_eq e e' :=
        match e, e' with
        | nil, nil => true
        | (k, subt)::l, (k', subt')::l' =>
          if (key_dec k k') then equal subt subt' && subdir_eq l l'
          else false
        | _, _ => false
        end in
    match t, t' with
    | (TFile i _), (TFile i' _) => ieqb i i'
    | (TDir  i ents), (TDir i' ents') =>
        ieqb i i' && subdir_eq ents ents'
    | _, _ => false
    end.

  Fixpoint walk (path : list key) (t : tree) :=
    match path with
    | nil => Some t
    | name :: rest => 
      match t with
      | TFile _ _ => None
      | TDir _ ents =>
        match Map.find name ents with
        | None => None
        | Some subt => walk rest subt
        end
      end
    end.

  Fixpoint update (path : list key) (newt t : tree) :=
    match path with
    | nil => newt
    | name :: rest => 
      match t with
      | TFile _ _ => t
      | TDir inum ents =>
        match Map.find name ents with
        | None =>
          match rest with
          | nil => TDir inum (Map.add name newt ents)
          | _ => t
          end
        | Some subt => 
          let newsubt := update rest newt subt in
          TDir inum (Map.add name newsubt ents)
        end
      end
    end.

  Fixpoint delete (path : list key) (t : tree) :=
    match path with
    | nil => t
    | name :: rest => 
      match t with
      | TFile _ _ => t
      | TDir inum ents =>
        match Map.find name ents with
        | None => t
        | Some subt => 
          match rest with
          | nil => TDir inum (Map.remove name ents)
          | _ =>
            let newsubt := delete rest subt in
            TDir inum (Map.add name newsubt ents)
          end
        end
      end
    end.

End Tree.





Require Import String StringUtils.

Module Sig <: TreeSig.

  Module KeyT := String_as_OT.
  Module TagT := Nat_as_OT.

  Definition file := string.

End Sig.


Module TR := Tree Sig.
Import TR.

Open Scope string_scope.

Definition rt := (TDir 0 [
    ("a", (TFile 1 "AAAA")) ;
    ("b", (TFile 2 "BBBB")) ;
    ("foo", (TDir 3 [
      ("bar", (TFile 4 "bababa")) ;
      ("emp", (TDir 6 [])) ;
      ("zoo", (TFile 5 "zzzzzz"))
    ] ))
]).

Definition st := (TDir 90 [
  ("x", (TFile 91 "xxx")) ;
  ("y", (TFile 92 "yyy"))
]).

(*
Eval compute in (walk   ["foo"; "zoo"] rt).
Eval compute in (update ["foo"; "emp"; "a"] st rt).
Eval compute in (update ["b"] st rt).
Eval compute in (delete ["foo"; "bar"] rt).
Eval compute in (equal rt (delete ["foo"; "emp"] rt)).
*)
