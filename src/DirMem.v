Require Import Mem.
Require Import DirTreeDef.
Require Import String.
Require Import List.
Require Import Pred.

Set Implicit Parameters.

Definition addr := nat.

Inductive dirtree_node:=
  | DtnFile : addr -> dirfile -> dirtree_node
  | DtnDir  : addr -> list string -> dirtree_node.

Definition splitter {A B C} (f: A -> B -> C) (v: A * B):= f (fst v) (snd v).

Definition extend_path (path: list string) (pt: string * dirtree):=
  ((path++(fst pt)::nil)%list, snd pt).

Fixpoint depth (d: dirtree) : nat.
  induction d.
  apply 1.
  apply (1 + fold_left max (map depth (snd (split l))) 0).
Qed.

(* Fixpoint depth (d: dirtree) :=
  match d with
  | TreeFile _ _ => 1
  | TreeDir _ dirs => 1 + fold_left max (map depth (snd (split dirs))) 0
  end. *)


Fixpoint dir2mem' (depth: nat) (path: list string) (tree: dirtree) : @mem (list string) (list_eq_dec string_dec) dirfile :=
 match depth with
 | O => empty_mem
 | S d' =>
     match tree with 
     | TreeFile _ f => insert empty_mem path f
     | TreeDir _ dirs => fold_left (@mem_union (list string) (list_eq_dec string_dec) dirfile)
                          (map (splitter (dir2mem' d'))
                              (map (extend_path path) dirs)) empty_mem
     end
 end.
   

Definition dir2mem d := dir2mem' (Depth d) nil d.



Fixpoint mem_union_list {AT AEQ V} (m: @mem AT AEQ V) ml :=
match ml with
| nil => m
| h::t => mem_union_list (mem_union m h) t
end.