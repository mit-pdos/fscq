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




Fixpoint rep_inner (m: @mem (list string) (list_eq_dec string_dec) dirtree_node) (path: list string) (tree: dirtree) : Prop :=
  match tree with
  | TreeFile n f => m path = Some (DtnFile n f)
  | TreeDir n dirs => m path = Some (DtnDir n (fst (split dirs))) 
                      /\ forall pt, 
                            In pt dirs 
                            -> rep_inner m (path++(fst pt :: nil)) (snd pt)
  end.



Definition splitter {A B C} (f: A -> B -> C) (v: A * B):= f (fst v) (snd v).

Definition child d1 d2 := exists p, In (p, d1) (dirtree_dirents d2).

Hint Constructors Acc.
Hint Unfold child.

Theorem succ_well_founded'': 
  forall n l, Acc child (TreeDir n l).
constructor; intros.
induction (@Acc_intro dirtree child y).
admit.

intro y.

intros.
intro y; induction (dirtree_dirents y) eqn:I.
Focus 2.

Theorem succ_well_founded': forall d, Acc child d.
  destruct d.
  constructor; intros.
  inversion H; simpl in *; exfalso; auto.
  
  destruct H; subst; eauto.
  constructor; intros.
  inversion H; simpl in *; exfalso; auto.
  constructor.
  induction y.
  inversion H; simpl in *.
  Search (In _ _ -> _).
  apply in_split in H0; deex.
  inversion H.
  deex.
  destruct y; simpl in *.
  exfalso; auto.
  generalize dependent p.
  generalize dependent d.
  generalize dependent n.
  induction l; intros.
  exfalso; auto.
  destruct a.
  destruct H.
  inversion H; subst.
  admit.
  eapply Acc_inv.
  eauto.
  simpl.
  constructor; intros.
  destruct y; simpl in *.
  deex; exfalso; auto.
  
  eapply Acc_inv.
  2: eexists; simpl; eauto.
  generalize dependent l.
  induction d.
  admit.
  destruct d1; simpl in *.
  deex; exfalso; auto.
  - constructor; intros.
    inversion H.
    exfalso; auto.
  - generalize dependent n; induction l.
    + unfold parent; constructor; intros.
      deex; exfalso; auto.
    +
  constructor; 
    induction 1.
    admit.
    destruct y; [exfalso; auto |].
    deex.
  - generalize dependent n; induction l; intros.
    + unfold child; constructor; intros; deex; exfalso; auto.
    + specialize (IHl n).
      inversion IHl.
  destruct y; [exfalso; auto |].
  
  deex.
  generalize dependent p.
  generalize dependent d.
  generalize dependent n.
  generalize dependent l.
  induction l; intros; [inversion H |].
  
  destruct H; subst; eauto.
  + constructor; intros.
    destruct y; [exfalso; auto |].
    
    
    
    
   red; intros. unfold child. 

Theorem succ_well_founded: well_founded succ.
  red; intros. *)
  
Definition extend_path (path: list string) (pt: string * dirtree):=
  ((path++(fst pt)::nil)%list, snd pt).

(* Fixpoint depth (d: dirtree) : nat.
  induction d.
  apply 1.
  apply (1 + fold_left max (map depth (snd (split l))) 0).
Qed. *)

Definition lb_height d : nat :=
match d with
| TreeFile _ _ => 0
| TreeDir _ nil => 0
| TreeDir _ _ => 1
end.

(* 
Inductive size (d: dirtree) : nat :=
 
 | SFile : (d = TreeFile _ _) -> size d.
 
 *)
 
Fixpoint height (d: dirtree):=
  match d with
  | TreeFile _ _ => 1
  | TreeDir _ nil => 1
  | TreeDir n (h::t) =>  1 + max (height (snd h)) (height (TreeDir n t))
  end.

Program Fixpoint dir2mem' (path: list string) (tree: dirtree) {measure (lb_height tree)}: @mem (list string) (list_eq_dec string_dec) dirfile :=
match tree with 
| TreeFile _ f => insert empty_mem path f
| TreeDir _ dirs => fold_left (@mem_union (list string) (list_eq_dec string_dec) dirfile)
                    (map (splitter dir2mem')
                        (map (extend_path path) dirs)) empty_mem
end.
   

Definition dir2mem d := dir2mem' (Depth d) nil d.



Fixpoint mem_union_list {AT AEQ V} (m: @mem AT AEQ V) ml :=
match ml with
| nil => m
| h::t => mem_union_list (mem_union m h) t
end.