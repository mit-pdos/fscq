Definition bool2nat (v : bool) : nat :=
   match v with
   | true => 1
   | _ => 0
   end.

Definition nat2bool (v : nat) : bool :=
   match v with
   | 1 => true
   | _ => false
   end.

Definition progseq1 {A B:Type} (a:B->A) (b:B) := a b.
Definition progseq2 {A B:Type} (a:B->A) (b:B) := a b.

Notation "a ;; b" := (progseq1 a b)
  (right associativity, at level 60) : fscq_scope.

Notation "ra <- a ; b" := (progseq2 a (fun ra => b))
  (right associativity, at level 60) : fscq_scope.

Delimit Scope fscq_scope with fscq.
