Require Import ProofIrrelevance.

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

Lemma sig_pi:
  forall {T:Type} {P:T->Prop} (a b:sig P),
  proj1_sig a = proj1_sig b ->
  a = b.
Proof.
  intros; destruct a; destruct b.
  simpl in *; subst.
  replace p with p0; [ auto | apply proof_irrelevance ].
Qed.

Lemma arg_sig_pi:
  forall {T R:Type} {P:T->Prop} (a b:sig P) (M:sig P->R),
  proj1_sig a = proj1_sig b ->
  M a = M b.
Proof.
  intros.
  rewrite (sig_pi a b); auto.
Qed.
