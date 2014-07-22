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

Lemma nat2bool2nat:
  forall b,
  nat2bool (bool2nat b) = b.
Proof.
  destruct b; auto.
Qed.
Hint Rewrite nat2bool2nat.

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

Definition setidx {K: Type} {V: Type}
                  (eq: forall (a b:K), {a=b}+{a<>b})
                  (db: K->V) (k: K) (v: V) :=
  fun x: K => if eq x k then v else db x.

Definition setidxsig {K: Type} {V: Type} {KP: K->Prop}
                     (eq: forall (a b:K), {a=b}+{a<>b})
                     (db: (sig KP) -> V) (k: K) (v: V) :=
  fun x: (sig KP) => if eq (proj1_sig x) k then v else db x.

Lemma setidx_same:
  forall K V eq db (k:K) (v:V),
  setidx eq db k v k = v.
Proof.
  intros. unfold setidx. destruct (eq k k). auto. destruct n. auto.
Qed.

Lemma setidx_other:
  forall K V eq db (k k':K) (v:V),
  k <> k' ->
  setidx eq db k v k' = db k'.
Proof.
  intros. unfold setidx. destruct (eq k' k). destruct H. auto. auto.
Qed.
