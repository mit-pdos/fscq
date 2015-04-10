Lemma master_key : unit. Proof. exact tt. Qed.

Definition locked {A} := let 'tt := master_key in fun x : A => x.

Definition unlock {A} : locked A -> A.
  unfold locked; destruct master_key; intro; assumption.
Defined.

Definition lock {A} : A -> locked A.
  unfold locked; destruct master_key; intro; assumption.
Defined.

Lemma locked_eq :
  forall A (x : A), locked x = x.
Proof.
  unfold locked; destruct master_key; auto.
Qed.
