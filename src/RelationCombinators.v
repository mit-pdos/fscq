Require Export Star.

Set Implicit Arguments.

(* More combinators for relations *)

Definition chain (S:Type) (R1 R2: S -> S -> Prop) : S -> S -> Prop :=
  fun s s'' =>
  exists (s':S), R1 s s' /\ R2 s' s''.

Definition applied S (f: S -> S) : S -> S -> Prop :=
  fun s s' =>
  s' = f s.

(* hints and associated proofs for chain/applied combinators *)
Lemma chain_trans : forall S (s s' s'':S) (R1 R2: _ -> _ -> Prop),
  R1 s s' ->
  R2 s' s'' ->
  chain R1 R2 s s''.
Proof.
  unfold chain; eauto.
Qed.

Hint Resolve chain_trans.

Lemma applied_def : forall S (s s':S) f,
  s' = f s ->
  applied f s s'.
Proof.
  unfold applied; auto.
Qed.

Hint Resolve applied_def.