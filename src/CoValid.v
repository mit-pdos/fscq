Require Import CoopConcur.

Inductive TookStep Sigma T : prog Sigma T -> prog Sigma T -> Prop :=
| TookStep_Bind : forall T' (p1: prog Sigma T') p v, TookStep (Bind p1 p) (p v).

Transparent valid.

(* for debugging purposes, override {{p; _}} notation to one that shows the
entire program *)
Notation "{{{ p ; p' }}}" := (valid _ _ _ (Bind p p')).

Theorem covalid : forall Sigma (delta: Protocol Sigma) tid T (p: prog Sigma T)
                    (pre: donecond T -> DISK -> hashmap -> memory _ -> abstraction _ -> abstraction _ -> Prop)
                    p' pre',
    TookStep p p' ->
    (valid delta tid pre' p' -> valid delta tid pre p) ->
    valid delta tid (fun done d hm m s_i s =>
                   pre' done d hm m s_i s /\
                   valid delta tid pre p) p' ->
    valid delta tid pre p.
Proof.
  inversion 1; subst.
  rename p0 into p.

  unfold valid; intros.
  remember (x <- p1; p x).
  induction H3; try congruence;
    subst;
    try solve [ inversion H3 ].
  (* how do we deal with p0 = ... obligations in the inductive hypotheses?
    those make it impossible to apply them *)
  admit.
  inversion Heqp0.
  match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
    pose proof (EqdepFacts.eq_sigT_fst H); subst
  end; repeat sigT_eq; cleanup.
  admit.
Abort.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)