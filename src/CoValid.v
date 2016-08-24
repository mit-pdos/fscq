Require Import CoopConcur.

Inductive TookStep Sigma T : prog Sigma T -> prog Sigma T -> Prop :=
| TookStep_Bind : forall T' (p1: prog Sigma T') p v, TookStep (Bind p1 p) (p v)
| TookStep_Trans : forall p p' p'',
    TookStep p p' ->
    TookStep p' p'' ->
    TookStep p p''.

Transparent valid.

Notation "{{{ p ; p' }}}" := (valid _ _ _ (Bind p p')).

Theorem covalid : forall Sigma (delta: Protocol Sigma) tid T (p: prog Sigma T)
                    (pre: donecond T -> DISK -> memory _ -> abstraction _ -> abstraction _ -> Prop)
                    p' pre',
    TookStep p p' ->
    (valid delta tid pre' p' -> valid delta tid pre p) ->
    valid delta tid (fun done d m s_i s =>
                   pre' done d m s_i s /\
                   valid delta tid pre p) p' ->
    valid delta tid pre p.
Proof.
  induction 1; intros.

  - unfold valid; intros.
    remember (x <- p1; p x).
    induction H2; try congruence;
      subst;
      try solve [ inversion H2 ].
    (* how do we deal with p0 = ... obligations in the inductive hypotheses?
    those make it impossible to apply them *)
    admit.
    inversion Heqp0.
    pose proof (EqdepFacts.eq_sigT_fst H5); subst.
    repeat sigT_eq; cleanup.
    admit.
  - (* perhaps induction on TookStep should occur within the induction on exec?
    or maybe we need an induction on exec that allows skipping the binding
    structure captured in TookStep? *)
    admit.
Abort.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)