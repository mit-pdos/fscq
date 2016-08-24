Require Import CoopConcur.

Inductive TookStep Sigma T : prog Sigma T -> prog Sigma T -> Prop :=
| TookStep_Bind : forall T' (p1: prog Sigma T') p v, TookStep (Bind p1 p) (p v)
| TookStep_Trans : forall p p' p'',
    TookStep p p' ->
    TookStep p' p'' ->
    TookStep p p''.

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

  - apply H.
    eapply pimpl_ok.
    apply H0.
    intros.
    split; eauto.
    (* back where we started *)
    admit.

  - (* induction on TookStep can't be right, it just produces more TookStep
    programs, and this wouldn't even be fixed by changing TookStep_Trans to
    require a right-assocative Bind structure *)
    admit.
Abort.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)