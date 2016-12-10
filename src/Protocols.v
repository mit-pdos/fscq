Require Import CoopConcur.
Require Import Automation.
Require Import Equality.
Import List.

Section Protocols.

  Variables (Sigma Sigma':State).

  (** Generic structure defining a way to project some smaller set of state
      (memory and abstractions) Sigma' out of the global state Sigma.

      The no_confusion well-formedness proofs guarantee Sigma' is actually less
      than or equal to Sigma. *)
  Record StateProj :=
    defStateProj { memVars: variables (mem_types Sigma) (mem_types Sigma');
                   abstractionVars: variables (abstraction_types Sigma) (abstraction_types Sigma');
                   no_confusion_memVars : NoDup (hmap var_index memVars);
                   no_confusion_abstractionVars : NoDup (hmap var_index abstractionVars) }.

  Variable (proj: StateProj).

  (** * Projections into smaller state. *)

  Definition pi__m (m: memory Sigma) : memory Sigma'.
    destruct proj; unfold memory in *; simpl in *.
    (* not relevant to the recursion *)
    clear no_confusion_memVars0 no_confusion_abstractionVars0.
    induction memVars0.
    - apply HNil.
    - apply HCons; hnf in *.
      apply (Hlist.get b m).
      apply IHmemVars0.
  Defined.

  Definition pi__s (m: abstraction Sigma) : abstraction Sigma'.
    destruct proj; unfold abstraction in *; simpl in *.
    clear no_confusion_memVars0 no_confusion_abstractionVars0.
    induction abstractionVars0.
    - apply HNil.
    - apply HCons; hnf in *.
      apply (Hlist.get b m).
      apply IHabstractionVars0.
  Defined.

  (** Generic statement that a smaller delta' is a subprotocol of delta.

      Transitions in delta correspond to transitions in delta', projected onto
      Sigma'. *)
  Definition SubProtocolPi delta delta' :=
    (forall d hm m s, invariant delta d hm m s -> invariant delta' d hm (pi__m m) (pi__s s)) /\
    (forall tid s s', guar delta tid s s' -> guar delta' tid (pi__s s) (pi__s s')).

  Theorem rely_subprotocol_pi : forall delta delta',
      SubProtocolPi delta delta' ->
      (forall tid s s', rely delta tid s s' -> rely delta' tid (pi__s s) (pi__s s')).
  Proof.
    unfold rely, others, SubProtocolPi; intuition.
    induction H; try deex; eauto.
  Qed.

  Definition SubProtocol (delta delta': Protocol Sigma) :=
    (forall d hm m s, invariant delta d hm m s -> invariant delta' d hm m s) /\
    (forall tid s s', guar delta tid s s' -> guar delta' tid s s').

  Theorem rely_subprotocol : forall delta delta',
      SubProtocol delta delta' ->
      (forall tid s s', rely delta tid s s' -> rely delta' tid s s').
  Proof.
    unfold rely, others, SubProtocol; intuition.
    induction H; try deex; eauto.
  Qed.

  (** * Injections into the global state. *)

  (* TODO: factor out Hlist.set_all *)
  Definition inj__m (m: memory Sigma) (m': memory Sigma') : memory Sigma.
    destruct proj; unfold memory in *; simpl in *.
    clear no_confusion_memVars0 no_confusion_abstractionVars0.
    induction memVars0; hnf in *.
    - exact m.
    - eapply (Hlist.set b (get HFirst m')).
      exact (IHmemVars0 (htail m')).
  Defined.

  Definition inj__s (s: abstraction Sigma) (s': abstraction Sigma') : abstraction Sigma.
    destruct proj; unfold abstraction in *; simpl in *.
    clear no_confusion_memVars0 no_confusion_abstractionVars0.
    induction abstractionVars0; hnf in *.
    - exact s.
    - eapply (Hlist.set b (get HFirst s')).
      exact (IHabstractionVars0 (htail s')).
  Defined.

  Definition InjectProtocol delta delta' :=
    (forall d hm m s d' hm' m' s', invariant delta d hm m s ->
                       invariant delta' d' hm' m' s' ->
                       invariant delta d hm (inj__m m m') (inj__s s s')) /\
    (forall tid s0 s s', guar delta' tid s s' ->
                    guar delta tid (inj__s s0 s) (inj__s s0 s')).

  Theorem rely_injectprotocol : forall delta delta',
      InjectProtocol delta delta' ->
      (forall tid s0 s s', rely delta' tid s s' ->
                      rely delta tid (inj__s s0 s) (inj__s s0 s')).
  Proof.
    unfold rely, others, InjectProtocol; intuition.
    induction H; try deex; eauto.
  Qed.

End Protocols.

Arguments memVars {Sigma Sigma'} _.
Arguments abstractionVars {Sigma Sigma'} _.

Theorem inj__m_get : forall Sigma Sigma' (proj: StateProj Sigma Sigma') m m'
                       t (v_index: var (mem_types Sigma') t),
    pi__m proj (inj__m proj m m') = m'.
Proof.
  cbn; intros.
  destruct proj; unfold memory in *; simpl.
  induction memVars0; simpl.
  - now inversion v_index.
  - rewrite get_set.
    apply hlist_get_extensional; intros.
    dependent induction m0; cbn;
      rewrite ?get_first, ?get_next;
      eauto.
Abort.

Module Type GlobalState.
  Parameter Sigma:State.
End GlobalState.

Module Type GlobalProtocol.
  Declare Module St : GlobalState.
  Definition Sigma := St.Sigma.
  Parameter delta:Protocol Sigma.
End GlobalProtocol.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)
