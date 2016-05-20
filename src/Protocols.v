Require Import CoopConcur.
Require Import Automation.
Import List.

(** Generic structure defining a way to project some smaller set of
state (memory and abstractions) Sigma' out of the global state Sigma.

The no_confusion well-formedness proofs guarantee Sigma' is actually
less than or equal to Sigma. *)
Record StateProj (Sigma:State) (Sigma': State) :=
  defStateProj { memVars: variables (mem_types Sigma) (mem_types Sigma');
                 abstractionVars: variables (abstraction_types Sigma) (abstraction_types Sigma');
                 no_confusion_memVars : NoDup (hmap var_index memVars);
                 no_confusion_abstractionVars : NoDup (hmap var_index abstractionVars) }.

(** Generic proof that delta is a subprotocol of delta', both over the
same global state.

The subprotocol comes from the fact that valid states and transitions
in delta are all valid in delta', so the state machine for delta is a
subset of that for delta'. *)
Definition SubProtocol (Sigma:State) (delta:Protocol Sigma) (delta':Protocol Sigma) :=
  (forall d m s, invariant delta d m s -> invariant delta' d m s) /\
  (forall tid s s', guar delta tid s s' -> guar delta' tid s s').

Theorem rely_subprotocol : forall Sigma (delta delta': Protocol Sigma),
    SubProtocol delta delta' ->
    (forall tid s s', rely delta tid s s' -> rely delta' tid s s').
Proof.
  unfold rely, others, SubProtocol; intuition.
  induction H; try deex; eauto.
Qed.

Record PrivateChanges Sigma PrivateSigma :=
  { privateMemVars :
      variables (mem_types Sigma) (mem_types PrivateSigma);
    privateAbstractionVars :
      variables (abstraction_types Sigma) (abstraction_types PrivateSigma) }.

Definition privateVars {Sigma} {mtypes abstypes} memVars abstractionVars :=
  Build_PrivateChanges Sigma (defState mtypes abstypes) memVars abstractionVars.

Definition SubProtocolUnder Sigma PrivateSigma (private:PrivateChanges Sigma PrivateSigma)
           (delta':Protocol Sigma) (delta:Protocol Sigma) :=
  (forall d m s d' m' s',
      invariant delta d m s ->
      invariant delta' d m s ->
      modified (privateMemVars private) m m' ->
      modified (privateAbstractionVars private) s s' ->
      invariant delta d' m' s') /\
  (forall tid s s',
      modified (privateAbstractionVars private) s s' ->
      guar delta' tid s s' ->
      guar delta tid s s').