Require Import CoopConcur.
Require Import Automation.
Require Import LinearizableLocking.
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

(* This constraint on R seems to be part of a general family of
protocols associated with a lock. Eventually would like the whole set
of locking definitions to be re-designed in light of how it is
actually used, but the changes are likely to be sweeping and some
things about lock usage remain unclear (eg, it would be nice to commit
to all locks being part of nat -> lock families, but this precludes,
eg, addr -> lock, string -> lock and singleton unit -> lock
families). *)

(* unfortunately this definition is dependent on an instantiation of
  Locks - it could be defined by the Lock functor, but then Locks.v
  would have to import linearizability *)

(** Predicate asserting the relation R ignores changes to locked
  addresses in the resource r_var (a linear_mem) protected by the set
  of locks in lock_var *)

Definition respects_lock Sigma (R: TID -> Relation Sigma)
           (lock_var: member (Locks addr) (abstraction_types Sigma)) V
           (r_var: member (@linear_mem addr (@weq _) V) (abstraction_types Sigma)) :=
  forall tid (s s': abstraction Sigma),
  forall a tid',
    get lock_var s a = Owned tid' ->
    tid <> tid' ->
    forall (v': V a),
      R tid s s' ->
      R tid (set r_var (linear_upd (get r_var s) a v') s)
        (set r_var (linear_upd (get r_var s') a v') s').
