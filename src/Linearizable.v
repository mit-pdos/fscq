Require Import Mem.
Require Import Pred.
Require Import Locking.

Section Linearizability.

  Variable A:Type.
  Variable AEQ:DecEq A.
  Variable V:A -> Type.

  Definition A':Type := A * BusyFlagOwner.
  Definition AEQ' : DecEq A'.
  Proof.
    unfold DecEq.
    decide equality.
    decide equality.
    decide equality.
  Defined.

  Definition V' : A' -> Type := fun ao =>
                                 let (a, _) := ao in
                                 V a.

  Definition linear_mem := @mem A' AEQ' V'.

  Definition view owner (m: linear_mem) : @mem A AEQ V :=
    fun a => m (a, owner).

  Definition lin_pred (F: @pred A AEQ V) owner : @pred A' AEQ' V' :=
    fun m => F (view owner m).

End Linearizability.

Arguments linear_mem {A AEQ V}.

  Notation "'linearized' mt" :=
    ltac:(
      match mt with
      | @mem ?AT ?AEQ ?V =>
        exact (@linear_mem AT AEQ V)
      | _ => match eval unfold mt in mt with
        | @mem ?AT ?AEQ ?V =>
          exact (@linear_mem AT AEQ V)
        end
      | _ => idtac "linearized" mt "failed; not a mem"
      end) (at level 50, only parsing).

Definition linearized_consistent A AEQ V (m: @linear_mem A AEQ V) (locks: _ -> BusyFlagOwner) : Prop :=
  forall a, match locks a with
       | Owned tid => forall tid',
           tid <> tid' ->
           m (a, Owned tid') = m (a, NoOwner)
       | NoOwner => forall tid,
           m (a, Owned tid) = m (a, NoOwner)
       end.

Local Definition linearized_consistent' A AEQ V (m: @linear_mem A AEQ V) (locks: A -> BusyFlagOwner) : Prop :=
  forall a tid,
  locks a <> Owned tid ->
  m (a, Owned tid) = m (a, NoOwner).

Local Theorem linearized_consistent'_equivalent : forall A AEQ V (m: @linear_mem A AEQ V) locks,
    linearized_consistent m locks <-> linearized_consistent' m locks.
Proof.
  unfold linearized_consistent, linearized_consistent';
  split; intros;
  specialize (H a).
  - destruct (locks a); eauto.
  - destruct (locks a); intros; eauto.
    eapply H; congruence.
    eapply H; congruence.
Qed.