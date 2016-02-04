Require Import EventCSL.

Set Implicit Arguments.

Section Locking.

Variable Mcontents : list Type.
Variable Scontents : list Type.

Inductive BusyFlagOwner : Set :=
| NoOwner
| Owned (id:ID).

(** given a lock variable and some other variable v, generate a
relation for tid that makes the variable read-only for non-owners. *)
Definition lock_protects (lvar : S Scontents -> BusyFlagOwner)
           {tv} (v : S Scontents -> tv) tid (s s': S Scontents) :=
  forall owner_tid,
    lvar s = Owned owner_tid ->
    tid <> owner_tid ->
    v s' = v s.

Hint Unfold lock_protects : prog.

Inductive lock_protocol (lvar : S Scontents -> BusyFlagOwner) (tid : ID) :
  S Scontents -> S Scontents -> Prop :=
| NoChange : forall s s', lvar s  = lvar s' ->
                     lock_protocol lvar tid s s'
| OwnerRelease : forall s s', lvar s = Owned tid ->
                         lvar s' = NoOwner ->
                         lock_protocol lvar tid s s'
| OwnerAcquire : forall s s', lvar s = NoOwner ->
                         lvar s' = Owned tid ->
                         lock_protocol lvar tid s s'.

Hint Constructors lock_protocol.

Inductive ghost_lock_invariant
          (lvar : M Mcontents -> BusyFlag)
          (glvar : S Scontents -> BusyFlagOwner)
          (m : M Mcontents) (s : S Scontents) : Prop :=
| LockOpen : lvar m = Open -> glvar s = NoOwner ->
             ghost_lock_invariant lvar glvar m s
| LockOwned : forall tid, lvar m = Locked -> glvar s = Owned tid ->
                     ghost_lock_invariant lvar glvar m s.

Hint Constructors ghost_lock_invariant.

Lemma ghost_lock_owned : forall lvar glvar m s tid,
    ghost_lock_invariant lvar glvar m s ->
    glvar s = Owned tid ->
    lvar m = Locked.
Proof.
  inversion 1; congruence.
Qed.

Theorem ghost_lock_inv_preserved :
  forall lvar glvar m s m' s',
  ghost_lock_invariant lvar glvar m s ->
  lvar m = lvar m' ->
  glvar s = glvar s' ->
  ghost_lock_invariant lvar glvar m' s'.
Proof.
  inversion 1; intros;
  repeat match goal with
       | [ H: ?v ?m = ?x, H': ?v ?m = ?y |- _ ] =>
          lazymatch goal with
          | [ Heq: x = y |- _ ] => fail
          | _ => assert (x = y) by congruence
          end
        end; eauto.
Qed.

End Locking.