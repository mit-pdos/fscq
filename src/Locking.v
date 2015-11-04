Require Import EventCSL.
Require Import Hlist.

Set Implicit Arguments.

Section Locking.

Variable Mcontents : list Set.
Variable Scontents : list Set.

Notation S := (hlist (fun T:Set => T) Scontents).

Inductive MutexOwner : Set :=
| NoOwner
| Owned (id:ID).

(** given a lock variable and some other variable v, generate a
relation for tid that makes the variable read-only for non-owners. *)
Definition lock_protects (lvar : var Scontents MutexOwner)
           {tv} (v : var Scontents tv) tid (s s': S) :=
  forall owner_tid,
    get lvar s = Owned owner_tid ->
    tid <> owner_tid ->
    get v s' = get v s.

Hint Unfold lock_protects : prog.

Inductive lock_protocol (lvar : var Scontents MutexOwner) (tid : ID) : S -> S -> Prop :=
| NoChange : forall s s', get lvar s  = get lvar s' ->
                     lock_protocol lvar tid s s'
| OwnerRelease : forall s s', get lvar s = Owned tid ->
                         get lvar s' = NoOwner ->
                         lock_protocol lvar tid s s'
| OwnerAcquire : forall s s', get lvar s = NoOwner ->
                         get lvar s' = Owned tid ->
                         lock_protocol lvar tid s s'.

Hint Constructors lock_protocol.

Inductive ghost_lock_invariant
          (lvar : var Mcontents Mutex)
          (glvar : var Scontents MutexOwner)
          (m : M Mcontents) (s : S) : Prop :=
| LockOpen : get lvar m = Open -> get glvar s = NoOwner ->
             ghost_lock_invariant lvar glvar m s
| LockOwned : forall tid, get lvar m = Locked -> get glvar s = Owned tid ->
                     ghost_lock_invariant lvar glvar m s.

Hint Constructors ghost_lock_invariant.

Lemma ghost_lock_owned : forall lvar glvar m s tid,
    ghost_lock_invariant lvar glvar m s ->
    get glvar s = Owned tid ->
    get lvar m = Locked.
Proof.
  inversion 1; congruence.
Qed.

End Locking.