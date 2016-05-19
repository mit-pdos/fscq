Require Import EventCSL.
Require Import Automation.
Require Export Locking.
Require Export Linearizable2.

Definition linearized_consistent A (AEQ: DecEq A) V (locks: Locks A)
           (m: @linear_mem A AEQ V) : Prop :=
forall a, match m a with
          | Some (v, v') =>
            match locks a with
            | Owned _ => True
            | NoOwner => v = v'
            end
          | None => True
          end.

Definition linear_rel A (AEQ: DecEq A) V tid (locks locks': Locks A)
  (m m': @linear_mem A AEQ V) :=
  (* lock protocol *)
  (forall a, lock_transition tid (locks a) (locks' a)) /\
  (* lock protection *)
  (forall a tid', locks a = Owned tid' ->
  tid <> tid' ->
  m' a = m a).

Theorem linear_rel_refl : forall A AEQ V tid locks (m: @linear_mem A AEQ V),
  linear_rel tid locks locks m m.
Proof.
  unfold linear_rel; intuition.
Qed.

Theorem linear_rel_trans : forall A AEQ V tid locks locks' locks''
  (m m' m'': @linear_mem A AEQ V),
  linear_rel tid locks locks' m m' ->
  linear_rel tid locks' locks'' m' m'' ->
  linear_rel tid locks locks'' m m''.
Proof.
  unfold linear_rel; intros; intuition;
    specialize_all A.
  - eapply lock_transition_trans; eauto.

  - eapply eq_trans with (y := m' a); eauto.
    inversion H1; subst; try intuition congruence.
    eapply (H3 tid'); (congruence || eauto).
Qed.

Theorem linearized_consistent_upd : forall A AEQ V (m: @linear_mem A AEQ V)
  locks a tid v,
  locks a = Owned tid ->
  linearized_consistent locks m ->
  linearized_consistent locks (linear_upd m a v).
Proof.
  unfold linearized_consistent, linear_upd; intros;
    learn_all A.
  destruct matches;
  destruct (AEQ a a0); subst;
    autorewrite with upd in *;
    cleanup.
Qed.

Theorem linearized_consistent_release : forall A AEQ V (m: @linear_mem A AEQ V)
  locks a,
  linearized_consistent locks m ->
  locks a = NoOwner ->
  linearized_consistent locks (lin_release m a).
Proof.
  unfold linearized_consistent, lin_release; intros.
  specialize_all A.
  destruct matches;
  destruct (AEQ a a0); subst;
  autorewrite with upd in *;
  cleanup.
Qed.

Hint Rewrite lin_release_eq linear_upd_eq using (solve [ auto ] ) : lin_upd.
Hint Rewrite lin_release_view_eq linear_upd_view_eq using (solve [ auto ] ) : lin_upd.
Hint Rewrite lin_release_neq linear_upd_neq using (solve [ auto ] ) : lin_upd.

Theorem linear_rel_upd :
  forall tid A AEQ V
    locks locks' (m m': @linear_mem A AEQ V)
    a v,
    locks a = Owned tid ->
    linear_rel tid locks locks' m m' ->
    linear_rel tid locks locks'
               m (linear_upd m' a v).
Proof.
  unfold linear_rel, linear_upd; intuition.
  destruct (AEQ a a0); try congruence.
  destruct matches; autorewrite with upd; eauto.
Qed.

Lemma linear_upd_same_domain : forall A AEQ V (m: @linear_mem A AEQ V) a v',
    same_domain m (linear_upd m a v').
Proof.
  unfold same_domain, subset, linear_upd; intuition.
  destruct (AEQ a a0); subst; intros;
  destruct matches;
  autorewrite with upd;
  eauto.

  destruct (AEQ a a0); subst; intros;
  destruct matches in *;
  autorewrite with upd in *;
  eauto.
Qed.