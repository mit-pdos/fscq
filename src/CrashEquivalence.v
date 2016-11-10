Require Import Mem.
Require Import Pred PredCrash.

(* This is a distilled version of the XCRASH condition. c is the crash invariant
quantified over by the whole spec, crashinv is the program's intended crash
invariant; xcrash crashinv c is intended to be true for acceptable c's. *)
Definition xcrash (crashinv c: rawpred) :=
    forall c', crash_xform c' =p=> crash_xform crashinv ->
                             c' =p=> c.

(* Here is a simple statement that I think captures crash equivalence. *)
Definition crash_equiv1 (crashinv c: rawpred) :=
  forall d d',
    crashinv d -> possible_crash d d' ->
    exists d0, c d0 /\ possible_crash d0 d'.

(* And here's an even simpler way to express good c's relative to crash
equivalence. Note the similarity to the definition without crash equivalence,
which is crash inv =p=> c. *)
Definition crash_equiv2 (crashinv c: rawpred) :=
  crash_xform crashinv =p=> crash_xform c.

Hint Unfold xcrash crash_equiv1 crash_equiv2 : crashequiv.

Theorem xcrash_to_crash_equiv1 : forall crashinv c,
    xcrash crashinv c ->
    crash_equiv1 crashinv c.
Proof.
  autounfold with crashequiv.
  intros.
  specialize (H _ (pimpl_refl _)).
  eexists; intuition eauto.
Qed.

Theorem crash_equiv1_to_crash_equiv2 : forall crashinv c,
    crash_equiv1 crashinv c <->
    crash_equiv2 crashinv c.
Proof.
  autounfold with crashequiv.
  unfold crash_xform.
  split; intros.
  - intros d ?; deex.
    pose proof (H _ _ H1 H2); deex.
    eexists; intuition eauto.
  - specialize (H d'); simpl in H.
    edestruct H; eauto.
Qed.

Theorem crash_equivalence_statements : forall crashinv c,
    crash_equiv1 crashinv c ->
    xcrash crashinv c.
Proof.
  autounfold with crashequiv; intros.
  intros d ?.
  unfold pimpl, crash_xform in H0.
  pose proof (H0 d).
  match type of H2 with
  | ?P -> _ => assert P as Hp
  end.
  eexists; split; eauto.
  apply possible_crash_refl.
  (* ok, that shouldn't have happened *)
  admit.
  intuition.
  clear Hp.
  deex.
  pose proof (H _ _ H3 H4); deex.
  (* ok, this is definitely wrong *)
  admit.
Abort.