Require Import Prog.

Set Implicit Arguments.

Section ADDRMAP.
  Variable T : Type.

  Definition fupd (m : addr -> T) a v :=
    fun a' => if addr_eq_dec a a' then v else m a'.

  Lemma fupd_same: forall m a a' v,
    a = a' -> fupd m a v a' = v.
  Proof.
    intros; unfold fupd; destruct (addr_eq_dec a a'); congruence.
  Qed.

  Lemma fupd_other: forall m a a' v,
    a <> a' -> fupd m a v a' = m a'.
  Proof.
    intros; unfold fupd; destruct (addr_eq_dec a a'); congruence.
  Qed.
End ADDRMAP.
