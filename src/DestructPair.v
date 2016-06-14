Set Implicit Arguments.

Theorem destruct_two : forall A B (p : A * B),
  exists a b, p = (a, b).
Proof.
  intros; destruct p; eauto.
Qed.

Theorem destruct_four : forall A B C D (p : A * B * C * D),
  exists a b c d, p = (a, b, c, d).
Proof.
  intros; do 3 destruct p; eauto.
Qed.

Theorem destruct_eight : forall A B C D E F G H (p : A * B * C * D * E * F * G * H),
  exists a b c d e f g h, p = (a, b, c, d, e, f, g, h).
Proof.
  intros; do 7 destruct p; eauto 10.
Qed.

Theorem x : forall (x : unit * bool * nat * list nat * option nat * nat * unit * bool * bool * nat * unit * bool),
  x = x.
Proof.
  intros.
  pose proof (destruct_eight x) as Hd. do 8 destruct Hd as [? Hd]. subst.
  pose proof (destruct_four x0) as Hd. do 4 destruct Hd as [? Hd]. subst.
  pose proof (destruct_two x) as Hd. do 2 destruct Hd as [? Hd]. subst.
Abort.
