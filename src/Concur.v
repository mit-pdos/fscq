(**
 * Loosely motivating example: bug 4 in section 2.2 of this paper:
 * http://www.cs.columbia.edu/~nieh/pubs/sosp2011_racepro.pdf
 *)

Require Import Arith.
Require Import List.
Require Import Omega.

Set Implicit Arguments.

Definition filename := nat.
Definition filedata := nat.

Inductive prog :=
| Write (file : filename) (data : filedata) (rx : prog)
| Exit.

Inductive proc_state :=
| NeverRan
| Running (p : prog)
| Exited.

Definition f_state := filename -> filedata.
Definition pid := nat.
Definition p_state := pid -> proc_state.
Definition sys_state := (f_state * p_state)%type.

Definition upd {V : Type} (m : nat -> V) (a : nat) (v : V) :=
  fun a' => if eq_nat_dec a a' then v else m a.

Lemma upd_eq : forall V m a (v : V),
  upd m a v a = v.
Proof.
  unfold upd; intros.
  destruct (eq_nat_dec a a); congruence.
Qed.

Inductive exec : sys_state -> sys_state -> Prop :=
| ExecWrite :
  forall pid file data rx fs ps,
  ps pid = Running (Write file data rx) ->
  exec (fs, ps) (upd fs file data, upd ps pid (Running rx))
| ExecExit :
  forall pid fs ps,
  ps pid = Running Exit ->
  exec (fs, ps) (fs, upd ps pid Exited).

Inductive execstar : sys_state -> sys_state -> Prop :=
| ExecStarRefl :
  forall s, execstar s s
| ExecStarStep :
  forall s0 s1 s2,
  exec s0 s1 ->
  execstar s1 s2 ->
  execstar s0 s2.

Definition write_to_file (f : filename) (d : filedata) :=
  Write f d Exit.

Lemma apply_eq : forall A B (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  congruence.
Qed.

Inductive will_not_write_to_file : filename -> prog -> Prop :=
| WNWTF_exit : forall f, will_not_write_to_file f Exit
| WNWTF_write : forall f f' data rx, f <> f' ->
  will_not_write_to_file f rx ->
  will_not_write_to_file f (Write f' data rx).

Theorem write_to_file_works_easy : forall fs ps fs' ps' newpid fn data,
  (forall pid, exists p, ps pid = Running p -> will_not_write_to_file fn p) ->
  ps newpid = NeverRan ->
  execstar (fs, upd ps newpid (Running (write_to_file fn data))) (fs', ps') ->
  ps' newpid = Exited ->
  fs' fn = data.
Proof.
  intros.
Admitted.
