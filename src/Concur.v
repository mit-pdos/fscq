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

Definition file_state := filename -> filedata.
Definition pid := nat.
Record state := {
  StateFS : file_state;
  StateProcs : list (pid * prog);
  StateDone : list pid
}.

Definition upd (m : file_state) (a : filename) (v : filedata) :=
  fun a' => if eq_nat_dec a a' then v else m a.

Lemma upd_eq : forall m a v,
  upd m a v a = v.
Proof.
  unfold upd; intros.
  destruct (eq_nat_dec a a); congruence.
Qed.

Inductive exec : state -> state -> Prop :=
| ExecWrite :
  forall pid file data rx a b fs finished,
  exec (Build_state fs (a ++ (pid, Write file data rx) :: b) finished)
       (Build_state (upd fs file data) (a ++ (pid, rx) :: b) finished)
| ExecExit :
  forall pid a b fs finished,
  exec (Build_state fs (a ++ (pid, Exit) :: b) finished)
       (Build_state fs (a ++ b) (pid :: finished)).

Inductive execstar : state -> state -> Prop :=
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

Lemma in_singleton_list : forall A (a c : list A) (b d : A),
  a ++ b :: c = d :: nil ->
  a = nil /\ b = d /\ c = nil.
Proof.
  destruct a; simpl; intros.
  intuition congruence.
  inversion H.
  apply (apply_eq (@length A)) in H2.
  rewrite app_length in *; simpl in *.
  omega.
Qed.

Lemma in_nil_list : forall A (a c : list A) (b : A),
  a ++ b :: c = nil ->
  False.
Proof.
  intros.
  apply (apply_eq (@length A)) in H.
  rewrite app_length in *; simpl in *.
  omega.
Qed.

Hint Resolve in_nil_list.

Theorem write_to_file_works_easy : forall s s' newpid f d,
  StateProcs s = nil ->
  ~ (In newpid (StateDone s)) ->
  execstar (Build_state (StateFS s)
                        ((newpid, write_to_file f d) :: (StateProcs s))
                        (StateDone s)) s' ->
  In newpid (StateDone s') ->
  StateFS s' f = d.
Proof.
  unfold write_to_file; intros.
  rewrite H in *.

  inversion H1; clear H1; subst; simpl in *; try congruence.
  inversion H3; clear H3; subst; simpl in *.

  apply in_singleton_list in H6. destruct H6. destruct H3. subst; simpl in *.
  inversion H4; clear H4; subst; simpl in *; try congruence.
  inversion H3; clear H3; subst; simpl in *.
  inversion H1; clear H1; subst; simpl in *.

  apply in_singleton_list in H6. destruct H6. destruct H3. inversion H3; congruence.
  apply in_singleton_list in H6. destruct H6. destruct H3. subst; simpl in *.

  inversion H5; clear H5; subst; simpl in *.
  rewrite upd_eq; auto.

  inversion H1; clear H1.
  exfalso; eauto.
  exfalso; eauto.

  apply in_singleton_list in H6. destruct H6. destruct H3. inversion H3.
Qed.
