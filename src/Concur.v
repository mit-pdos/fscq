(**
 * Loosely motivating example: bug 4 in section 2.2 of this paper:
 * http://www.cs.columbia.edu/~nieh/pubs/sosp2011_racepro.pdf
 *)

Require Import Arith.
Require Import List.
Require Import Omega.

Set Implicit Arguments.

Definition filenameT := nat.
Definition filedataT := nat.

Inductive progT :=
| Write (file : filenameT) (data : filedataT) (rx : progT)
| Exit.

Inductive proc_state :=
| NeverRan
| Running (p : progT)
| Exited.

Definition file_map := filenameT -> filedataT.
Definition pidT := nat.
Definition proc_map := pidT -> proc_state.
Definition sys_state := (file_map * proc_map)%type.

Definition upd {V : Type} (m : nat -> V) (a : nat) (v : V) :=
  fun a' => if eq_nat_dec a a' then v else m a'.

Lemma upd_eq : forall V m a (v : V),
  upd m a v a = v.
Proof.
  unfold upd; intros.
  destruct (eq_nat_dec a a); congruence.
Qed.

Lemma upd_ne : forall V m a (v : V) a',
  a <> a' ->
  upd m a v a' = m a'.
Proof.
  unfold upd; intros.
  destruct (eq_nat_dec a a'); congruence.
Qed.

Inductive step_pid : file_map -> proc_state -> file_map -> proc_state -> Prop :=
| StepWrite :
  forall file data rx fs ps,
  ps = Running (Write file data rx) ->
  step_pid fs ps (upd fs file data) (Running rx)
| StepExit :
  forall fs ps,
  ps = Running Exit ->
  step_pid fs ps fs Exited.

Inductive step : sys_state -> sys_state -> Prop :=
| StepChoosePid :
  forall pid fmap fmap' pmap ps',
  step_pid fmap (pmap pid) fmap' ps' ->
  step (fmap, pmap) (fmap', upd pmap pid ps').

Inductive star : sys_state -> sys_state -> Prop :=
| StarRefl :
  forall s, star s s
| StarStep :
  forall s0 s1 s2,
  step s0 s1 ->
  star s1 s2 ->
  star s0 s2.

Definition write_to_file (f : filenameT) (d : filedataT) :=
  Write f d Exit.

Lemma apply_eq : forall A B (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  congruence.
Qed.

Inductive will_not_write_to_file : filenameT -> progT -> Prop :=
| WNWTF_exit : forall f, will_not_write_to_file f Exit
| WNWTF_write : forall f f' data rx, f <> f' ->
  will_not_write_to_file f rx ->
  will_not_write_to_file f (Write f' data rx).

Definition wnwtf_except (pid : pidT) (fn : filenameT) (pmap : proc_map) :=
  forall pid' p, pid' <> pid -> pmap pid' = Running p -> will_not_write_to_file fn p.

Lemma wnwtf_monotonic : forall pid fn fs ps fs' ps',
  step (fs, ps) (fs', ps') ->
  wnwtf_except pid fn ps ->
  wnwtf_except pid fn ps'.
Proof.
  inversion 1.
  destruct (eq_nat_dec pid pid0); subst; unfold wnwtf_except; intros.
  - rewrite upd_ne in * by auto.
    eauto.
  - destruct (eq_nat_dec pid0 pid'); subst.
    + rewrite upd_eq in *; subst.
      inversion H1.
      specialize (H0 pid' _ H2 H7).
      inversion H0.
      eauto.
    + rewrite upd_ne in * by auto.
      eauto.
Qed.

Lemma skip_other_pids : forall fmap pmap fmap' pmap' mypid fn,
  step (fmap, pmap) (fmap', pmap') ->
  wnwtf_except mypid fn pmap ->
  ((fmap fn = fmap' fn /\ pmap mypid = pmap' mypid) \/
   (exists ps ps', pmap mypid = ps /\ pmap' = upd pmap mypid ps' /\
    step_pid fmap ps fmap' ps')).
Proof.
  inversion 1.
  destruct (eq_nat_dec pid mypid); subst; intros.
  - right; eauto.
  - left.
    rewrite upd_ne by eauto; intuition.
    inversion H1; subst; eauto.
    unfold wnwtf_except in *.
    specialize (H0 pid _ n H2).
    inversion H0.
    rewrite upd_ne; eauto.
Qed.

Theorem write_to_file_works : forall fmap pmap fmap' pmap' newpid fn data,
  pmap newpid = NeverRan ->
  wnwtf_except newpid fn pmap ->
  star (fmap, upd pmap newpid (Running (write_to_file fn data)))
       (fmap', pmap') ->
  pmap' newpid = Exited ->
  fmap' fn = data.
Proof.
  intros.
Admitted.
