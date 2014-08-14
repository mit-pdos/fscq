Require Import Arith.

Set Implicit Arguments.

(** * The programming language *)

Definition addr := nat.
Definition valu := nat.

Parameter donetoken : Set.

Inductive prog :=
| Fail
| Done (t: donetoken)
| Read (a: addr) (rx: valu -> prog)
| Write (a: addr) (v: valu) (rx: unit -> prog).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).

Notation "!" := Read.
Infix "<--" := Write (at level 8).


Definition mem := addr -> option valu.
Definition mem0 : mem := fun _ => Some 0.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if eq_nat_dec a' a then Some v else m a'.

Inductive outcome :=
| Failed
| Finished
| Crashed.

Inductive exec : mem -> prog -> mem -> outcome -> Prop :=
| XFail : forall m, exec m Fail m Failed
| XDone : forall m t, exec m (Done t) m Finished
| XReadFail : forall m a rx,
  m a = None ->
  exec m (Read a rx) m Failed
| XWriteFail : forall m a v rx,
  m a = None ->
  exec m (Write a v rx) m Failed
| XReadOK : forall m a v rx m' out,
  m a = Some v ->
  exec m (rx v) m' out ->
  exec m (Read a rx) m' out
| XWriteOK : forall m a v v0 rx m' out,
  m a = Some v0 ->
  exec (upd m a v) (rx tt) m' out ->
  exec m (Write a v rx) m' out
| XCrash : forall m p, exec m p m Crashed.

Inductive exec_recover : mem -> prog -> prog -> mem -> outcome -> Prop :=
| XRFail : forall m p1 p2 m',
  exec m p1 m' Failed -> exec_recover m p1 p2 m' Failed
| XRFinished : forall m p1 p2 m',
  exec m p1 m' Finished -> exec_recover m p1 p2 m' Finished
| XRCrashed : forall m p1 p2 m' m'' out,
  exec m p1 m' Crashed ->
  exec_recover m' p2 p2 m'' out -> exec_recover m p1 p2 m'' out.

Hint Constructors exec.
Hint Constructors exec_recover.

Theorem upd_eq : forall m a v a',
  a' = a
  -> upd m a v a' = Some v.
Proof.
  intros; subst; unfold upd.
  destruct (eq_nat_dec a a); tauto.
Qed.

Theorem upd_ne : forall m a v a',
  a' <> a
  -> upd m a v a' = m a'.
Proof.
  intros; subst; unfold upd.
  destruct (eq_nat_dec a' a); tauto.
Qed.
