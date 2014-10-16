Require Import Arith.
Require Import Word.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

(** * The programming language *)

Module Type VALULEN.
  Parameter valulen : nat.
  Axiom valulen_is: valulen = 4096. (* 512 bytes *)
End VALULEN.

Module Valulen : VALULEN.
  Definition valulen := 4096.
  Theorem valulen_is: valulen = 4096.
  Proof.
    auto.
  Qed.
End Valulen.

Definition addrlen := 64.
Notation "'valulen'" := (Valulen.valulen).
Notation "'valulen_is'" := (Valulen.valulen_is).

Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).
Definition addr_eq_dec := @weq addrlen.

Definition wringaddr := wring addrlen.
Add Ring wringaddr : wringaddr (decidable (weqb_sound addrlen), constants [wcst]).


Inductive prog :=
| Done (T: Type) (v: T)
| Read (a: addr) (rx: valu -> prog)
| Write (a: addr) (v: valu) (rx: unit -> prog).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).


Definition mem := addr -> option valu.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if addr_eq_dec a' a then Some v else m a'.

Inductive outcome :=
| Failed
| Finished (m: mem) (T: Type) (v: T)
| Crashed (m: mem).

Inductive exec : mem -> prog -> outcome -> Prop :=
| XReadFail : forall m a rx, m a = None
  -> exec m (Read a rx) Failed
| XWriteFail : forall m a v rx, m a = None
  -> exec m (Write a v rx) Failed
| XReadOK : forall m a v rx out, m a = Some v
  -> exec m (rx v) out
  -> exec m (Read a rx) out
| XWriteOK : forall m a v v0 rx out, m a = Some v0
  -> exec (upd m a v) (rx tt) out
  -> exec m (Write a v rx) out
| XDone : forall (m: mem) T (v: T), exec m (Done v) (Finished m v)
| XCrash : forall m p, exec m p (Crashed m).

Hint Constructors exec.


Inductive recover_crashflag :=
| NoCrash
| YesCrash.

Inductive recover_outcome :=
| RFailed
| RFinished (c: recover_crashflag) (m: mem) (T: Type) (v: T).

Inductive exec_recover : mem -> prog -> prog -> recover_outcome -> Prop :=
| XRFail : forall m p1 p2, exec m p1 Failed
  -> exec_recover m p1 p2 RFailed
| XRFinished : forall m p1 p2 m' T (v: T), exec m p1 (Finished m' v)
  -> exec_recover m p1 p2 (RFinished NoCrash m' v)
| XRCrashedFail : forall m p1 p2 m', exec m p1 (Crashed m')
  -> exec_recover m' p2 p2 RFailed
  -> exec_recover m p1 p2 RFailed
| XRCrashedOK : forall m p1 p2 m' m'' c T (v: T), exec m p1 (Crashed m')
  -> exec_recover m' p2 p2 (RFinished c m'' v)
  -> exec_recover m p1 p2 (RFinished YesCrash m'' v).

Hint Constructors exec_recover.


Theorem upd_eq : forall m a v a',
  a' = a
  -> upd m a v a' = Some v.
Proof.
  intros; subst; unfold upd.
  destruct (addr_eq_dec a a); tauto.
Qed.

Theorem upd_ne : forall m a v a',
  a' <> a
  -> upd m a v a' = m a'.
Proof.
  intros; subst; unfold upd.
  destruct (addr_eq_dec a' a); tauto.
Qed.

Theorem upd_repeat: forall m a v v',
  upd (upd m a v') a v = upd m a v.
Proof.
  intros; apply functional_extensionality; intros.
  case_eq (addr_eq_dec a x); intros; subst.
  repeat rewrite upd_eq; auto.
  repeat rewrite upd_ne; auto.
Qed.

Theorem upd_comm: forall m a0 v0 a1 v1, a0 <> a1
  -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
Proof.
  intros; apply functional_extensionality; intros.
  case_eq (addr_eq_dec a1 x); case_eq (addr_eq_dec a0 x); intros; subst.
  rewrite upd_eq; auto. rewrite upd_ne; auto. rewrite upd_eq; auto.
  rewrite upd_eq; auto. rewrite upd_ne; auto. rewrite upd_eq; auto.
  rewrite upd_ne; auto. rewrite upd_eq; auto. rewrite upd_eq; auto.
  rewrite upd_ne; auto. rewrite upd_ne; auto. rewrite upd_ne; auto. rewrite upd_ne; auto.
Qed.
