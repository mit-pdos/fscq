Require Import Arith.
Require Import Word.
Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.

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


Inductive prog (T: Set) :=
| Done (v: T)
| Read (a: addr) (rx: valu -> prog T)
| Write (a: addr) (v: valu) (rx: unit -> prog T)
| Sync (rx: unit -> prog T).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).


Definition mem := addr -> option valu.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if addr_eq_dec a' a then Some v else m a'.

Inductive outcome (T: Set) :=
| Failed
| Finished (m: mem) (v: T)
| Crashed (m: mem).

Inductive exec (T: Set) : mem -> list mem -> prog T -> outcome T -> Prop :=
| XReadFail : forall m cms a rx, m a = None
  -> exec m cms (Read a rx) (Failed T)
| XWriteFail : forall m cms a v rx, m a = None
  -> exec m cms (Write a v rx) (Failed T)
| XReadOK : forall m cms a v rx out, m a = Some v
  -> exec m cms (rx v) out
  -> exec m cms (Read a rx) out
| XWriteOK : forall m cms cms' a v v0 rx out, m a = Some v0
  -> cms' = cms ++ map (fun m' => upd m' a v) cms
  -> exec (upd m a v) cms (rx tt) out
  -> exec m cms' (Write a v rx) out
| XSync : forall m cms rx out, exec m [m] (rx tt) out
  -> exec m cms (Sync rx) out
(* Note: the "Done" operation ignores possible crash states;
 * we assume Done is like sync *)
| XDone : forall m cms v, exec m cms (Done v) (Finished m v)
| XCrash : forall m cms p m', In m' cms -> exec m cms p (Crashed T m').

Hint Constructors exec.


Inductive recover_outcome (TF TR: Set) :=
| RFailed
| RFinished (m: mem) (v: TF)
| RRecovered (m: mem) (v: TR).

Inductive exec_recover (TF TR: Set)
  : mem -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
| XRFail : forall m p1 p2, exec m [m] p1 (Failed TF)
  -> exec_recover m p1 p2 (RFailed TF TR)
| XRFinished : forall m p1 p2 m' (v: TF), exec m [m] p1 (Finished m' v)
  -> exec_recover m p1 p2 (RFinished TR m' v)
| XRCrashedFailed : forall m p1 p2 m', exec m [m] p1 (Crashed TF m')
  -> @exec_recover TR TR m' p2 p2 (RFailed TR TR)
  -> exec_recover m p1 p2 (RFailed TF TR)
| XRCrashedFinished : forall m p1 p2 m' m'' (v: TR), exec m [m] p1 (Crashed TF m')
  -> @exec_recover TR TR m' p2 p2 (RFinished TR m'' v)
  -> exec_recover m p1 p2 (RRecovered TF m'' v)
| XRCrashedRecovered : forall m p1 p2 m' m'' (v: TR), exec m [m] p1 (Crashed TF m')
  -> @exec_recover TR TR m' p2 p2 (RRecovered TR m'' v)
  -> exec_recover m p1 p2 (RRecovered TF m'' v).

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
