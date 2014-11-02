Require Import Arith.
Require Import Word.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
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

Fixpoint apply_writes pending m :=
  match pending with
  | nil => m
  | (a, v) :: rest => upd (apply_writes rest m) a v
  end.

Inductive apply_some : list (addr*valu)%type -> mem -> mem -> Prop :=
  | KeepOneWrite: forall a v m m' pending, apply_some pending m m'
    -> apply_some ((a, v) :: pending) m (upd m' a v)
  | DropOneWrite: forall a v m m' pending, apply_some pending m m'
    -> apply_some ((a, v) :: pending) m m'.

Inductive exec (T: Set) : mem -> list (addr*valu)%type -> prog T -> outcome T -> Prop :=
| XReadFail : forall m pending a rx, apply_writes pending m a = None
  -> exec m pending (Read a rx) (Failed T)
| XWriteFail : forall m pending a v rx, apply_writes pending m a = None
  -> exec m pending (Write a v rx) (Failed T)
| XReadOK : forall m pending a v rx out, apply_writes pending m a = Some v
  -> exec m pending (rx v) out
  -> exec m pending (Read a rx) out
| XWriteOK : forall m pending a v v0 rx out, apply_writes pending m a = Some v0
  -> exec m ((a, v) :: pending) (rx tt) out
  -> exec m pending (Write a v rx) out
| XSync : forall m pending rx out, exec (apply_writes pending m) nil (rx tt) out
  -> exec m pending (Sync rx) out
| XCrash : forall m pending p m', apply_some pending m m'
  -> exec m pending p (Crashed T m')
(* Note: the "Done" operation ignores possible crash states;
 * we assume Done is like sync *)
| XDone : forall m pending v, exec m pending (Done v) (Finished m v).

Hint Constructors exec.


Inductive recover_outcome (TF TR: Set) :=
| RFailed
| RFinished (m: mem) (v: TF)
| RRecovered (m: mem) (v: TR).

Inductive exec_recover (TF TR: Set)
  : mem -> list (addr*valu)%type ->
    prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
| XRFail : forall m pending p1 p2, exec m pending p1 (Failed TF)
  -> exec_recover m pending p1 p2 (RFailed TF TR)
| XRFinished : forall m pending p1 p2 m' (v: TF), exec m pending p1 (Finished m' v)
  -> exec_recover m pending p1 p2 (RFinished TR m' v)
| XRCrashedFailed : forall m pending p1 p2 m', exec m pending p1 (Crashed TF m')
  -> @exec_recover TR TR m' nil p2 p2 (RFailed TR TR)
  -> exec_recover m pending p1 p2 (RFailed TF TR)
| XRCrashedFinished : forall m pending p1 p2 m' m'' (v: TR), exec m pending p1 (Crashed TF m')
  -> @exec_recover TR TR m' nil p2 p2 (RFinished TR m'' v)
  -> exec_recover m pending p1 p2 (RRecovered TF m'' v)
| XRCrashedRecovered : forall m pending p1 p2 m' m'' (v: TR), exec m pending p1 (Crashed TF m')
  -> @exec_recover TR TR m' nil p2 p2 (RRecovered TR m'' v)
  -> exec_recover m pending p1 p2 (RRecovered TF m'' v).

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

Lemma addrlen_valulen: addrlen + (valulen - addrlen) = valulen.
Proof.
  rewrite valulen_is; auto.
Qed.

Definition addr2valu (a: addr) : valu.
  set (zext a (valulen-addrlen)) as r.
  rewrite addrlen_valulen in r.
  apply r.
Defined.

Definition valu2addr (v: valu) : addr.
  rewrite <- addrlen_valulen in v.
  apply (split1 addrlen (valulen-addrlen) v).
Defined.

Lemma addr2valu2addr: forall a,
  valu2addr (addr2valu a) = a.
Proof.
  unfold valu2addr, addr2valu.
  unfold eq_rec_r, eq_rec.
  intros.
  rewrite <- addrlen_valulen.
  rewrite <- eq_rect_eq_dec; try apply eq_nat_dec.
  rewrite <- eq_rect_eq_dec; try apply eq_nat_dec.
  apply split1_combine.
Qed.

Global Opaque addr2valu.
Global Opaque valu2addr.
(* Once this bug is fixed:
     https://coq.inria.fr/bugs/show_bug.cgi?id=3731
   we should enable this rewrite hint:
Hint Rewrite addr2valu2addr.
*)
