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
| Sync (a: addr) (rx: unit -> prog T).

Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).


Definition valuset := (valu * list valu)%type.
Definition valuset_list (vs : valuset) := fst vs :: snd vs.

Definition mem := addr -> option valuset.
Definition upd (m : mem) (a : addr) (vs : valuset) : mem :=
  fun a' => if addr_eq_dec a' a then Some vs else m a'.

Inductive outcome (T: Set) :=
| Failed
| Finished (m: mem) (v: T)
| Crashed (m: mem).

Inductive exec (T: Set) : mem -> prog T -> outcome T -> Prop :=
| XReadFail : forall m a rx, m a = None
  -> exec m (Read a rx) (Failed T)
| XReadOK : forall m a v rx out x, m a = Some (v, x)
  -> exec m (rx v) out
  -> exec m (Read a rx) out
| XWriteFail : forall m a v rx, m a = None
  -> exec m (Write a v rx) (Failed T)
| XWriteOK : forall m a v v0 rx out x, m a = Some (v0, x)
  -> exec (upd m a (v, v0 :: x)) (rx tt) out
  -> exec m (Write a v rx) out
| XSyncFail : forall m a rx, m a = None
  -> exec m (Sync a rx) (Failed T)
| XSyncOK : forall m a rx v out x, m a = Some (v, x)
  -> exec (upd m a (v, nil)) (rx tt) out
  -> exec m (Sync a rx) out
| XCrash : forall m p, exec m p (Crashed T m)
| XDone : forall m v, exec m (Done v) (Finished m v).

Hint Constructors exec.



Inductive recover_outcome (TF TR: Set) :=
| RFailed
| RFinished (m: mem) (v: TF)
| RRecovered (m: mem) (v: TR).

Definition possible_crash (m m' : mem) : Prop :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists vs v', m a = Some vs /\ m' a = Some (v', nil) /\ In v' (valuset_list vs)).

Inductive exec_recover (TF TR: Set)
  : mem -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
| XRFail : forall m p1 p2, exec m p1 (Failed TF)
  -> exec_recover m p1 p2 (RFailed TF TR)
| XRFinished : forall m p1 p2 m' (v: TF), exec m p1 (Finished m' v)
  -> exec_recover m p1 p2 (RFinished TR m' v)
| XRCrashedFailed : forall m p1 p2 m' m'r, exec m p1 (Crashed TF m')
  -> possible_crash m' m'r
  -> @exec_recover TR TR m'r p2 p2 (RFailed TR TR)
  -> exec_recover m p1 p2 (RFailed TF TR)
| XRCrashedFinished : forall m p1 p2 m' m'r m'' (v: TR), exec m p1 (Crashed TF m')
  -> possible_crash m' m'r
  -> @exec_recover TR TR m'r p2 p2 (RFinished TR m'' v)
  -> exec_recover m p1 p2 (RRecovered TF m'' v)
| XRCrashedRecovered : forall m p1 p2 m' m'r m'' (v: TR), exec m p1 (Crashed TF m')
  -> possible_crash m' m'r
  -> @exec_recover TR TR m'r p2 p2 (RRecovered TR m'' v)
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
  case_eq (addr_eq_dec a1 x); case_eq (addr_eq_dec a0 x); intros; subst; try congruence;
  repeat ( ( rewrite upd_ne by auto ) || ( rewrite upd_eq by auto ) ); auto.
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
