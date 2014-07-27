Require Import Arith.

Set Implicit Arguments.


(** * The programming language *)

Definition addr := nat.
Definition valu := nat.

Inductive prog :=
| Halt
| Read (a : addr)
| Write (a : addr) (v : valu)
| Seq (p1 : prog) (p2 : valu -> prog).

Notation "!" := Read.
Infix "<--" := Write (at level 8).
Notation "p1 ;; p2" := (Seq p1 (fun _ => p2)) (at level 9).
Notation "x <- p1 ; p2" := (Seq p1 (fun x => p2)) (at level 9).

Definition mem := addr -> valu.
Definition mem0 : mem := fun _ => 0.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if eq_nat_dec a' a then v else m a'.

Inductive result :=
| Halted (v : valu)
| Crashed.

Inductive exec : mem -> prog -> mem -> result -> Prop :=
| XHalt : forall m, exec m Halt m (Halted 0)
| XRead : forall m a, exec m (Read a) m (Halted (m a))
| XWrite : forall m a v, exec m (Write a v) (upd m a v) (Halted 0)
| XCrash : forall m p, exec m p m Crashed
| XSeqC : forall m p1 p2 m', exec m p1 m' Crashed
  -> exec m (Seq p1 p2) m' Crashed
| XSeqH : forall m p1 p2 m' v m'' r, exec m p1 m' (Halted v)
  -> exec m' (p2 v) m'' r
  -> exec m (Seq p1 p2) m'' r.


(** * The program logic *)

(** ** Predicates *)

Definition pred := mem -> Prop.

Definition ptsto (a : addr) (v : valu) : pred :=
  fun m => m a = v.
Infix "|->" := ptsto (at level 40) : pred_scope.
Bind Scope pred_scope with pred.
Delimit Scope pred_scope with pred.

Definition and (p q : pred) : pred :=
  fun m => p m /\ q m.
Infix "/\" := and : pred_scope.

Definition or (p q : pred) : pred :=
  fun m => p m \/ q m.
Infix "\/" := or : pred_scope.

Definition exis A (p : A -> pred) : pred :=
  fun m => exists x, p x m.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : pred_scope.

Definition lift (P : Prop) : pred :=
  fun _ => P.
Notation "[ P ]" := (lift P) : pred_scope.

Definition pimpl (p q : pred) := forall m, p m -> q m.
Notation "p --> q" := (pimpl p%pred q%pred) (at level 95).

Definition pupd (p : pred) (a : addr) (v : valu) : pred :=
  fun m => exists m', p m' /\ m = upd m' a v.
Notation "p [ a <--- v ]" := (pupd p a v) (at level 0) : pred_scope.

(** ** Hoare triples *)

Inductive corr :
     pred             (* Precondition *)
  -> prog             (* Program being verified *)
  -> (result -> pred) (* Postcondition *)
  -> Prop :=
| CHalt : forall pre,
  corr pre Halt (fun r => [r = Crashed \/ r = Halted 0] /\ pre)%pred
| CRead : forall pre a,
  corr pre (Read a) (fun r => exists v, a |-> v /\ [r = Crashed \/ r = Halted v] /\ pre)%pred
| CWrite : forall pre a v,
  corr pre (Write a v) (fun r => ([r = Crashed] /\ pre) \/ ([r = Halted 0] /\ pre[a <--- v]))%pred
| CSeq : forall pre p1 p2 post1 post2,
  corr pre p1 post1
  -> (forall v, corr (post1 (Halted v)) (p2 v) post2)
  -> corr pre (Seq p1 p2) (fun r => post1 Crashed \/ post2 r)%pred
| Conseq : forall pre post p pre' post', corr pre p post
  -> (pre' --> pre)
  -> (forall r, post r --> post' r)
  -> corr pre' p post'.

Notation "{{ pre }} p {{ r , post }}" := (corr pre p (fun r => post)%pred)
  (at level 0, p at level 9).

(** ** Soundness  *)

Ltac pred_unfold := unfold ptsto, and, or, exis, lift, pimpl, pupd in *.
Ltac pred := pred_unfold; intuition eauto.

Lemma could_always_crash : forall pre p post, corr pre p post
  -> forall m, pre m -> post Crashed m.
Proof.
  induction 1; pred.
Qed.

Local Hint Extern 1 =>
  match goal with
    | [ |- _ Crashed _ ] =>
      eapply could_always_crash; eassumption
  end.

Theorem corr_sound : forall pre p post, corr pre p post
  -> forall m m' r, exec m p m' r
    -> pre m
    -> post r m'.
Proof.
  induction 1; solve [ pred | inversion_clear 1; pred ].
Qed.
