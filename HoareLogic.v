Require Import Arith Omega List.

Set Implicit Arguments.


(** * The programming language *)

Definition addr := nat.
Definition valu := nat.

Inductive prog :=
| Halt
| Crash
| Read (a : addr)
| Write (a : addr) (v : valu)
| Seq (p1 : prog) (p2 : valu -> prog).

Notation "!" := Read.
Infix "<--" := Write (at level 8).
Notation "p1 ;; p2" := (Seq p1 (fun _ => p2)) (at level 9, right associativity).
Notation "x <- p1 ; p2" := (Seq p1 (fun x => p2)) (at level 9, right associativity).

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

Definition impl (p q : pred) : pred :=
  fun m => p m -> q m.
Infix "-->" := impl (right associativity, at level 95) : pred_scope.

Definition and (p q : pred) : pred :=
  fun m => p m /\ q m.
Infix "/\" := and : pred_scope.

Definition or (p q : pred) : pred :=
  fun m => p m \/ q m.
Infix "\/" := or : pred_scope.

Definition foral_ A (p : A -> pred) : pred :=
  fun m => forall x, p x m.
Notation "'foral' x .. y , p" := (foral_ (fun x => .. (foral_ (fun y => p)) ..)) (at level 200, x binder, right associativity) : pred_scope.

Definition exis A (p : A -> pred) : pred :=
  fun m => exists x, p x m.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : pred_scope.

Definition lift (P : Prop) : pred :=
  fun _ => P.
Notation "[ P ]" := (lift P) : pred_scope.

Definition pimpl (p q : pred) := forall m, p m -> q m.
Notation "p --> q" := (pimpl p%pred q%pred).

Definition pupd (p : pred) (a : addr) (v : valu) : pred :=
  fun m => exists m', p m' /\ m = upd m' a v.
Notation "p [ a <--- v ]" := (pupd p a v) (at level 0) : pred_scope.

Definition diskIs (m : mem) : pred := eq m.

(** ** Hoare triples *)

Inductive corr :
     pred             (* Precondition *)
  -> prog             (* Program being verified *)
  -> (result -> pred) (* Postcondition *)
  -> Prop :=
| CHalt : forall pre,
  corr pre Halt (fun r => [r = Crashed \/ r = Halted 0] /\ pre)%pred
| CCrash : forall pre,
  corr pre Crash (fun r => [r = Crashed] /\ pre)%pred
| CRead : forall pre a,
  corr pre (Read a) (fun r => exists v, a |-> v /\ [r = Crashed \/ r = Halted v] /\ pre)%pred
| CWrite : forall pre a v,
  corr pre (Write a v) (fun r => ([r = Crashed] /\ pre) \/ ([r = Halted 0] /\ pre[a <--- v]))%pred
| CSeq : forall pre p1 p2 post1 post2,
  corr pre p1 post1
  -> (forall v, corr (post1 (Halted v)) (p2 v) post2)
  -> corr pre (Seq p1 p2) (fun r => ([r = Crashed] /\ post1 Crashed) \/ post2 r)%pred
| Conseq : forall pre post p pre' post', corr pre p post
  -> (pre' --> pre)
  -> (forall r, post r --> post' r)
  -> corr pre' p post'.

Hint Constructors corr.

Notation "{{ pre }} p {{ r , post }}" := (corr pre p (fun r => post)%pred)
  (at level 0, p at level 9).

(** ** Soundness  *)

Ltac deex := match goal with
               | [ H : ex _ |- _ ] => destruct H; intuition subst
             end.

Ltac pred_unfold := unfold ptsto, impl, and, or, foral_, exis, lift, pimpl, pupd, diskIs in *.
Ltac pred := pred_unfold;
  repeat (repeat deex;
    intuition (try congruence; try autorewrite with core in *; eauto)).

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


(** * Some helpful [prog] combinators *)

Theorem pimpl_refl : forall p, p --> p.
Proof.
  pred.
Qed.

Hint Resolve pimpl_refl.

Fixpoint Countdown (nocrash : nat -> pred) (crashed : pred)
  (f : nat -> prog) (n : nat) : prog :=
  match n with
    | O => Halt
    | S n' => (f n');; (Countdown nocrash crashed f n')
  end.

Notation "'Loop' i < n 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Pool'" :=
  (Countdown (fun i => nocrash)%pred crashed (fun i => body) n)
  (at level 9, i at level 0, n at level 0, body at level 9).

Theorem CCountdown : forall (f : nat -> prog)
  (nocrash : nat -> pred) (crashed : pred),
  (forall n, {{nocrash (S n)}} (f n)
    {{r, ([r = Halted 0] /\ nocrash n) \/ ([r = Crashed] /\ crashed)}})
  -> (nocrash 0 --> crashed)
  -> forall n, {{nocrash n}} (Countdown nocrash crashed f n)
    {{r, ([r = Halted 0] /\ nocrash 0) \/ ([r = Crashed] /\ crashed)}}.
Proof.
  induction n; simpl; intros.

  eapply Conseq.
  apply CHalt.
  apply pimpl_refl.
  simpl.
  pred.
  
  eapply Conseq.
  econstructor.
  eauto.
  simpl.
  intros.
  eapply Conseq.
  apply IHn.
  pred.
  simpl.
  intros.
  apply pimpl_refl.
  apply pimpl_refl.
  pred.
Qed.


(** * A log-based transactions implementation *)

Definition disjoint (r1 : addr * nat) (r2 : addr * nat) :=
  forall a, fst r1 <= a < fst r1 + snd r1
    -> ~(fst r2 <= a < fst r2 + snd r2).

Fixpoint disjoints (rs : list (addr * nat)) :=
  match rs with
    | nil => True
    | r1 :: rs => Forall (disjoint r1) rs /\ disjoints rs
  end.

Record xparams := {
  DataStart : addr; (* The actual committed data start at this disk address. *)
    DataLen : nat;  (* Size of data region *)

  LogLength : addr; (* Store the length of the log here. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : nat;  (* Size of log region *)

       Temp : addr; (* Temporary slot for use by library code *)

   Disjoint : disjoints ((DataStart, DataLen)
     :: (LogLength, 1)
     :: (LogStart, LogLen)
     :: (Temp, 1)
     :: nil)
}.

Theorem upd_eq : forall m a v a',
  a' = a
  -> upd m a v a' = v.
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

Ltac disjoint' xp :=
  generalize (Disjoint xp); simpl; intuition;
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : Forall _ nil |- _ ] => clear H
             | [ H : Forall _ (_ :: _) |- _ ] => inversion_clear H
           end; unfold disjoint in *; simpl in *; subst.

Ltac disjoint'' a :=
  match goal with
    | [ H : forall a', _ |- _ ] => specialize (H a); omega
  end.

Ltac disjoint xp :=
  disjoint' xp;
  match goal with
    | [ _ : _ <= ?n |- _ ] => disjoint'' n
  end.

Hint Rewrite upd_eq upd_ne using (congruence
  || match goal with
       | [ xp : xparams |- _ ] => disjoint xp
     end).

Ltac corr :=
  ((apply CHalt || apply CCrash || apply CRead || apply CWrite
    || eapply CSeq)
  || (eapply Conseq; [ | apply pimpl_refl | ])); intros.


Module Type LOG.
  (* Methods *)
  Parameter begin : xparams -> prog.
  Parameter commit : xparams -> prog.
  Parameter read : xparams -> addr -> prog.
  Parameter write : xparams -> addr -> valu -> prog.

  (* Representation invariant *)
  Parameter rep : xparams
    -> mem (* Memory as modified by current transaction,
            * only consulted for addresses in data range *)
    -> pred.

  (* Specs *)
  Axiom begin_ok : forall xp m, {{diskIs m}} (begin xp)
    {{r, ([r = Crashed] /\ diskIs m) \/ rep xp m}}.
End LOG.

Module Log : LOG.
  Definition begin xp :=
    (LogLength xp) <-- 0.

  Definition commit xp :=
    len <- !(LogLength xp);
    Loop i < len
      Invariant [True]
      OnCrash [True] Begin
      a <- !(LogStart xp + 2*i);
      v <- !(LogStart xp + 2*i + 1);
      a <-- v
    Pool.

  Definition read xp a :=
    len <- !(LogLength xp);
    (Temp xp) <-- len;;

    Loop i < len
      Invariant [True]
      OnCrash [True] Begin
      a' <- !(LogStart xp + 2*i);
      if eq_nat_dec a' a then
        tmp <- !(Temp xp);
        if eq_nat_dec tmp len then
          (Temp xp) <-- a
        else
          Halt
      else
        Halt
     Pool;;

     tmp <- !(Temp xp);
     if eq_nat_dec tmp len then
       !a
     else
       !(LogStart xp + 2*tmp + 1).

  Definition write xp a v :=
    len <- !(LogLength xp);
    if le_lt_dec (LogLen xp) len then
      Crash
    else
      (LogStart xp + 2*len) <-- a;;
      (LogStart xp + 2*len + 1) <-- v;;
      (LogLength xp) <-- (S len).

  Definition rep xp (m : mem) := (
    (* Quantify over log. *)
    exists ls,
      (* The right log length is stored. *)
      (LogLength xp) |-> (length ls)

      (* This log is stored in the real memory. *)
      /\ (foral i a_v, [nth_error (ls : list (addr * valu)) i = Some a_v]
        --> (LogStart xp + 2*i) |-> (fst a_v))
      /\ (foral i a_v, [nth_error ls i = Some a_v]
        --> (LogStart xp + 2*i + 1) |-> (snd a_v))

      (* The final log entry for each address is in the abstract memory. *)
      /\ [forall i a_v, nth_error ls i = Some a_v
        -> (forall j a_v', j > i -> nth_error ls i = Some a_v'
          -> fst a_v' <> fst a_v)
        -> m (fst a_v) = snd a_v]

      (* Unupdated addresses are unchanged. *)
      /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
        --> [forall i a_v, nth_error ls i = Some a_v
          -> fst a_v <> a]
        --> a |-> m a)
  )%pred.


  Lemma rep_nil : forall xp m,
    rep xp m (upd m (LogLength xp) 0).
  Proof.
    exists nil; pred;
      try match goal with
            | [ _ : nth_error nil ?X = Some _ |- _ ] =>
              destruct X; discriminate
          end.
  Qed.

  Hint Resolve rep_nil.

  Theorem begin_ok : forall xp m, {{diskIs m}} (begin xp) {{r, ([r = Crashed] /\ diskIs m) \/ rep xp m}}.
  Proof.
    repeat (corr || pred).
  Qed.
End Log.
