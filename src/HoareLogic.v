Require Import Arith Omega List.

Set Implicit Arguments.


(** * The programming language *)

Definition addr := nat.
Definition valu := nat.

Inductive prog :=
| Halt_
| Crash_
| Read (a : addr)
| Write (a : addr) (v : valu)
| Seq (p1 : prog) (p2 : valu -> prog).

Notation "'Halt'" := Halt_.
Notation "'Crash'" := Crash_.
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

Ltac pred_unfold := unfold ptsto, impl, and, or, foral_, exis, lift, pimpl, pupd, diskIs, addr, valu in *.
Ltac pred := pred_unfold;
  repeat (repeat deex; simpl in *;
    intuition (try (congruence || omega);
      try autorewrite with core in *; eauto)).

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

Fixpoint For_ (f : nat -> prog) (i n : nat) : prog :=
  match n with
    | O => Halt
    | S n' => (f i);; (For_ f (S i) n')
  end.

Theorem CFor : forall (f : nat -> prog)
  (nocrash : nat -> pred) (crashed : pred),
  (forall m, nocrash m --> crashed)
  -> forall n i,
    (forall m, i <= m < n + i
      -> {{nocrash m}} (f m)
      {{r, ([r = Halted 0] /\ nocrash (S m)) \/ ([r = Crashed] /\ crashed)}})
    -> {{nocrash i}} (For_ f i n)
    {{r, ([r = Halted 0] /\ nocrash (n + i)) \/ ([r = Crashed] /\ crashed)}}.
Proof.
  induction n; simpl; intros.

  eapply Conseq.
  apply CHalt.
  apply pimpl_refl.
  simpl.
  pred.
  
  eapply Conseq.
  econstructor.
  eapply H0.
  omega.
  simpl.
  intros.
  eapply Conseq.
  apply IHn.
  intros.
  apply H0; omega.
  pred.
  simpl.
  intros.
  apply pimpl_refl.
  apply pimpl_refl.
  pred.
  replace (S (n + i)) with (n + S i) by omega; auto.
Qed.


(** * Better automation for Hoare triples *)

Section prog'.
  Variable ghostT : Type.
  (* This is a type that we pretend was passed as an extra
   * function argument, for specification purposes. *)

  Inductive prog' :=
  | Halt'
  | Crash'
  | Read' (a : addr)
  | Write' (a : addr) (v : valu)
  | Seq' (p1 : prog') (p2 : valu -> prog')
  | If' P Q (b : {P} + {Q}) (p1 p2 : prog')
  | For' (nocrash : ghostT -> nat -> pred) (crashed : ghostT -> pred)
    (f : nat -> prog') (n : nat).

  Fixpoint prog'Out (p : prog') : prog :=
    match p with
      | Halt' => Halt
      | Crash' => Crash
      | Read' a => Read a
      | Write' a v => Write a v
      | Seq' p1 p2 => Seq (prog'Out p1) (fun x => prog'Out (p2 x))
      | If' _ _ b p1 p2 => if b then prog'Out p1 else prog'Out p2
      | For' _ _ f n => For_ (fun x => prog'Out (f x)) 0 n
    end.

  Variable ghost : ghostT.

  (* Strongest postcondition *)
  Fixpoint spost (pre : pred) (p : prog') : result -> pred :=
    match p with
      | Halt' => fun r => [r = Crashed \/ r = Halted 0] /\ pre
      | Crash' => fun r => [r = Crashed] /\ pre
      | Read' a => fun r => exists v, a |-> v /\ [r = Crashed \/ r = Halted v] /\ pre
      | Write' a v => fun r => ([r = Crashed] /\ pre) \/ ([r = Halted 0] /\ pre[a <--- v])
      | Seq' p1 p2 => fun r => ([r = Crashed] /\ spost pre p1 Crashed)
        \/ exists v, spost (spost pre p1 (Halted v)) (p2 v) r
      | If' P Q b p1 p2 => fun r => spost (pre /\ [P]) p1 r
        \/ spost (pre /\ [Q]) p2 r
      | For' nocrash crashed f n => fun r =>
        ([r = Halted 0] /\ nocrash ghost n) \/ ([r = Crashed] /\ crashed ghost)
    end%pred.

  (* Verification conditions *)
  Fixpoint vc (pre : pred) (p : prog') : Prop :=
    match p with
      | Halt' => True
      | Crash' => True
      | Read' _ => True
      | Write' _ _ => True
      | Seq' p1 p2 => vc pre p1
        /\ forall v, vc (spost pre p1 (Halted v)) (p2 v)
      | If' P Q b p1 p2 => vc (pre /\ [P]) p1 /\ vc (pre /\ [Q]) p2
      | For' nocrash crashed f n =>
        (forall m, nocrash ghost m --> crashed ghost)
        /\ (pre --> nocrash ghost 0)
        /\ (forall m, m < n -> vc (nocrash ghost m) (f m))
        /\ (forall m r, m < n -> (spost (nocrash ghost m) (f m) r -->
          ([r = Halted 0] /\ nocrash ghost (S m)) \/ ([r = Crashed] /\ crashed ghost)))
    end.

  Lemma spost_sound' : forall p pre,
    vc pre p
    -> corr pre (prog'Out p) (spost pre p).
  Proof.
    induction p; simpl; intuition.

    eapply Conseq; [ | apply pimpl_refl | ].
    econstructor.
    eauto.
    intros.
    specialize (H2 v).
    apply H in H2.
    instantiate (1 := (fun r => exists v, spost (spost pre p (Halted v)) (p2 v) r)%pred).
    eapply Conseq; [ | apply pimpl_refl | ]; eauto.
    pred.
    auto.

    eapply IHp1 in H0.
    eapply Conseq; eauto; pred.

    eapply IHp2 in H1.
    eapply Conseq; eauto; pred.

    eapply Conseq.
    apply (@CFor _ (nocrash ghost) (crashed ghost)); auto.
    intros.
    eapply Conseq; [ | apply pimpl_refl | ]; eauto.
    apply H; apply H2; omega.
    intros.
    apply H4; omega.
    auto.
    simpl.
    replace (n + 0) with n; auto.
  Qed.

  Theorem spost_sound : forall p pre post,
    vc pre p
    -> (forall r, spost pre p r --> post r)
    -> corr pre (prog'Out p) post.
  Proof.
    intros; eapply Conseq; eauto using spost_sound'.
  Qed.
End prog'.

Implicit Arguments Halt' [ghostT].
Implicit Arguments Crash' [ghostT].
Implicit Arguments Read' [ghostT].
Implicit Arguments Write' [ghostT].

Notation "'Halt'" := Halt' : prog'_scope.
Notation "'Crash'" := Crash' : prog'_scope.
Notation "!" := Read' : prog'_scope.
Infix "<--" := Write' : prog'_scope.
Notation "p1 ;; p2" := (Seq' p1 (fun _ => p2)) : prog'_scope.
Notation "x <- p1 ; p2" := (Seq' p1 (fun x => p2)) : prog'_scope.
Delimit Scope prog'_scope with prog'.
Bind Scope prog'_scope with prog'.

Notation "'For' i < n 'Ghost' g 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Pool'" :=
  (For' (fun g i => nocrash%pred) (fun g => crashed%pred) (fun i => body) n)
  (at level 9, i at level 0, n at level 0, body at level 9) : prog'_scope.

Notation "'If' b { p1 } 'else' { p2 }" := (If' b p1 p2) (at level 9, b at level 0)
  : prog'_scope.

Notation "$( ghostT : p )" := (prog'Out (p%prog' : prog' ghostT))
  (ghostT at level 0).


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
     :: (LogStart, LogLen*2)
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
    | [ _ : _ = ?n |- _ ] => disjoint'' n
  end.

Hint Rewrite upd_eq upd_ne using (congruence
  || match goal with
       | [ xp : xparams |- _ ] => disjoint xp
     end).

Ltac hoare' :=
  match goal with
    | [ H : Crashed = Crashed |- _ ] => clear H
    | [ H : Halted _ = Halted _ |- _ ] => injection H; clear H; intros; subst
  end.

Ltac hoare := intros; match goal with
                        | _ => apply (spost_sound tt)
                        | [ x : _ |- _ ] => apply (spost_sound x)
                      end; simpl; pred; repeat hoare';
  intuition eauto.

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| InTransaction (old_cur : mem * mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second. *)
| Failed (cur : mem)
(* Crashed!  Recovery procedure should bring us to this memory. *).

Module Type LOG.
  (* Methods *)
  Parameter init : xparams -> prog.
  Parameter begin : xparams -> prog.
  Parameter commit : xparams -> prog.
  Parameter rollback : xparams -> prog.
  Parameter recover : xparams -> prog.
  Parameter read : xparams -> addr -> prog.
  Parameter write : xparams -> addr -> valu -> prog.

  (* Representation invariant *)
  Parameter rep : xparams -> logstate -> pred.

  (* Specs *)
  Axiom init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ diskIs m)}}.

  Axiom begin_ok : forall xp m, {{rep xp (NoTransaction m)}} (begin xp)
    {{r, rep xp (InTransaction (m, m))
      \/ ([r = Crashed] /\ rep xp (NoTransaction m))}}.

  Axiom commit_ok : forall xp ms, {{rep xp (InTransaction ms)}}
    (commit xp)
    {{r, rep xp (NoTransaction (snd ms))
      \/ ([r = Crashed] /\ rep xp (Failed (snd ms)))}}.

  Axiom rollback_ok : forall xp ms, {{rep xp (InTransaction ms)}}
    (rollback xp)
    {{r, rep xp (NoTransaction (fst ms))
      \/ ([r = Crashed] /\ rep xp (InTransaction ms))}}.

  Axiom recover_ok : forall xp m, {{rep xp (Failed m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (Failed m))}}.

  Axiom read_ok : forall xp ms a,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (InTransaction ms)}}
    (read xp a)
    {{r, rep xp (InTransaction ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.

  Axiom write_ok : forall xp ms a v,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (InTransaction ms)}}
    (write xp a v)
    {{r, rep xp (InTransaction (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (InTransaction ms))}}.
End LOG.

Module Log : LOG.
  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (a : addr) (len : nat) (m : mem) : mem :=
    match len with
      | O => m
      | S len' => replay (a+2) len' (upd m (m a) (m (a+1)))
    end.

  (* Check that a log is well-formed in memory. *)
  Fixpoint validLog xp (a : addr) (len : nat) (m : mem) : Prop :=
    match len with
      | O => True
      | S len' => DataStart xp <= m a < DataStart xp + DataLen xp
        /\ validLog xp (a+2) len' m
    end.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (* Log is empty. *)
        (LogLength xp) |-> 0
        (* Every data address has its value from [m]. *)
        /\ foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
        --> a |-> m a

      | InTransaction (old, cur) =>
        (* Every data address has its value from [old]. *)
        (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> old a)
        (* Look up log length. *)
        /\ exists len, (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            (* All log entries reference data addresses. *)
            /\ [validLog xp (LogStart xp) len m]
            (* We may compute the current memory by replaying the log. *)
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> cur a = replay (LogStart xp) len m a]

      | Failed cur =>
        exists len, (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> cur a = replay (LogStart xp) len m a]
    end%pred.

  Definition init xp := $(unit:
    (LogLength xp) <-- 0
  ).

  Definition begin := init.

  Definition commit xp := $((mem*mem):
    len <- !(LogLength xp);
    For i < len
      Ghost old_cur
      Invariant (
        (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> replay (LogStart xp) i (fst old_cur) a)
        /\ (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> snd old_cur a = replay (LogStart xp) len m a])
      OnCrash rep xp (NoTransaction (snd old_cur))
      \/ rep xp (Failed (snd old_cur)) Begin
      a <- !(LogStart xp + i*2);
      v <- !(LogStart xp + i*2 + 1);
      a <-- v
    Pool;;

    (LogLength xp) <-- 0).

  Definition rollback := init.
  Definition recover := commit.

  Definition read xp a := $((mem*mem):
    len <- !(LogLength xp);
    v <- !a;
    (Temp xp) <-- v;;

    For i < len
      Ghost old_cur
      Invariant (
        (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> fst old_cur a)
        /\ (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> snd old_cur a = replay (LogStart xp) len m a]
            /\ [m (Temp xp) = replay (LogStart xp) i m a])
      OnCrash rep xp (InTransaction old_cur) Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        (Temp xp) <-- i
      } else {
        Halt
      }
     Pool;;

     (!(Temp xp))
  ).

  Definition write xp a v := $(unit:
    len <- !(LogLength xp);
    If (le_lt_dec (LogLen xp) len) {
      Crash
    } else {
      (LogStart xp + len*2) <-- a;;
      (LogStart xp + len*2 + 1) <-- v;;
      (LogLength xp) <-- (S len)
    }
  ).

  Theorem init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ diskIs m)}}.
  Proof.
    hoare.
  Qed.
    
  Hint Extern 1 (_ <= _) => omega.

  Ltac t'' := intuition eauto; pred;
    try solve [ symmetry; eauto ].

  Ltac t' := t'';
    repeat (match goal with
              | [ |- ex _ ] => eexists
            end; t'').

  Ltac t := t';
    match goal with
      | [ |- _ \/ _ ] => (left; solve [t]) || (right; solve [t])
      | _ => idtac
    end.

  Theorem begin_ok : forall xp m, {{rep xp (NoTransaction m)}} (begin xp)
    {{r, rep xp (InTransaction (m, m))
      \/ ([r = Crashed] /\ rep xp (NoTransaction m))}}.
  Proof.
    hoare; t.
  Qed.

  Theorem rollback_ok : forall xp ms, {{rep xp (InTransaction ms)}}
    (rollback xp)
    {{r, rep xp (NoTransaction (fst ms))
      \/ ([r = Crashed] /\ rep xp (InTransaction ms))}}.
  Proof.
    hoare.
  Qed.

  Lemma validLog_irrel : forall xp len a m1 m2,
    validLog xp a len m1
    -> (forall a', a <= a' < a + len*2
      -> m1 a' = m2 a')
    -> validLog xp a len m2.
  Proof.
    induction len; simpl; intuition eauto;
      try match goal with
            | [ H : _ |- _ ] => rewrite <- H by omega; solve [ auto ]
            | [ H : _ |- _ ] => eapply H; intuition eauto
          end.
  Qed.

  Lemma upd_same : forall m1 m2 a1 a2 v1 v2 a',
    m1 a' = m2 a'
    -> a1 = a2
    -> v1 = v2
    -> upd m1 a1 v1 a' = upd m2 a2 v2 a'.
  Proof.
    intros; subst; unfold upd; destruct (eq_nat_dec a' a2); auto.
  Qed.

  Hint Resolve upd_same.

  Lemma replay_irrel : forall xp a',
    DataStart xp <= a' < DataStart xp + DataLen xp
    -> forall len a m1 m2,
      (forall a', a <= a' < a + len*2
        -> m1 a' = m2 a')
      -> (forall a', DataStart xp <= a' < DataStart xp + DataLen xp
        -> m1 a' = m2 a')
      -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition eauto;
      apply IHlen; intuition;
        match goal with
          | [ H : _ |- _ ] => repeat rewrite H by omega; solve [ auto ]
        end.
  Qed.

  Hint Rewrite plus_0_r.

  Lemma two : forall a len,
    a + 2 + len * 2 = a + S (S (len * 2)).
  Proof.
    intros; omega.
  Qed.

  Hint Rewrite two.

  Lemma validLog_add' : forall xp len a m1 m2,
    validLog xp a len m1
    -> (forall a', a <= a' < a + len*2
      -> m1 a' = m2 a')
    -> DataStart xp <= m2 (a + len*2) < DataStart xp + DataLen xp
    -> validLog xp a (len+1) m2.
  Proof.
    induction len; simpl; intuition eauto;
      try match goal with
            | [ H : _ |- _ ] => rewrite <- H by omega; solve [ auto ]
          end; pred;
      match goal with
        | [ H : _ |- _ ] => eapply H; intuition eauto; pred
      end.
  Qed.

  Lemma validLog_add : forall xp len a m1 m2,
    validLog xp a len m1
    -> (forall a', a <= a' < a + len*2
      -> m1 a' = m2 a')
    -> DataStart xp <= m2 (a + len*2) < DataStart xp + DataLen xp
    -> validLog xp a (S len) m2.
  Proof.
    intros; replace (S len) with (len + 1) by omega.
    eauto using validLog_add'.
  Qed.

  Lemma replay_plus : forall len2 len1 a m,
    replay a (len1 + len2) m = replay (a + len1*2) len2 (replay a len1 m).
  Proof.
    induction len1; simpl; intuition eauto; pred.
    rewrite IHlen1; pred.
  Qed.

  Lemma replay_log : forall xp a' len m a,
    LogStart xp <= a' < LogStart xp + LogLen xp*2
    -> validLog xp a len m
    -> LogStart xp <= a
    -> a + len*2 < LogStart xp + LogLen xp * 2
    -> replay a len m a' = m a'.
  Proof.
    induction len; simpl; intuition eauto.
    rewrite IHlen; intuition eauto.
    pred.
    eapply validLog_irrel; eauto; pred.
  Qed.

  Theorem write_ok : forall xp ms a v,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (InTransaction ms)}}
    (write xp a v)
    {{r, rep xp (InTransaction (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (InTransaction ms))}}.
  Proof.
    hoare.

    right; intuition.
    pred.
    eexists; intuition eauto.
    eexists; intuition eauto.
    eapply validLog_irrel; eauto; pred.
    erewrite replay_irrel; eauto; pred.

    right; intuition.
    pred.
    eexists; intuition eauto.
    eexists; intuition eauto.
    eapply validLog_irrel; eauto; pred.
    erewrite replay_irrel; eauto; pred.

    left; intuition.
    pred.
    eexists; intuition eauto.
    eexists; intuition eauto.
    eapply validLog_add; eauto; pred.
    replace (S (x2 (LogLength xp))) with (x2 (LogLength xp) + 1) by omega.
    rewrite replay_plus.
    simpl.

    apply upd_same.
    rewrite H10 by auto.
    eapply replay_irrel; eauto; pred.
    erewrite replay_log.
    2: instantiate (1 := xp); eauto.
    pred.
    eapply validLog_irrel; eauto; pred.
    auto.
    auto.
    erewrite replay_log.
    2: instantiate (1 := xp); eauto.
    pred.
    eapply validLog_irrel; eauto; pred.
    auto.
    auto.
  Qed.

  Axiom commit_ok : forall xp ms, {{rep xp (InTransaction ms)}}
    (commit xp)
    {{r, rep xp (NoTransaction (snd ms))
      \/ ([r = Crashed] /\ rep xp (Failed (snd ms)))}}.

  Axiom recover_ok : forall xp m, {{rep xp (Failed m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (Failed m))}}.

  Axiom read_ok : forall xp ms a,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (InTransaction ms)}}
    (read xp a)
    {{r, rep xp (InTransaction ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.

End Log.
