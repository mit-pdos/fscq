Require Import Arith Omega List.

Set Implicit Arguments.


(** * The programming language *)

Definition addr := nat.
Definition valu := nat.

Inductive prog : Set -> Type :=
| Halt_ {R : Set} (v : R) : prog R
| Crash_ (R : Set) : prog R
| Read (a : addr) : prog valu
| Write (a : addr) (v : valu) : prog unit
| Seq {T R : Set} (p1 : prog T) (p2 : T -> prog R) : prog R.

Notation "'Halt'" := Halt_.
Notation "'Crash'" := Crash_.
Notation "!" := Read.
Infix "<--" := Write (at level 8).
Notation "p1 ;; p2" := (Seq p1 (fun _: unit => p2)) (at level 9, right associativity).
Notation "x <- p1 ; p2" := (Seq p1 (fun x => p2)) (at level 9, right associativity).

Definition mem := addr -> valu.
Definition mem0 : mem := fun _ => 0.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if eq_nat_dec a' a then v else m a'.

Inductive result (R:Set) :=
| Halted (v : R)
| Crashed.
Implicit Arguments Halted [R].
Implicit Arguments Crashed [R].

Inductive exec : forall {R : Set}, mem -> prog R -> mem -> result R -> Prop :=
| XHalt : forall (R : Set) m (v : R), exec m (Halt v) m (Halted v)
| XRead : forall m a, exec m (Read a) m (Halted (m a))
| XWrite : forall m a v, exec m (Write a v) (upd m a v) (Halted tt)
| XCrash : forall (R : Set) m p, exec m p m (@Crashed R)
| XSeqC : forall (R T : Set) m p1 p2 m', exec m p1 m' (@Crashed T)
  -> exec m (Seq p1 p2) m' (@Crashed R)
| XSeqH : forall (R T : Set) m p1 p2 m' (v : T) m'' (r : result R), exec m p1 m' (Halted v)
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

Inductive corr : forall {R : Set},
     pred                (* Precondition *)
  -> prog R              (* Program being verified *)
  -> (@result R -> pred) (* Postcondition *)
  -> Prop :=
| CHalt : forall (R:Set) pre (v:R),
  corr pre (Halt v) (fun r => [r = Crashed \/ r = Halted v] /\ pre)%pred
| CCrash : forall (R:Set) pre,
  corr pre (Crash R) (fun r => [r = Crashed] /\ pre)%pred
| CRead : forall pre a,
  corr pre (Read a) (fun r => exists v, a |-> v /\ [r = Crashed \/ r = Halted v] /\ pre)%pred
| CWrite : forall pre a v,
  corr pre (Write a v) (fun r => ([r = Crashed] /\ pre) \/ ([r = Halted tt] /\ pre[a <--- v]))%pred
| CSeq : forall (R T:Set) pre p1 p2 post1 post2,
  corr pre p1 post1
  -> (forall (v:T), corr (post1 (Halted v)) (p2 v) post2)
  -> corr pre (Seq p1 p2) (fun r => ([r = @Crashed R] /\ post1 Crashed) \/ post2 r)%pred
| Conseq : forall (R:Set) pre post p pre' post', @corr R pre p post
  -> (pre' --> pre)
  -> (forall r, post r --> post' r)
  -> corr pre' p post'
| CExistsPre : forall (R:Set) pre post p, @corr R pre p post
  -> corr pre p (fun rr => post rr /\ [exists s', pre s'])%pred.

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
      try autorewrite with core in *; eauto); try subst).

Lemma could_always_crash : forall R pre p post, @corr R pre p post
  -> forall m, pre m -> post Crashed m.
Proof.
  induction 1; pred.
Qed.

Local Hint Extern 1 =>
  match goal with
    | [ |- _ Crashed _ ] =>
      eapply could_always_crash; eassumption
  end.

Lemma invert_exec : forall R m (p : prog R) m' r,
  exec m p m' r
  -> (m' = m /\ r = Crashed)
     \/ match p in prog R return result R -> Prop with
        | Halt_ _ v => fun r => m' = m /\ r = Halted v
        | Read a => fun r => m' = m /\ r = Halted (m a)
        | Write a v => fun r => m' = upd m a v /\ r = Halted tt
        | Seq _ _ p1 p2 => fun r => (exec m p1 m' Crashed /\ r = Crashed)
          \/ (exists m'' v, exec m p1 m'' (Halted v)
                            /\ exec m'' (p2 v) m' r)
        | Crash_ _ => fun _ => False
        end r.
Proof.
  destruct 1; eauto 10.
Qed.

Theorem corr_sound : forall R pre p post, @corr R pre p post
  -> forall m m' r, exec m p m' r
    -> pre m
    -> post r m'.
Proof.
  induction 1; try solve [ pred | intros ? ? ? Hexec; apply invert_exec in Hexec; pred ].
Qed.


(** * Some helpful [prog] combinators *)

Theorem pimpl_refl : forall p, p --> p.
Proof.
  pred.
Qed.

Hint Resolve pimpl_refl.

Fixpoint For_ (f : nat -> prog unit) (i n : nat) : prog unit :=
  match n with
    | O => Halt tt
    | S n' => (f i);; (For_ f (S i) n')
  end.

Theorem CFor : forall (f : nat -> prog unit)
  (nocrash : nat -> pred) (crashed : pred),
  (forall m, nocrash m --> crashed)
  -> forall n i,
    (forall m, i <= m < n + i
      -> {{nocrash m}} (f m)
      {{r, ([r = Halted tt] /\ nocrash (S m)) \/ ([r = Crashed] /\ crashed)}})
    -> {{nocrash i}} (For_ f i n)
    {{r, ([r = Halted tt] /\ nocrash (n + i)) \/ ([r = Crashed] /\ crashed)}}.
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

  Inductive prog' : Set -> Type :=
  | Halt' (R : Set) (v : R) : prog' R
  | Crash' (R : Set) : prog' R
  | Read' (a : addr) : prog' valu
  | Write' (a : addr) (v : valu) : prog' unit
  | Seq' {T R : Set} (p1 : prog' T) (p2 : T -> prog' R) : prog' R
  | If' (R : Set) P Q (b : {P} + {Q}) (p1 p2 : prog' R) : prog' R
  | For' (nocrash : ghostT -> nat -> pred) (crashed : ghostT -> pred)
    (f : nat -> prog' unit) (n : nat) : prog' unit
  | Call' (R : Set) (pre: ghostT -> pred) (p: prog R)
    (post: ghostT -> result R -> pred)
    (c: forall g: ghostT, corr (pre g) p (post g)) : prog' R.

  Fixpoint prog'Out {R : Set} (p : prog' R) : prog R :=
    match p with
      | Halt' _ v => Halt v
      | Crash' R => Crash R
      | Read' a => Read a
      | Write' a v => Write a v
      | Seq' _ _ p1 p2 => Seq (prog'Out p1) (fun x => prog'Out (p2 x))
      | If' _ _ _ b p1 p2 => if b then prog'Out p1 else prog'Out p2
      | For' _ _ f n => For_ (fun x => prog'Out (f x)) 0 n
      | Call' _ _ p _ _ => p
    end.

  Variable ghost : ghostT.

  (* Strongest postcondition *)
  Fixpoint spost {R : Set} (pre : pred) (p : prog' R) : result R -> pred :=
    match p with
      | Halt' _ v => fun r => [r = Crashed \/ r = Halted v] /\ pre
      | Crash' _ => fun r => [r = Crashed] /\ pre
      | Read' a => fun r => exists v, a |-> v /\ [r = Crashed \/ r = Halted v] /\ pre
      | Write' a v => fun r => ([r = Crashed] /\ pre) \/ ([r = Halted tt] /\ pre[a <--- v])
      | Seq' _ _ p1 p2 => fun r => ([r = Crashed] /\ spost pre p1 Crashed)
        \/ exists v, spost (spost pre p1 (Halted v)) (p2 v) r
      | If' _ P Q b p1 p2 => fun r => spost (pre /\ [P]) p1 r
        \/ spost (pre /\ [Q]) p2 r
      | For' nocrash crashed f n => fun r =>
        ([r = Halted tt] /\ nocrash ghost n) \/ ([r = Crashed] /\ crashed ghost)
      | Call' _ cpre cp cpost c => (fun r => cpost ghost r /\ [exists s', pre s'])
    end%pred.

  (* Verification conditions *)
  Fixpoint vc {R : Set} (pre : pred) (p : prog' R) : Prop :=
    match p with
      | Halt' _ v => True
      | Crash' _ => True
      | Read' _ => True
      | Write' _ _ => True
      | Seq' _ _ p1 p2 => vc pre p1
        /\ forall v, vc (spost pre p1 (Halted v)) (p2 v)
      | If' _ P Q b p1 p2 => vc (pre /\ [P]) p1 /\ vc (pre /\ [Q]) p2
      | For' nocrash crashed f n =>
        (forall m, nocrash ghost m --> crashed ghost)
        /\ (pre --> nocrash ghost 0)
        /\ (forall m, m < n -> vc (nocrash ghost m) (f m))
        /\ (forall m r, m < n -> (spost (nocrash ghost m) (f m) r -->
          ([r = Halted tt] /\ nocrash ghost (S m)) \/ ([r = Crashed] /\ crashed ghost)))
      | Call' _ cpre cp cpost c => pre --> (cpre ghost)
    end.

  Lemma spost_sound' : forall R p pre,
    @vc R pre p
    -> corr pre (prog'Out p) (spost pre p).
  Proof.
    induction p; simpl; intuition.

    - eapply Conseq; [ | apply pimpl_refl | ].
      + econstructor.
        * eauto.
        * intros.
          specialize (H2 v).
          apply H in H2.
          instantiate (1 := (fun r => exists v, spost (spost pre p (Halted v)) (p2 v) r)%pred).
          eapply Conseq; [ | apply pimpl_refl | ]; eauto.
          pred.
      + auto.

    - eapply IHp1 in H0.
      eapply Conseq; eauto; pred.

    - eapply IHp2 in H1.
      eapply Conseq; eauto; pred.

    - eapply Conseq.
      + apply (@CFor _ (nocrash ghost) (crashed ghost)); auto.
        intros.
        eapply Conseq; [ | apply pimpl_refl | ]; eauto.
        * apply H; apply H2; omega.
        * intros.
          apply H4; omega.
      + auto.
      + simpl.
        replace (n + 0) with n; auto.

    - eauto.
  Qed.

  Theorem spost_sound : forall R p pre post,
    @vc R pre p
    -> (forall r, spost pre p r --> post r)
    -> corr pre (prog'Out p) post.
  Proof.
    intros; eapply Conseq; eauto using spost_sound'.
  Qed.
End prog'.

Implicit Arguments Halt' [ghostT R].
Implicit Arguments Crash' [ghostT R].
Implicit Arguments Read' [ghostT].
Implicit Arguments Write' [ghostT].
Implicit Arguments Call' [ghostT R pre p post].

Notation "'Halt'" := Halt' : prog'_scope.
Notation "'Crash'" := Crash' : prog'_scope.
Notation "!" := Read' : prog'_scope.
Infix "<--" := Write' : prog'_scope.
Notation "'Call'" := Call' : prog'_scope.
Notation "p1 ;; p2" := (Seq' p1 (fun _ : unit => p2)) : prog'_scope.
Notation "x <- p1 ; p2" := (Seq' p1 (fun x => p2)) : prog'_scope.
Delimit Scope prog'_scope with prog'.
Bind Scope prog'_scope with prog'.

Notation "'For' i < n 'Ghost' g 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Pool'" :=
  (For' (fun g i => nocrash%pred) (fun g => crashed%pred) (fun i => body) n)
  (at level 9, i at level 0, n at level 0, body at level 9) : prog'_scope.

Notation "'If' b { p1 } 'else' { p2 }" := (If' b p1 p2) (at level 9, b at level 0)
  : prog'_scope.

Notation "$( ghostT : p )" := (prog'Out (p%prog' : prog' ghostT _))
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
  LogCommit : addr; (* Store true to apply after crash. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : nat;  (* Size of log region *)

       Temp : addr; (* Temporary slot for use by library code *)

   Disjoint : disjoints ((DataStart, DataLen)
     :: (LogLength, 1)
     :: (LogCommit, 1)
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

Ltac hoare_ghost g := apply (spost_sound g); simpl; pred; repeat hoare'; intuition eauto.

Ltac hoare := intros; match goal with
                        | _ => hoare_ghost tt
                        | [ x : _ |- _ ] => hoare_ghost x
                      end.

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old_cur : mem * mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| CommittedTxn (cur : mem)
(* A transaction has committed but the log has not been applied yet. *).

Module Type LOG.
  (* Methods *)
  Parameter init : xparams -> prog unit.
  Parameter begin : xparams -> prog unit.
  Parameter commit : xparams -> prog unit.
  Parameter abort : xparams -> prog unit.
  Parameter recover : xparams -> prog unit.
  Parameter read : xparams -> addr -> prog valu.
  Parameter write : xparams -> addr -> valu -> prog unit.

  (* Representation invariant *)
  Parameter rep : xparams -> logstate -> pred.

  (* Specs *)
  Axiom init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ diskIs m)}}.

  Axiom begin_ok : forall xp m, {{rep xp (NoTransaction m)}} (begin xp)
    {{r, rep xp (ActiveTxn (m, m))
      \/ ([r = Crashed] /\ rep xp (NoTransaction m))}}.

  Axiom commit_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (commit xp)
    {{r, rep xp (NoTransaction m2)
      \/ ([r = Crashed] /\ (rep xp (ActiveTxn (m1, m2)) \/
                            rep xp (CommittedTxn m2)))}}.

  Axiom abort_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (abort xp)
    {{r, rep xp (NoTransaction m1)
      \/ ([r = Crashed] /\ rep xp (ActiveTxn (m1, m2)))}}.

  Axiom recover_ok : forall xp m m', {{rep xp (NoTransaction m) \/
                                       rep xp (ActiveTxn (m, m')) \/
                                       rep xp (CommittedTxn m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ (rep xp (NoTransaction m) \/
                            rep xp (CommittedTxn m)))}}.

  Axiom read_ok : forall xp a ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (read xp a)
    {{r, rep xp (ActiveTxn ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.

  Axiom write_ok : forall xp a v ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (write xp a v)
    {{r, rep xp (ActiveTxn (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (ActiveTxn ms))}}.
End LOG.

Module Log : LOG.
  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (a : addr) (len : nat) (m : mem) : mem :=
    match len with
      | O => m
      | S len' => upd (replay a len' m) (m (a + len'*2)) (m (a + len'*2 + 1))
    end.

  (* Check that a log is well-formed in memory. *)
  Fixpoint validLog xp (a : addr) (len : nat) (m : mem) : Prop :=
    match len with
      | O => True
      | S len' => DataStart xp <= m (a + len'*2) < DataStart xp + DataLen xp
        /\ validLog xp a len' m
    end.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (* Not committed. *)
        (LogCommit xp) |-> 0
        (* Every data address has its value from [m]. *)
        /\ foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
        --> a |-> m a

      | ActiveTxn (old, cur) =>
        (* Not committed. *)
        (LogCommit xp) |-> 0
        (* Every data address has its value from [old]. *)
        /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
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

      | CommittedTxn cur =>
        (* Committed but not applied. *)
        (LogCommit xp) |-> 1
        (* Log produces cur. *)
        /\ exists len, (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> cur a = replay (LogStart xp) len m a]
    end%pred.

  Definition init xp := $(unit:
    (LogCommit xp) <-- 0
  ).

  Theorem init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ diskIs m)}}.
  Proof.
    hoare.
  Qed.

  Definition begin xp := $(unit:
    (LogLength xp) <-- 0
  ).
    
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
    {{r, rep xp (ActiveTxn (m, m))
      \/ ([r = Crashed] /\ rep xp (NoTransaction m))}}.
  Proof.
    hoare; t.
  Qed.

  Definition apply xp := $(mem:
    len <- !(LogLength xp);
    For i < len
      Ghost cur
      Invariant (exists m, diskIs m
        /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
          -> cur a = replay (LogStart xp) len m a]
        /\ (LogCommit xp) |-> 1
        /\ (LogLength xp) |-> len
        /\ [len <= LogLen xp]
        /\ [validLog xp (LogStart xp) len m]
        /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
          -> m a = replay (LogStart xp) i m a])
      OnCrash rep xp (NoTransaction cur)
      \/ rep xp (CommittedTxn cur) Begin
      a <- !(LogStart xp + i*2);
      v <- !(LogStart xp + i*2 + 1);
      a <-- v
    Pool;;
    (LogCommit xp) <-- 0
  ).

  Lemma validLog_irrel : forall xp a len m1 m2,
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

  Lemma validLog_data : forall xp m len a x1,
    m < len
    -> validLog xp a len x1
    -> DataStart xp <= x1 (a + m * 2) < DataStart xp + DataLen xp.
  Proof.
    induction len; simpl; intros.
    intuition.
    destruct H0.
    destruct (eq_nat_dec m len); subst; auto.
  Qed.

  Lemma upd_same : forall m1 m2 a1 a2 v1 v2 a',
    a1 = a2
    -> v1 = v2
    -> (a' <> a1 -> m1 a' = m2 a')
    -> upd m1 a1 v1 a' = upd m2 a2 v2 a'.
  Proof.
    intros; subst; unfold upd; destruct (eq_nat_dec a' a2); auto.
  Qed.

  Hint Resolve upd_same.

  Lemma replay_irrel : forall xp a',
    DataStart xp <= a' < DataStart xp + DataLen xp
    -> forall a len m1 m2,
      (forall a', a <= a' < a + len*2
        -> m1 a' = m2 a')
      -> m1 a' = m2 a'
      -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition eauto.
    apply upd_same; eauto.
  Qed.

  Hint Rewrite plus_0_r.

  Lemma replay_redo : forall a a' len m1 m2,
    (forall a'', a <= a'' < a + len*2
      -> m1 a'' = m2 a'')
    -> (m1 a' <> m2 a'
      -> exists k, k < len
        /\ m1 (a + k*2) = a'
        /\ m2 (a + k*2) = a')
    -> ~(a <= a' < a + len*2)
    -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition.
    destruct (eq_nat_dec (m1 a') (m2 a')); auto.
    apply H0 in n.
    destruct n; intuition omega.

    apply upd_same; eauto; intros.
    apply IHlen; eauto; intros.
    apply H0 in H3.
    destruct H3; intuition.
    destruct (eq_nat_dec x len); subst; eauto.
    2: exists x; eauto.
    tauto.
  Qed.

  Theorem apply_ok : forall xp m, {{rep xp (CommittedTxn m)}} (apply xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (CommittedTxn m))}}.
  Proof.
    hoare.

    - eauto 10.
    - eauto 10.
    - eauto 12.
    - eauto 12.
    - eauto 12.
    - assert (DataStart xp <= x1 (LogStart xp + m0 * 2) < DataStart xp + DataLen xp) by eauto using validLog_data.
      left; intuition eauto.
      eexists; intuition eauto.
      + rewrite H0 by auto.
        apply replay_redo.
        * pred.
        * destruct (eq_nat_dec a (x1 (LogStart xp + m0 * 2))); subst; eauto; pred.
          eexists; intuition eauto; pred.
        * pred.
          disjoint xp.
      + pred.
      + pred.
      + eapply validLog_irrel; eauto; pred.
      + apply upd_same; pred.
        rewrite H9 by auto.
        apply replay_redo.
        * pred.
        * destruct (eq_nat_dec a (x1 (LogStart xp + m0 * 2))); subst; eauto; pred.
        * pred.
          disjoint xp.
    - eauto 12.
    - left; intuition.
      pred.
      firstorder.
  Qed.

  Definition commit xp := $(mem:
    (LogCommit xp) <-- 1;;
    (Call (apply_ok xp))
  ).

  Theorem commit_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (commit xp)
    {{r, rep xp (NoTransaction m2)
      \/ ([r = Crashed] /\ (rep xp (ActiveTxn (m1, m2)) \/
                            rep xp (CommittedTxn m2)))}}.
  Proof.
    intros; hoare_ghost m2.
    eexists; intuition eauto.
    eexists; intuition eauto.
    - eapply validLog_irrel; eauto; pred.
    - erewrite replay_irrel; eauto; pred.
  Qed.

  Definition abort xp := $(unit:
    (LogLength xp) <-- 0
  ).

  Theorem abort_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (abort xp)
    {{r, rep xp (NoTransaction m1)
      \/ ([r = Crashed] /\ rep xp (ActiveTxn (m1, m2)))}}.
  Proof.
    hoare.
  Qed.

  Definition recover xp := $(mem:
    com <- !(LogCommit xp);
    If (eq_nat_dec com 1) {
      (Call (apply_ok xp))
    } else {
      Halt tt
    }
  ).

  Theorem recover_ok : forall xp m m', {{rep xp (NoTransaction m) \/
                                         rep xp (ActiveTxn (m, m')) \/
                                         rep xp (CommittedTxn m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ (rep xp (NoTransaction m) \/
                            rep xp (CommittedTxn m)))}}.
  Proof.
    intros; hoare_ghost m.
  Qed.

  Definition read xp a := $((mem*mem):
    len <- !(LogLength xp);
    v <- !a;
    (Temp xp) <-- v;;

    For i < len
      Ghost old_cur
      Invariant (
        [DataStart xp <= a < DataStart xp + DataLen xp]
        /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> fst old_cur a)
        /\ (LogCommit xp) |-> 0
        /\ (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> snd old_cur a = replay (LogStart xp) len m a]
            /\ [m (Temp xp) = replay (LogStart xp) i m a])
      OnCrash rep xp (ActiveTxn old_cur) Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        v <- !(LogStart xp + i*2 + 1);
        (Temp xp) <-- v
      } else {
        Halt tt
      }
    Pool;;

    (!(Temp xp))
  ).

  Theorem read_ok : forall xp a ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (read xp a)
    {{r, rep xp (ActiveTxn ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.
  Proof.
    hoare.

    - eauto 7.

    - eexists; intuition eauto.
      + eapply validLog_irrel; eauto; pred.
      + erewrite replay_irrel; eauto; pred.
      + pred.

    - eauto 20.
    - eauto 20.
    - eauto 20.

    - left; intuition.
      + pred.
      + eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.
        * pred.
          symmetry.
          rewrite upd_eq; pred.

    - eauto 20.

    - left; intuition.
      eexists; intuition eauto.
      pred.

    - eauto 10.
    - eauto 10.

    - rewrite H9.
      rewrite <- H6; auto.
  Qed.

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

  Theorem write_ok : forall xp a v ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (write xp a v)
    {{r, rep xp (ActiveTxn (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (ActiveTxn ms))}}.
  Proof.
    hoare.

    - right; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.

    - right; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.

    - left; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * pred.
          eapply validLog_irrel; eauto; pred.
        * pred.
          apply upd_same; pred.
          rewrite H11 by auto.
          erewrite replay_irrel; eauto; pred.
  Qed.
End Log.

Definition write_two_blocks xp a1 a2 v1 v2 := $(mem:
  (Call (fun m: mem => Log.begin_ok xp m));;
  (Call (fun m: mem => Log.write_ok xp a1 v1 (m, m)));;
  (Call (fun m: mem => Log.write_ok xp a2 v2 (m, upd m a1 v1)));;
  (Call (fun m: mem => Log.commit_ok xp m (upd (upd m a1 v1) a2 v2)))
).

Theorem write_two_blocks_ok: forall xp a1 a2 v1 v2 m,
  {{[DataStart xp <= a1 < DataStart xp + DataLen xp]
    /\ [DataStart xp <= a2 < DataStart xp + DataLen xp]
    /\ Log.rep xp (NoTransaction m)}}
  (write_two_blocks xp a1 a2 v1 v2)
  {{r, Log.rep xp (NoTransaction (upd (upd m a1 v1) a2 v2))
    \/ ([r = Crashed] /\ (Log.rep xp (NoTransaction m) \/
                          (exists ms, [fst ms = m] /\ Log.rep xp (ActiveTxn ms)) \/
                          Log.rep xp (CommittedTxn (upd (upd m a1 v1) a2 v2))))}}.
Proof.
  hoare.
  - right. intuition eauto. right. left. eexists. split; eauto. eauto.
  - right. intuition eauto. right. left. eexists. split; eauto. eauto.
  - right. intuition eauto. right. left. eexists. split; eauto. eauto.
  - right. intuition eauto. right. left. eexists. split; eauto. eauto.
  - right. intuition eauto. right. left. eexists. split; eauto. eauto.
  - right. intuition eauto. right. left. eexists. split; eauto. eauto.
Qed.


Inductive recovery_result (R:Set) :=
| RHalted (v : R)
| RRecovered.
Implicit Arguments RHalted [R].
Implicit Arguments RRecovered [R].

Inductive exec_tryrecover xp : mem -> mem -> result unit -> Prop :=
| XTROK : forall m m' r,
  exec m (Log.recover xp) m' r ->
  exec_tryrecover xp m m' r
| XTRCrash : forall m m' m'' r,
  exec_tryrecover xp m m' Crashed ->
  exec m' (Log.recover xp) m'' r ->
  exec_tryrecover xp m m'' r.

Inductive exec_recover xp : forall {R : Set}, mem -> prog R -> mem -> recovery_result R -> Prop :=
| XROK : forall (R:Set) m (p:prog R) m' v,
  exec m p m' (Halted v) ->
  exec_recover xp m p m' (RHalted v)
| XRCrash : forall (R:Set) m (p:prog R) m' m'',
  exec m p m' Crashed ->
  exec_tryrecover xp m' m'' (Halted tt) ->
  exec_recover xp m p m'' RRecovered.

Inductive recover_corr xp : forall {R : Set},
     pred        (* precondition *)
  -> prog R      (* program *)
  -> (R -> pred) (* postcondition if halted *)
  -> pred        (* postcondition if crashed and recovered *)
  -> Prop :=
| RCbase : forall (R:Set) pre (p:prog R) post postcrash,
  corr pre p post ->
  corr (post Crashed) (Log.recover xp) postcrash ->
  corr (postcrash Crashed) (Log.recover xp) postcrash ->
  recover_corr xp pre p (fun r => post (Halted r)) (postcrash (Halted tt)).

Hint Constructors recover_corr.

Parameter the_xp : xparams.
Notation "{{ pre }} p {{ r , postok }} {{ postcrash }}" :=
  (recover_corr the_xp (pre)%pred p (fun r => postok)%pred (postcrash)%pred)
  (at level 0, p at level 9).

Require Import Eqdep.
Ltac deexistT :=
  match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
  end.

Ltac invert_exec :=
  match goal with
  | [ H: exec _ _ _ _ |- _ ] => apply invert_exec in H
  end.

Theorem recover_corr_sound: forall xp R pre p postok postcrash,
  @recover_corr xp R pre p postok postcrash ->
  forall m m' rr,
  exec_recover xp m p m' rr ->
  pre m ->
  ((exists v, rr = RHalted v /\ postok v m') \/
   (rr = RRecovered /\ postcrash m')).
Proof.
  destruct 1.
  intros m m' rr Hexec Hpre.
  inversion Hexec; clear Hexec; repeat deexistT.
  - left; eexists; intuition eauto; subst.
    eapply corr_sound; eauto.
  - right; intuition eauto; subst.
    match goal with
    | [ H: exec_tryrecover _ _ _ _ |- _ ] => induction H
    end.
    + eapply corr_sound with (pre:=(post Crashed)); eauto.
      eapply corr_sound; eauto.
    + eapply corr_sound with (pre:=(postcrash Crashed)); eauto.
Qed.

Theorem write_two_blocks_ok2: forall xp a1 a2 v1 v2 m,
  {{[DataStart xp <= a1 < DataStart xp + DataLen xp]
    /\ [DataStart xp <= a2 < DataStart xp + DataLen xp]
    /\ Log.rep xp (NoTransaction m)}}
  (write_two_blocks xp a1 a2 v1 v2)
  {{r, Log.rep xp (NoTransaction (upd (upd m a1 v1) a2 v2))}}
  {{Log.rep xp (NoTransaction m)}}.
Proof.
  intros.
