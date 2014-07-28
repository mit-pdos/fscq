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

Fixpoint Countdown (f : nat -> prog) (n : nat) : prog :=
  match n with
    | O => Halt
    | S n' => (f n');; (Countdown f n')
  end.

Theorem CCountdown : forall (f : nat -> prog)
  (nocrash : nat -> pred) (crashed : pred),
  (nocrash 0 --> crashed)
  -> forall n,
    (forall m, m < n
      -> {{nocrash (S m)}} (f m)
      {{r, ([r = Halted 0] /\ nocrash m) \/ ([r = Crashed] /\ crashed)}})
    -> {{nocrash n}} (Countdown f n)
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
  pred.
  simpl.
  intros.
  apply pimpl_refl.
  apply pimpl_refl.
  pred.
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
  | Countdown' (nocrash : ghostT -> nat -> pred) (crashed : ghostT -> pred)
    (f : nat -> prog') (n : nat).

  Fixpoint prog'Out (p : prog') : prog :=
    match p with
      | Halt' => Halt
      | Crash' => Crash
      | Read' a => Read a
      | Write' a v => Write a v
      | Seq' p1 p2 => Seq (prog'Out p1) (fun x => prog'Out (p2 x))
      | If' _ _ b p1 p2 => if b then prog'Out p1 else prog'Out p2
      | Countdown' _ _ f n => Countdown (fun x => prog'Out (f x)) n
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
      | Countdown' nocrash crashed f n => fun r =>
        ([r = Halted 0] /\ nocrash ghost 0) \/ ([r = Crashed] /\ crashed ghost)
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
      | Countdown' nocrash crashed f n =>
        (nocrash ghost 0 --> crashed ghost)
        /\ (pre --> nocrash ghost n)
        /\ (forall m, m < n -> vc (nocrash ghost (S m)) (f m))
        /\ (forall m r, m < n -> (spost (nocrash ghost (S m)) (f m) r -->
          ([r = Halted 0] /\ nocrash ghost m) \/ ([r = Crashed] /\ crashed ghost)))
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
    apply (@CCountdown _ (nocrash ghost) (crashed ghost)); auto.
    intros.
    eapply Conseq; [ | apply pimpl_refl | ]; eauto.
    auto.
    auto.
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

Notation "'Loop' i < n 'Ghost' g 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Pool'" :=
  (Countdown' (fun g i => nocrash%pred) (fun g => crashed%pred) (fun i => body) n)
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

Module Type LOG.
  (* Methods *)
  Parameter init : xparams -> prog.
  Parameter flush : xparams -> prog.
  Parameter read : xparams -> addr -> prog.
  Parameter write : xparams -> addr -> valu -> prog.

  (* Representation invariant *)
  Parameter rep : xparams
    -> mem (* Memory as modified by current transaction,
            * only consulted for addresses in data range *)
    -> pred.

  (* Specs *)
  Axiom init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, ([r = Crashed] /\ diskIs m) \/ rep xp m}}.

  Axiom read_ok : forall xp m a,
    {{[DataStart xp <= a < DataStart xp + DataLen xp] /\ rep xp m}}
    (read xp a)
    {{r, rep xp m /\ [r = Crashed \/ r = Halted (m a)]}}.

  Axiom write_ok : forall xp m a v,
    {{[DataStart xp <= a < DataStart xp + DataLen xp] /\ rep xp m}}
    (write xp a v)
    {{r, ([r = Crashed] /\ rep xp m) \/ rep xp (upd m a v)}}.
End LOG.

Module Log : LOG.
  Definition rep' xp (m : mem) (ls : list (addr * valu)) := (
    (* The right log length is stored. *)
    (LogLength xp) |-> (length ls)

    (* The log is not too long. *)
    /\ [length ls <= LogLen xp]

    (* Log entries are only for addresses within the data region. *)
    /\ [forall i a_v, nth_error (ls : list (addr * valu)) i = Some a_v
      -> DataStart xp <= fst a_v < DataStart xp + DataLen xp]

    (* This log is stored in the real memory. *)
    /\ (foral i a_v, [nth_error ls i = Some a_v]
      --> (LogStart xp + i*2) |-> (fst a_v))
    /\ (foral i a_v, [nth_error ls i = Some a_v]
      --> (LogStart xp + i*2 + 1) |-> (snd a_v))

    (* The final log entry for each address is in the abstract memory. *)
    /\ [forall i a_v, nth_error ls i = Some a_v
      -> (forall j a_v', j > i -> nth_error ls j = Some a_v'
        -> fst a_v' <> fst a_v)
      -> m (fst a_v) = snd a_v]

    (* Unupdated addresses are unchanged. *)
    /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
      --> [forall i a_v, nth_error ls i = Some a_v
        -> fst a_v <> a]
      --> a |-> m a)
  )%pred.

  Definition rep xp (m : mem) := (
    (* Quantify over log. *)
    exists ls, rep' xp m ls
  )%pred.


  Definition init xp := $(unit:
    (LogLength xp) <-- 0
  ).

  Definition flush xp := $(unit:
    len <- !(LogLength xp);
    Loop i < len
      Ghost _
      Invariant [True]
      OnCrash [True] Begin
      a <- !(LogStart xp + i*2);
      v <- !(LogStart xp + i*2 + 1);
      a <-- v
    Pool).

  Definition read xp a := $(mem:
    len <- !(LogLength xp);
    (Temp xp) <-- len;;

    Loop i < len
      Ghost m
      Invariant (exists ls, rep' xp m ls
        /\ [DataStart xp <= a < DataStart xp + DataLen xp]
        /\ (LogLength xp) |-> len
        /\ (((Temp xp) |-> len
          /\ [forall j a_v, j >= i
            -> nth_error ls j = Some a_v
            -> fst a_v <> a])
        \/ (exists k a_v, (Temp xp) |-> k
          /\ [nth_error ls k = Some a_v
            /\ fst a_v = a
            /\ forall j a_v', j > k
              -> nth_error ls j = Some a_v'
              -> fst a_v' <> a])))
      OnCrash rep xp m Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        tmp <- !(Temp xp);
        If (eq_nat_dec tmp len) {
          (Temp xp) <-- i
        } else {
          Halt
        }
      } else {
        Halt
      }
     Pool;;

     tmp <- !(Temp xp);
     If (eq_nat_dec tmp len) {
       !a
     } else {
       !(LogStart xp + tmp*2 + 1)
     }
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

  Lemma rep_nil : forall xp m,
    rep xp m (upd m (LogLength xp) 0).
  Proof.
    exists nil; unfold rep'; pred;
      try match goal with
            | [ _ : nth_error nil ?X = Some _ |- _ ] =>
              destruct X; discriminate
          end.
  Qed.

  Hint Resolve rep_nil.

  Theorem init_ok : forall xp m, {{diskIs m}} (init xp) {{r, ([r = Crashed] /\ diskIs m) \/ rep xp m}}.
  Proof.
    hoare.
  Qed.

  Lemma nth_error_bound : forall A v n (ls : list A),
    nth_error ls n = Some v
    -> n < length ls.
  Proof.
    induction n; destruct ls; simpl; intuition; discriminate.
  Qed.

  Ltac nth_error_bound :=
    match goal with
      | [ H : nth_error _ _ = Some _ |- _ ] =>
        specialize (nth_error_bound _ _ H); pred
    end.

  Lemma rep_write1 : forall xp m m' a,
    m' (LogLength xp) < LogLen xp
    -> rep xp m m'
    -> rep xp m (upd m' (LogStart xp + m' (LogLength xp) * 2) a).
  Proof.
    destruct 2 as [ls]; exists ls; unfold rep, rep' in *; pred;
      nth_error_bound.
  Qed.

  Hint Resolve rep_write1.

  Lemma rep_write2 : forall xp m m' a v,
    m' (LogLength xp) < LogLen xp
    -> rep xp m m'
    -> rep xp m (upd (upd m' (LogStart xp + m' (LogLength xp) * 2) a)
      (LogStart xp + m' (LogLength xp) * 2 + 1) v).
  Proof.
    destruct 2 as [ls]; exists ls; unfold rep, rep' in *; pred;
      nth_error_bound.
  Qed.

  Hint Resolve rep_write2.

  Hint Rewrite app_length.

  Lemma nth_error_end : forall A v v' n (ls : list A),
    nth_error (ls ++ v :: nil) n = Some v'
    -> (n < length ls /\ nth_error ls n = Some v')
    \/ (n = length ls /\ v = v').
  Proof.
    induction n; destruct ls; simpl; unfold value, error in *; intuition.
    intuition (try congruence).
    destruct n; discriminate.
    apply IHn in H; intuition.
  Qed.

  Lemma nth_error_end_preserve : forall A x v (ls : list A) n,
    nth_error ls n = Some v
    -> nth_error (ls ++ x :: nil) n = Some v.
  Proof.
    induction ls; destruct n; simpl; intuition; discriminate.
  Qed.

  Lemma nth_error_end_skip : forall A x (ls : list A),
    nth_error (ls ++ x :: nil) (length ls) = Some x.
  Proof.
    induction ls; simpl; intuition.
  Qed.

  Hint Resolve nth_error_end_preserve nth_error_end_skip.

  Lemma rep_write3 : forall xp m m' a v,
    m' (LogLength xp) < LogLen xp
    -> rep xp m m'
    -> DataStart xp <= a < DataStart xp + DataLen xp
    -> rep xp (upd m a v) (upd
      (upd (upd m' (LogStart xp + m' (LogLength xp) * 2) a)
        (LogStart xp + m' (LogLength xp) * 2 + 1) v)
      (LogLength xp) (S (m' (LogLength xp)))).
  Proof.
    destruct 2 as [ls]; exists (ls ++ (a, v) :: nil); unfold rep, rep' in *; pred;
      try match goal with
            | [ H : nth_error (_ ++ _ :: nil) _ = _ |- _ ] =>
              apply nth_error_end in H; intuition (subst; simpl);
                autorewrite with core; eauto
          end;
      match goal with
        | _ => rewrite upd_ne; eauto
        | [ H' : context[_ <= _ < _], H : nth_error _ _ = _ |- _ ] =>
          apply H' in H; tauto
      end.
  Qed.

  Hint Resolve rep_write3.

  Theorem write_ok : forall xp m a v,
    {{[DataStart xp <= a < DataStart xp + DataLen xp] /\ rep xp m}}
    (write xp a v)
    {{r, ([r = Crashed] /\ rep xp m) \/ rep xp (upd m a v)}}.
  Proof.
    hoare.
  Qed.

  Lemma unfold_rep : forall xp m m' ls,
    rep' xp m ls m'
    -> rep xp m m'.
  Proof.
    intros; hnf; eauto.
  Qed.

  Hint Resolve unfold_rep.

  Lemma rep'_Temp : forall xp m ls m' v,
    rep' xp m ls m'
    -> rep' xp m ls (upd m' (Temp xp) v).
  Proof.
    unfold rep'; pred; nth_error_bound.
  Qed.

  Hint Resolve rep'_Temp.

  Lemma nth_error_out_of_bound : forall xp m ls m' v j,
    rep' xp m ls m'
    -> j >= m' (LogLength xp)
    -> nth_error ls j = Some v
    -> False.
  Proof.
    unfold rep'; pred; nth_error_bound.
  Qed.

  Hint Immediate nth_error_out_of_bound.

  Lemma nth_error_exists : forall A (ls : list A) n,
    n < length ls
    -> exists v, nth_error ls n = Some v.
  Proof.
    induction ls; destruct n; simpl; intuition (omega || eauto).
    edestruct IHls; eauto; omega.
  Qed.

  Theorem read_ok : forall xp m a,
    {{[DataStart xp <= a < DataStart xp + DataLen xp] /\ rep xp m}}
    (read xp a)
    {{r, rep xp m /\ [r = Crashed \/ r = Halted (m a)]}}.
  Proof.
    hoare.

    destruct H4; eauto 9.
    
    left; intuition.
    exists x; intuition.
    right.
    assert (Hlen : x1 (LogLength xp) = length x)
      by (unfold rep' in *; pred).
    rewrite Hlen in H.
    apply nth_error_exists in H; destruct H.
    do 2 eexists; intuition eauto.
    unfold rep' in *; pred.
    symmetry; eauto.

    unfold rep' in *; nth_error_bound.

    eauto 14.

    left; intuition.
    eexists; intuition eauto.
    left; intuition subst.
    destruct (eq_nat_dec j m0); subst.
    unfold rep' in *; pred.
    eapply H8 in H2; eauto; omega.

    eauto 14.

    unfold rep' in *; pred.
    rewrite H11; intuition.
    eapply H7; [ | eauto | ]; eauto; omega.

    unfold rep' in *; nth_error_bound.

    unfold rep' in *; pred.
    erewrite H7 by eauto.
    erewrite H8; eauto.
  Qed.
End Log.
