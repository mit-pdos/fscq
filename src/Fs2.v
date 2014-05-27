Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

(* An alternative definition of legal histories.  Note that this
 * definition treats histories "backwards": writing and then reading
 * a file is represented by: (Read 1) :: (Write 1) :: nil.
 *)

Inductive event : Set :=
  | Read: nat -> event
  | Write: nat -> event
  | Flush: nat -> event
  | Sync: event
  | Crash: event.

Definition history := list event.

(* (last_flush h n) means n was the last thing flushed in h *)
Inductive last_flush: history -> nat -> Prop :=
  | last_flush_read:
    forall (h:history) (n:nat) (rn:nat),
    last_flush h n -> last_flush ((Read rn) :: h) n
  | last_flush_write:
    forall (h:history) (n:nat) (wn:nat),
    last_flush h n -> last_flush ((Write wn) :: h) n
  | last_flush_flush:
    forall (h:history) (n:nat),
    last_flush ((Flush n) :: h) n
  | last_flush_sync:
    forall (h:history) (n:nat),
    last_flush h n -> last_flush (Sync :: h) n
  | last_flush_crash:
    forall (h:history) (n:nat),
    last_flush h n -> last_flush (Crash :: h) n
  | last_flush_nil:
    last_flush nil 0.

Ltac invert_last_flush :=
  match goal with 
  | [ H1: last_flush ?T ?n  |- _ ] => 
    crush; inversion H1; clear H1
  end.

Theorem test_last_flush_1:
  last_flush [ Read 1 ; Crash ; Flush 1 ; Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ] 1.
Proof.
  repeat constructor.
Qed.
      
Theorem test_last_flush_2:
  ~ last_flush [ Read 1 ; Crash ; Flush 1 ; Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ] 0.
Proof.
  crush.
  repeat invert_last_flush.
Qed.

(* (could_read h n) means n could be the return value of a read *)
Inductive could_read: history -> nat -> Prop :=
  | could_read_read:
    forall (h:history) (n:nat) (rn:nat),
    could_read h n -> could_read ((Read rn) :: h) n
  | could_read_write:
    forall (h:history) (n:nat),
    could_read ((Write n) :: h) n
  | could_read_flush:
    forall (h:history) (n:nat) (fn:nat),
    could_read h n -> could_read ((Flush fn) :: h) n
  | could_read_sync:
    forall (h:history) (n:nat),
    could_read h n -> could_read (Sync :: h) n
  | could_read_crash:
    forall (h:history) (n:nat),
    last_flush h n -> could_read (Crash :: h) n
  | could_read_nil:
    could_read nil 0.

Theorem test_could_read_1:
  could_read [ Read 1 ; Crash ; Flush 1 ; Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ] 1.
Proof.
  repeat constructor.
Qed.

Theorem test_could_read_2:
  could_read [ Read 0; Crash ; Flush 0 ; Write 1 ; Write 0 ] 0.
Proof.
  repeat constructor.
Qed.

Theorem test_could_read_3:
  could_read [ Read 0; Crash ; Write 1 ; Write 0 ] 0.
Proof.
  repeat constructor.
Qed.

Ltac invert_could_read := 
  match goal with 
  | [ H1: could_read ?T ?n  |- _ ] => 
    crush; inversion H1; clear H1
  end.

Inductive could_flush: history -> nat -> Prop :=
  | could_flush_read:
    forall (h:history) (n:nat) (rn:nat),
    could_flush h n -> could_flush ((Read rn) :: h) n
  | could_flush_write_1:
    forall (h:history) (n:nat),
    could_flush ((Write n) :: h) n
  | could_flush_write_2:
    forall (h:history) (n:nat) (wn:nat),
    could_flush h n -> could_flush ((Write wn) :: h) n
  | could_flush_flush:
    forall (h:history) (n:nat) (fn:nat),
    could_flush h n -> could_flush ((Flush fn) :: h) n
  | could_flush_sync:
    forall (h:history) (n:nat),
    could_read h n -> could_flush (Sync :: h) n
  | could_flush_crash:
    forall (h:history) (n:nat),
    last_flush h n -> could_flush (Crash :: h) n
  | could_flush_nil:
    could_flush nil 0.


Theorem test_could_flush_1:
  could_flush [ Flush 1; Write 1 ; Write 0 ] 1.
Proof.
  repeat constructor.
Qed.

Theorem test_could_flush_2:
  could_flush [ Flush 1; Write 1 ; Sync; Write 0 ] 1.
Proof.
  repeat constructor.
Qed.

Theorem test_could_flush_3:
  could_flush [ Write 1 ;Flush 1; Write 0 ] 1.
Proof.
  repeat constructor.
Qed.

Ltac invert_could_flush := 
  match goal with 
  | [ H: could_flush ?T ?n  |- _ ] => 
    crush; inversion H; clear H
  | [ H1: last_flush ?T ?n  |- _ ] => 
    crush; inversion H1; clear H1
  end.

Theorem test_could_flush_4:
  ~could_flush [ Flush 1; Write 0 ] 1.
Proof.
  crush.
  repeat invert_could_flush.
Qed.

Theorem test_could_flush_5:
  ~could_flush [ Flush 1; Crash; Write 1 ] 1.
Proof.
  crush.
  repeat invert_could_flush.
Qed.

Ltac invert_history :=
  try invert_last_flush || invert_could_read.

Theorem test_could_read_4:
  ~ could_read [ Read 0; Crash ; Write 1 ; Write 0 ] 1.
Proof.
  crush.
  repeat invert_history.
Qed.

Inductive legal: history -> Prop :=
  | legal_read:
    forall (h:history) (n:nat),
    could_read h n ->
    legal h -> legal ((Read n) :: h)
  | legal_write:
    forall (h:history) (n:nat),
    legal h -> legal ((Write n) :: h)
  | legal_flush:
    forall (h:history) (n:nat),
    could_flush h n ->
    legal h ->
    legal ((Flush n) :: h)
  | legal_sync:
    forall (h:history) (n:nat),
    could_read h n ->
    last_flush h n ->
    legal h ->
    legal (Sync :: h)
  | legal_crash:
    forall (h:history),
    legal h -> legal (Crash :: h)
  | legal_nil:
    legal nil.

(* Prove some properties about the spec, to build confidence.. *)

Theorem legal_monotonic:
  forall h e,
  legal (e::h) -> legal h.
Proof.
  destruct e; intro; inversion H; crush.
Qed.

Lemma last_flush_unique:
  forall h a b,
  last_flush h a -> last_flush h b -> a = b.
Proof.
  induction h.
  - crush.  inversion H.  inversion H0.  crush.
  - destruct a; intros; inversion H; inversion H0; crush.
Qed.

Lemma could_read_unique:
  forall h a b,
  could_read h a -> could_read h b -> a = b.
Proof.
  induction h.
  - crush.  inversion H.  inversion H0.  crush.
  - destruct a; intros; inversion H; inversion H0; crush.
    apply last_flush_unique with (h:=h); crush.
Qed.

Theorem legal_repeat_reads:
  forall h a b,
  legal ((Read a) :: (Read b) :: h) -> a = b.
Proof.
  intros.
  inversion H.
  inversion H2.
  inversion H3.
  apply could_read_unique with (h:=h); crush.
Qed.

(* Some explicit test cases *)

Theorem test_legal_1:
  legal [ Read 1 ; Crash ; Write 0 ; Sync ; Flush 1 ; Write 1 ].
Proof.
  constructor.
  - repeat constructor.
  - constructor.  constructor.
    apply legal_sync with (n:=1); repeat constructor.
Qed.

Theorem test_legal_0:
  legal [ Read 0 ; Crash ; Flush 0 ; Write 0 ; Sync ; Flush 1 ; Write 1 ].
Proof.
  constructor.
  - repeat constructor.
  - constructor.  constructor.
    + repeat constructor.
    + constructor.  apply legal_sync with (n:=1).
      * repeat constructor.
      * constructor.
      * repeat constructor.
Qed.

Theorem test_legal_nondeterm_0:
  legal [ Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ].
Proof.
  repeat constructor.
Qed.

Theorem test_legal_nondeterm_1:
  legal [ Read 1 ; Crash ; Flush 1 ; Write 1 ; Write 0 ].
Proof.
  repeat constructor.
Qed.

Ltac invert_legal_step :=
  match goal with
  | [ H: legal _ |- _ ] => inversion H; clear H; crush
  | [ H: could_read _ _ |- _ ] => inversion H; clear H; crush
  | [ H: could_flush _ _ |- _ ] => inversion H; clear H; crush
  | [ H: last_flush _ _ |- _ ] => inversion H; clear H; crush
  end.

Theorem Test_legal_weird_1:
  ~ legal [ Read 1 ; Crash ; Read 0 ; Crash ; Flush 1 ; Write 1 ; Write 0 ].
Proof.
  crush.
  repeat invert_legal_step.
Qed.

Theorem test_legal_weird_2:
  ~ legal [ Read 1 ; Crash ; Flush 1 ; Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ].
Proof.
  crush.
  repeat invert_legal_step.
Qed.

(* Toy implementations of a file system *)

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: nat -> invocation
  | do_sync: invocation
  | do_crash: invocation.

(* Eager file system *)

Definition eager_state := nat.

Definition eager_init := 0.

Definition eager_apply (s: eager_state) (i: invocation) (h: history) : eager_state * history :=
  match i with
  | do_read => (s, (Read s) :: h)
  | do_write n => (n, (Flush n) :: (Write n) :: h)
  | do_sync => (s, Sync :: h)
  | do_crash => (s, Crash :: h)
  end.

(* Lazy file system *)

Record lazy_state : Set := mklazy {
  LazyMem: nat;
  LazyDisk: nat
}.

Definition lazy_init := mklazy 0 0.

Definition lazy_apply (s: lazy_state) (i: invocation) (h: history) : lazy_state * history :=
  match i with
  | do_read => (s, (Read s.(LazyMem)) :: h)
  | do_write n => (mklazy n s.(LazyDisk), (Write n) :: h)
  | do_sync => (mklazy s.(LazyMem) s.(LazyMem), Sync :: (Flush s.(LazyMem)) :: h)
  | do_crash => (mklazy s.(LazyDisk) s.(LazyDisk), Crash :: h)
  end.

(* What does it mean for a file system to be correct? *)

Fixpoint fs_apply_list (state_type: Set)
                       (fs_init: state_type)
                       (fs_apply: state_type -> invocation -> history -> state_type * history)
                       (l: list invocation)
                       : state_type * history :=
  match l with
  | i :: rest =>
    match fs_apply_list state_type fs_init fs_apply rest with
    | (s, h) => fs_apply s i h
    end
  | nil => (fs_init, nil)
  end.

Definition fs_legal (state_type: Set)
                     (fs_init: state_type)
                     (fs_apply: state_type -> invocation -> history -> state_type * history) :=
  forall (l: list invocation) (h: history) (s: state_type),
  fs_apply_list state_type fs_init fs_apply l = (s, h) ->
  legal h.

(* Eager FS is correct *)

Hint Constructors last_flush.
Hint Constructors could_read.
Hint Constructors could_flush.
Hint Constructors legal.

Lemma eager_last_flush:
  forall (l: list invocation) (s: eager_state) (h: history),
  fs_apply_list eager_state eager_init eager_apply l = (s, h) ->
  last_flush h s.
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    crush.
Qed.

Lemma eager_could_read:
  forall (l: list invocation) (s: eager_state) (h: history),
  fs_apply_list eager_state eager_init eager_apply l = (s, h) ->
  could_read h s.
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    crush.
    + constructor.  apply eager_last_flush with (l:=l).  crush.
Qed.

Theorem eager_correct:
  fs_legal eager_state eager_init eager_apply.
Proof.
  unfold fs_legal.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    crush.
    + constructor.
      * apply eager_could_read with (l:=l).  crush.
      * apply IHl with (s:=s).  crush.
    + repeat constructor.
      apply IHl with (s:=e).  crush.
    + apply legal_sync with (n:=s).
      * apply eager_could_read with (l:=l).  crush.
      * apply eager_last_flush with (l:=l).  crush.
      * apply IHl with (s:=s).  crush.
    + constructor.  apply IHl with (s:=s).  crush.
Qed.

(* Lazy FS correct *)

Lemma lazy_last_flush:
  forall (l: list invocation) (s: lazy_state) (h: history),
  fs_apply_list lazy_state lazy_init lazy_apply l = (s, h) ->
  last_flush h (LazyDisk s).
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    crush.
Qed.

Lemma lazy_could_read:
  forall (l: list invocation) (s: lazy_state) (h: history),
  fs_apply_list lazy_state lazy_init lazy_apply l = (s, h) ->
  could_read h (LazyMem s).
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    crush.
    + constructor.  apply lazy_last_flush with (l:=l).  crush.
Qed.

Lemma could_read_2_could_flush:
  forall h v,
  could_read h v ->
  could_flush h v.
Proof.
  induction h.
  - crush.  inversion H.  crush.
  - destruct a; intros; inversion H; crush.
Qed.

Theorem lazy_correct:
  fs_legal lazy_state lazy_init lazy_apply.
Proof.
  unfold fs_legal.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    crush.
    + constructor.
      * apply lazy_could_read with (l:=l).  crush.
      * apply IHl with (s:=s).  crush.
    + constructor.  apply IHl with (s:=l0).  crush.
    + apply legal_sync with (n:=(LazyMem l0)).
      * constructor.  apply lazy_could_read with (l:=l).  crush.
      * constructor.
      * constructor.
        apply could_read_2_could_flush.
        apply lazy_could_read with (l:=l).  crush.
        apply IHl with (s:=l0).  crush.
    + constructor.  apply IHl with (s:=l0).  crush.
Qed.

(* Haogang-style flushless spec *)

Inductive write_since_crash: history -> nat -> Prop :=
  | write_since_crash_read:
    forall (h:history) (n:nat) (rn:nat),
    write_since_crash h n -> write_since_crash ((Read rn) :: h) n
  | write_since_crash_write:
    forall (h:history) (n:nat),
    write_since_crash ((Write n) :: h) n
  | write_since_crash_sync:
    forall (h:history) (n:nat),
    write_since_crash h n -> write_since_crash (Sync :: h) n.

Inductive hpstate: history -> nat -> Prop :=
  | hpstate_write_1:
    forall (h:history) (n:nat),
    hpstate ((Write n) :: h) n
  | hpstate_write_2:
    forall (h:history) (n:nat) (wn:nat),
    hpstate h n -> hpstate ((Write wn) :: h) n
  | hpstate_read_1:
    forall (h:history) (n:nat),
    (~ exists (wn:nat), write_since_crash h wn) ->
    hpstate ((Read n) :: h) n
  | hpstate_read_2:
    forall (h:history) (n:nat) (rn:nat) (wn:nat),
    write_since_crash h wn -> hpstate h n -> hpstate ((Read rn) :: h) n
  | hpstate_sync_1:
    forall (h:history) (n:nat),
    (~ exists (wn:nat), write_since_crash h wn) ->
    hpstate h n -> hpstate (Sync :: h) n
  | hpstate_sync_2:
    forall (h:history) (n:nat),
    write_since_crash h n -> hpstate (Sync :: h) n
  | hpstate_crash:
    forall (h:history) (n:nat),
    hpstate h n -> hpstate (Crash :: h) n
  | hpstate_nil:
    hpstate nil 0.

Inductive hread: history -> nat -> Prop :=
  | hread_write:
    forall (h:history) (n:nat),
    hread ((Write n) :: h) n
  | hread_read:
    forall (h:history) (n:nat),
    hread h n -> hread ((Read n) :: h) n
  | hread_sync:
    forall (h:history) (n:nat),
    hread h n -> hread (Sync :: h) n
  | hread_crash:
    forall (h:history) (n:nat),
    hpstate h n -> hread (Crash :: h) n
  | hread_nil:
    hread nil 0.

Inductive hlegal: history -> Prop :=
  | hlegal_sync:
    forall (h:history),
    hlegal h -> hlegal (Sync :: h)
  | hlegal_crash:
    forall (h:history),
    hlegal h -> hlegal (Crash :: h)
  | hlegal_write:
    forall (h:history) (n:nat),
    hlegal h -> hlegal ((Write n) :: h)
  | hlegal_read:
    forall (h:history) (n:nat),
    hlegal h -> hread h n -> hlegal ((Read n) :: h)
  | hlegal_nil:
    hlegal nil.

Lemma hlegal_double_read:
  forall h x y,
  hlegal ((Read x) :: (Read y) :: h) -> x = y.
Proof.
  intros.
  inversion H; crush.
  inversion H3; crush.
Qed.

Hint Constructors hlegal.
Hint Constructors hread.
Hint Constructors hpstate.
Hint Constructors write_since_crash.

(* Prove that every legal history with flushes
 * is also legal in the Haogang sense.
 *)

Fixpoint drop_flush (h:history) : history :=
  match h with
  | nil => nil
  | a::b =>
    match a with
    | Flush _ => drop_flush b
    | _ => a :: drop_flush b
    end
  end.

Lemma write_since_crash_dec:
  forall h,
  (exists wn, write_since_crash (drop_flush h) wn) +
  (~ exists wn, write_since_crash (drop_flush h) wn).
Proof.
  induction h.
  - right.  crush.  inversion H.
  - destruct IHh.
    + destruct a.
      * left.  crush.  exists x.  crush.
      * left.  exists n.  constructor.
      * left.  crush.
      * left.  crush.  exists x.  crush.
      * right.  crush.  inversion H.
    + destruct a.
      * right.  crush.  inversion H.  apply n.  exists x.  crush.
      * left.  exists n0.  constructor.
      * right.  crush.
      * right.  crush.  inversion H.  apply n.  exists x.  crush.
      * right.  crush.  inversion H.
Qed.

Lemma last_flush_2_could_flush:
  forall h n,
  legal h -> last_flush h n -> could_flush h n.
Proof.
  induction h.
  - crush.  inversion H0.  crush.
  - intros.
    assert (legal h); [ apply legal_monotonic with (e:=a); auto | idtac ].
    destruct a; inversion H0; crush.
    * constructor.  inversion H.  auto.
    * constructor.  inversion H.
      assert (n=n0); [ apply last_flush_unique with (h:=h); crush | idtac ].
      crush.
Qed.

Lemma could_read_write_since_crash:
  forall h n wn,
  could_read h n ->
  write_since_crash (drop_flush h) wn ->
  n = wn.
Proof.
  induction h.
  - crush.  inversion H0.
  - destruct a; simpl; intros; inversion H; inversion H0; crush.
Qed.

Lemma read_flush_nowrite:
  forall h x y,
  legal h ->
  could_read h x ->
  could_flush h y ->
  (~ (exists wn, write_since_crash (drop_flush h) wn)) ->
  x = y.
Proof.
  induction h.
  - crush.  inversion H0.  inversion H1.  reflexivity.
  - intros.
    assert (legal h); [ apply legal_monotonic with (e:=a); auto | idtac ].
    destruct a; simpl; inversion H0; inversion H1; crush.
    + apply IHh; auto.
      intros.  apply H2.  crush.  exists x0.  crush.
    + assert False.  apply H2.  exists x.  crush.  crush.
    + apply IHh; auto.
      * apply could_read_2_could_flush; auto.
      * intros.  apply H2.  crush.  exists x0.  crush.
    + apply last_flush_unique with (h:=h); auto.
Qed.

Theorem could_flush_hpstate:
  forall h n,
  legal h -> could_flush h n -> hpstate (drop_flush h) n.
Proof.
  induction h.
  - intros.  inversion H0.  crush.
  - intros.
    assert (legal h); [ apply legal_monotonic with (e:=a); auto | idtac ].
    destruct a; crush; inversion H0; crush.
    + destruct (write_since_crash_dec h).
      * crush.  apply hpstate_read_2 with (wn:=x); crush.
      * inversion H.
        cut (n0=n).  crush.
        apply read_flush_nowrite with (h:=h); auto.
    + destruct (write_since_crash_dec h).
      * inversion H.  apply hpstate_sync_2.  crush.
        assert (n=x); [ apply could_read_write_since_crash with (h:=h); crush | crush ].
      * apply hpstate_sync_1; crush.  apply IHh; crush.  apply could_read_2_could_flush.  auto.
    + constructor.  apply IHh; crush.  apply last_flush_2_could_flush; auto.
Qed.

Theorem could_read_hread:
  forall h n,
  legal h -> could_read h n -> hread (drop_flush h) n.
Proof.
  induction h.
  - intros.  inversion H0.  crush.
  - intros.
    assert (legal h); [ apply legal_monotonic with (e:=a); crush | idtac ].
    destruct a; crush; inversion H; inversion H0; crush.
    + assert (n=n0); [ apply could_read_unique with (h:=h); crush | idtac ].
      crush.
    + constructor.  apply could_flush_hpstate; crush.
      apply last_flush_2_could_flush; crush.
Qed.

Theorem flush_irrelevant:
  forall h,
  legal h -> hlegal (drop_flush h).
Proof.
  induction h.
  - crush.
  - destruct a; simpl; intros; inversion H; crush.
    constructor; auto.
    apply could_read_hread; auto.
Qed.

(* Lazy file system with lazy reading *)

Record lazy2_state : Set := mklazy2 {
  Lazy2Mem: option nat;
  Lazy2Disk: nat
}.

Definition lazy2_init := mklazy2 None 0.

Definition lazy2_apply (s: lazy2_state) (i: invocation) (h: history) : lazy2_state * history :=
  match i with
  | do_read =>
    match s.(Lazy2Mem) with
    | None => (mklazy2 (Some s.(Lazy2Disk)) s.(Lazy2Disk), (Read s.(Lazy2Disk)) :: h)
    | Some x => (s, (Read x) :: h)
    end
  | do_write n => (mklazy2 (Some n) s.(Lazy2Disk), (Write n) :: h)
  | do_sync =>
    match s.(Lazy2Mem) with
    | None => (s, Sync :: h)
    | Some x => (mklazy2 (Some x) x, Sync :: (Flush x) :: h)
    end
  | do_crash => (mklazy2 None s.(Lazy2Disk), Crash :: h)
  end.

(* Lazy file system with lazy reading is correct *)

Lemma lazy2_could_read:
  forall (l: list invocation) (s: lazy2_state) (h: history) (x: nat),
  fs_apply_list lazy2_state lazy2_init lazy2_apply l = (s, h) ->
  (Lazy2Mem s) = Some x ->
  could_read h x.
Proof.
  admit.
Qed.

Lemma lazy2_could_read_disk:
  forall (l: list invocation) (s: lazy2_state) (h: history),
  fs_apply_list lazy2_state lazy2_init lazy2_apply l = (s, h) ->
  (Lazy2Mem s) = None ->
  could_read h (Lazy2Disk s).
Proof.
  admit.
Qed.

Lemma lazy2_last_flush:
  forall (l: list invocation) (s: lazy2_state) (h: history),
  fs_apply_list lazy2_state lazy2_init lazy2_apply l = (s, h) ->
  last_flush h (Lazy2Disk s).
Proof.
  admit.
Qed.

Theorem lazy2_correct:
  fs_legal lazy2_state lazy2_init lazy2_apply.
Proof.
  unfold fs_legal.
  induction l.
  - crush.
  - destruct a; simpl.
    + intros.
      case_eq (fs_apply_list lazy2_state lazy2_init lazy2_apply l).
      crush.
      rewrite H0 in H.
      destruct l0.  destruct Lazy2Mem0.
      * simpl in H.  inversion H.
        constructor.  apply lazy2_could_read with (l:=l) (s:=({| Lazy2Mem := Some n; Lazy2Disk := Lazy2Disk0 |})).
        crush.  crush.  apply IHl with (s:=({| Lazy2Mem := Some n; Lazy2Disk := Lazy2Disk0 |})).  crush.
      * simpl in H.  inversion H.
        constructor.  apply lazy2_could_read_disk with (l:=l) (s:=({| Lazy2Mem := None; Lazy2Disk := Lazy2Disk0 |})).
        crush.  crush.  crush.
        apply IHl with (s:=({| Lazy2Mem := None; Lazy2Disk := Lazy2Disk0 |})).  crush.
    + intros.
      case_eq (fs_apply_list lazy2_state lazy2_init lazy2_apply l).
      crush.
      rewrite H0 in H.
      inversion H.
      constructor.
      apply IHl with (s:=l0).  crush.
    + intros.
      case_eq (fs_apply_list lazy2_state lazy2_init lazy2_apply l).
      crush.
      rewrite H0 in H.
      destruct l0.  destruct Lazy2Mem0.
      * simpl in H.  inversion H.
        apply legal_sync with (n:=n).
        constructor.  apply lazy2_could_read with (l:=l) (s:=({| Lazy2Mem := Some n; Lazy2Disk := Lazy2Disk0 |})); crush.
        constructor.
        constructor.  apply could_read_2_could_flush.  apply lazy2_could_read with (l:=l) (s:=({| Lazy2Mem := Some n; Lazy2Disk := Lazy2Disk0 |})); crush.
        apply IHl with (s:=({| Lazy2Mem := Some n; Lazy2Disk := Lazy2Disk0 |})).  crush.
      * simpl in H.  inversion H.
        apply legal_sync with (n:=(Lazy2Disk s)).
        apply lazy2_could_read_disk with (l:=l) (s:=s); crush.
        apply lazy2_last_flush with (l:=l); crush.
        apply IHl with (s:=({| Lazy2Mem := None; Lazy2Disk := Lazy2Disk0 |})).  crush.
    + intros.
      case_eq (fs_apply_list lazy2_state lazy2_init lazy2_apply l).
      crush.
      rewrite H0 in H.
      inversion H.
      constructor.
      apply IHl with (s:=l0).  crush.
Qed.
