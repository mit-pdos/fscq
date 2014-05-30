Require Import List.
Require Import CpdtTactics.
Require Import Monad.
Import ListNotations.

(* Initial state *)
Definition IS : state := 0.

(* Definition of event and trace. 
 * Note that this definition treats histories "backwards": writing and then
 * reading a file is represented by: (Read 1) :: (Write 1) :: nil.
 *)

Inductive event : Set :=
  | Read: state -> event
  | Write: state -> event
  | Sync: event
  | Crash: event.

Definition trace := list event.

Inductive last_write_since_crash : trace -> state -> Prop :=
  | last_write_read:  forall (t:trace) (s rs:state),
    last_write_since_crash t s -> last_write_since_crash ((Read rs) :: t) s
  | last_write_sync:  forall (t:trace) (s:state),
    last_write_since_crash t s -> last_write_since_crash (Sync :: t) s
  | last_write_write: forall (t:trace) (s:state),
    last_write_since_crash ((Write s) :: t) s.

Let no_write_since_crash (t:trace) : Prop :=
  ~ exists (s:state), last_write_since_crash t s.

Inductive could_persist : trace -> state -> Prop :=
  | persist_nil:
    could_persist nil IS
  | persist_write:       forall (t:trace) (s:state),
    could_persist ((Write s) :: t) s
  | persist_sync:        forall (t:trace) (s:state),
    last_write_since_crash t s -> could_persist (Sync :: t) s
  | persist_crash_intro: forall (t:trace) (s:state),
    could_persist t s -> could_persist (Crash :: t) s
  | persist_write_intro: forall (t:trace) (s ws:state),
    could_persist t s -> could_persist ((Write ws) :: t) s
  | persist_read_intro:  forall (t:trace) (s rs:state),
    last_write_since_crash t rs -> could_persist t s -> could_persist ((Read rs) :: t) s
  | persist_read:        forall (t:trace) (s:state),
    no_write_since_crash t -> could_persist t s -> could_persist ((Read s) :: t) s
  | persist_sync_intro:  forall (t:trace) (s:state),
    no_write_since_crash t -> could_persist t s -> could_persist (Sync :: t) s.

Inductive trace_legal : trace -> Prop :=
  | trace_legal_nil:
    trace_legal nil
  | trace_legal_sync_intro:       forall (t:trace),
    trace_legal t -> trace_legal (Sync :: t)
  | trace_legal_crash_intro:      forall (t:trace),
    trace_legal t -> trace_legal (Crash :: t)
  | trace_legal_write_intro:      forall (t:trace) (s:state),
    trace_legal t -> trace_legal ((Write s) :: t)
  | trace_legal_read_after_write: forall (t:trace) (s:state),
    last_write_since_crash t s -> trace_legal t -> trace_legal ((Read s) :: t)
  | trace_legal_read_after_crash: forall (t:trace) (s:state),
    no_write_since_crash t -> could_persist t s -> trace_legal t -> trace_legal ((Read s) :: t).

(* Some theorems *)

Lemma legal_subtrace:
  forall (t:trace) (e:event),
  trace_legal (e :: t) -> trace_legal t.
Proof.
  intros.
  inversion H; crush.
Qed.

Lemma last_write_uniqueness:
  forall (t:trace), uniqueness (last_write_since_crash t).
Proof.
  unfold uniqueness.  crush. 
  induction H; inversion H0; crush.
Qed.

Ltac write_contradict :=
  match goal with
  | H1: last_write_since_crash ?T ?s, 
    H2: no_write_since_crash ?T |- _ =>
      unfold no_write_since_crash in H2; destruct H2; exists s; assumption
  | H1: last_write_since_crash ?T ?a,
    H2: last_write_since_crash ?T ?b |- _ =>
      apply last_write_uniqueness with (t:=T); crush
  | _ => idtac
  end.

Lemma read_immutability:
  forall (t:trace) (a b: state),
  trace_legal ((Read a) :: (Read b) :: t) -> a = b.
Proof.
  intros.  inversion H.
  - inversion H3; inversion H2; write_contradict.
  - inversion H4.
    + apply last_write_read with (rs:=b) in H7;  write_contradict.
    + inversion H3; crush; write_contradict.
Qed.

Lemma read_get_last_write :
  forall (t:trace) (s ws:state),
  trace_legal ((Read s) :: t) -> last_write_since_crash t ws -> s = ws.
Proof.
  intros.
  inversion H.
  - apply last_write_uniqueness with (t:=t). assumption. assumption.
  - write_contradict.
Qed.

Lemma write_complement:
  forall (t:trace),
  (exists (s:state), last_write_since_crash t s) \/ no_write_since_crash t.
Proof.
  induction t; unfold no_write_since_crash.
  - right. crush. inversion H.
  - unfold no_write_since_crash in IHt; destruct IHt; destruct a.
    + left. crush. exists x. constructor. assumption.
    + left. exists s. constructor.
    + left. crush. exists x. constructor. assumption.
    + right. crush. inversion H0.
    + right. crush. inversion H0. apply H. exists x. assumption.
    + left. exists s. constructor.
    + right. crush. inversion H0. apply H. exists x. assumption.
    + right. crush. inversion H0.
Qed.

Lemma sync_before_read_irrelevence:
  forall (t:trace) (s:state),
  trace_legal ((Read s) :: Sync :: t) -> trace_legal ((Read s) :: t).
Proof.
  intros. inversion H; inversion H3.
  - inversion H2.
    cut (trace_legal (Read s ::t)); crush. 
    apply trace_legal_read_after_write; crush.
  - destruct H2. exists s. constructor. assumption.
  - inversion H4. apply trace_legal_read_after_crash; crush.
Qed.

Corollary readability :
  forall (t:trace) (s ws:state),
  trace_legal ((Read s) :: t) ->
  ((last_write_since_crash t ws -> s = ws) \/ could_persist t s).
Proof.
  intros.
  destruct (write_complement t).
  - left. intro. apply read_get_last_write with (t:=t); crush.
  - right. inversion H.
    + write_contradict.
    + assumption.
Qed.

Hint Constructors trace_legal.
Hint Constructors last_write_since_crash.
Hint Constructors could_persist.

(* Lemma for testing equivalence for inductive version. Build confidence. *)

Inductive could_read : trace -> state -> Prop :=
  | could_read_nil:
    could_read nil IS
  | could_read_write: forall (t:trace) (s:state),
    could_read ((Write s) :: t) s
  | could_read_crash: forall (t:trace) (s:state),
    could_persist t s -> could_read (Crash :: t) s
  | could_read_read:  forall (t:trace) (s:state),
    could_read t s -> could_read ((Read s) :: t) s
  | could_read_sync:  forall (t:trace) (s:state),
    could_read t s -> could_read (Sync :: t) s.

Hint Constructors could_read.

Ltac trace_resolve :=
  match goal with
  | |- no_write_since_crash ?T => 
        unfold no_write_since_crash; crush; inversion H
  | _ => constructor
  end.

Lemma could_read_write_uniqueness:
  forall (t:trace) (s ws:state),
  could_read t s -> last_write_since_crash t ws -> ws = s.
Proof.
  induction t.
  - crush. inversion H0.
  - destruct a; crush; inversion H; inversion H0; crush.
Qed.

Lemma could_read_persist:
  forall (t:trace) (s:state),
  could_read t s -> could_persist t s.
Proof.
  induction t; intros.
  - inversion H. crush.
  - destruct a; inversion H; crush.
    + destruct (write_complement t); crush.
      apply persist_read_intro; crush.
      replace s with x. assumption.
      apply could_read_write_uniqueness with (t:=t) (s:=s) (ws:=x); crush.
    + destruct (write_complement t); crush.
      apply persist_sync; crush.
      replace s with x. assumption.
      apply could_read_write_uniqueness with (t:=t) (s:=s) (ws:=x); crush.
Qed.

Lemma could_persist_read:
  forall (t:trace) (s:state),
  could_persist t s -> no_write_since_crash t -> could_read t s.
Proof.
  induction t; intros; unfold no_write_since_crash in H0.
  - inversion H. constructor.
  - destruct a; inversion H; crush.
    + contradict H0. apply last_write_read with (rs:=s0) in H3.
      exists s0. assumption.
    + contradict H0. exists s0. constructor.
    + contradict H0. exists s. constructor. assumption.
Qed.

Theorem legal_could_read :
  forall (t:trace) (s:state),
  trace_legal ((Read s) :: t) -> could_read t s.
Proof.
  induction t; intros.
  - inversion H. inversion H2. inversion H3. constructor.
  - destruct a.
    + assert (Hx:=H); apply read_immutability in Hx. crush.
      apply legal_subtrace in H.
      assert (Hx:=H); apply IHt in H. 
      constructor. assumption.
    + replace s0 with s. constructor. inversion H; crush.
      * inversion H2. reflexivity.
      * destruct H2. exists s0. constructor.
    + constructor.
      apply sync_before_read_irrelevence in H. crush.
    + constructor.
      inversion H. inversion H2. inversion H3. assumption.
Qed.

Theorem could_read_legal:
  forall (t:trace) (s:state),
  trace_legal t -> could_read t s -> trace_legal ((Read s) :: t).
Proof.
  intros. induction t.
  - inversion H0. apply trace_legal_read_after_crash;
    repeat trace_resolve. inversion H1.
  - inversion H0; destruct a; crush.
    + apply trace_legal_read_after_crash.
      trace_resolve. inversion H2.
      apply persist_crash_intro. assumption.
      inversion H0. inversion H. crush.
    + destruct (write_complement t).
      * constructor. apply legal_subtrace in H. crush.
        inversion H3. crush. write_contradict. crush.
      * apply trace_legal_read_after_crash.
        repeat trace_resolve; write_contradict.
        inversion H2. write_contradict.
        apply persist_read. assumption.
        apply could_read_persist. assumption. crush.
    + destruct (write_complement t).
      * constructor. apply legal_subtrace in H. crush.
        inversion H5. crush. write_contradict. crush.
      * apply trace_legal_read_after_crash.
        repeat trace_resolve; write_contradict.
        inversion H3. write_contradict.
        apply could_read_persist. assumption.
        assumption.
Qed.

(* Testing *)

Example test_1 : 
  trace_legal [ Read 1; Write 1; Read 0; Write 0; Sync; Read 1; Crash; Read 2; Write 2; Write 1 ] .
Proof.
  do 5 constructor.  apply trace_legal_read_after_crash;  repeat trace_resolve.
Qed.

Example test_2 :
  trace_legal [ Read 1; Crash; Read 3; Write 3; Crash; Write 2; Write 1 ] .
Proof.
  apply trace_legal_read_after_crash; repeat trace_resolve.
Qed.

Example test_3:
  trace_legal [ Read 1; Crash; Read 3; Sync; Write 3; Crash; Write 2; Write 1 ].
Proof.
  apply trace_legal_read_after_crash; repeat trace_resolve.
  Abort.

Example test_4:
  trace_legal [ Read 2; Crash; Read 3; Write 3; Read 1; Crash; Write 2 ; Write 1 ] .
Proof.
  apply trace_legal_read_after_crash; repeat trace_resolve.
  Abort.

Example test_5:
  trace_legal [ Read 1; Read 2; Crash;  Write 1; Write 2 ].
Proof.
  apply trace_legal_read_after_crash; repeat trace_resolve.
  Abort.


(* Base implementations of a file system *)

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: state -> invocation
  | do_sync: invocation
  | do_crash: invocation.

Inductive result : Set :=
  | rs_read: state -> result
  | rs_void: result.

Fixpoint fs_apply_list (fsstate: Set)
                       (init: fsstate)
                       (applyfun: fsstate -> invocation -> fsstate * result)
                       (l: list invocation)
                       : fsstate * trace :=
  match l with
  | i :: rest =>
    let (s, t) := fs_apply_list fsstate init applyfun rest in
    let (s', r) := applyfun s i in
      match i with
      | do_read => match r with
         | rs_read x => (s', Read x :: t)
         | rs_void   => (s', t) (* invalid *)
        end
      | do_write x => (s', Write x :: t)
      | do_sync => (s', Sync :: t)
      | do_crash => (s', Crash :: t)
      end
  | nil => (init, nil)
  end.

Definition fs_legal (fsstate: Set)
                     (init: fsstate)
                     (applyfun: fsstate -> invocation -> trace -> fsstate * trace) :=
  forall (l: list invocation) (t: trace) (s: fsstate),
  fs_apply_list fsstate init applyfun l = (s, t) ->
  trace_legal t.


(* Eager file system: sync after every write *)

Definition eager_state := storage.

Definition eager_init := st_init IS.

Definition eager_apply (s: eager_state) (i: invocation) (t: trace) : eager_state * trace :=
  match i with
  | do_read    => let io := IOread 0 s    in (fst io, (Read (snd io)) :: t)
  | do_write n => let io := IOwrite 0 n s in (fst io, Sync :: (Write n) :: t)
  | do_sync    => (s, Sync :: t)
  | do_crash   => (s, Crash :: t)
  end.

Ltac destruct_invocation :=
  match goal with
  | [ Ha : invocation, Hl : list invocation |- 
      forall _ _, fs_apply_list ?Ts ?Ti ?Ta _ = _ -> _ ] =>
      destruct Ha; simpl; case_eq (fs_apply_list Ts Ti Ta Hl)
  | [ Ha : invocation, Hl : list invocation |- 
      forall _ _ _, fs_apply_list ?Ts ?Ti ?Ta _ = _ -> _ ] =>
      destruct Ha; simpl; case_eq (fs_apply_list Ts Ti Ta Hl)
  | [ Ha : invocation, Hl : list invocation |- 
      forall _ _ _ _, fs_apply_list ?Ts ?Ti ?Ta _ = _ -> _ ] =>
      destruct Ha; simpl; case_eq (fs_apply_list Ts Ti Ta Hl)
  | _ => fail
  end.

Lemma eager_could_read:
  forall (l:list invocation) (s:eager_state) (t:trace),
  fs_apply_list eager_state eager_init eager_apply l = (s, t) ->
  could_read t (s 0).
Proof.
  induction l.
  - unfold eager_init. crush.
  - destruct_invocation; try st_rewrite; crush. constructor.
    + apply IHl in H.
      apply could_read_persist. assumption.
Qed.

Theorem eager_correct:
  fs_legal eager_state eager_init eager_apply.
Proof.
  unfold fs_legal.  induction l.
  - crush.
  - destruct_invocation; crush. 
    + assert (Hx:=H). apply IHl in H.
      apply could_read_legal. assumption.
      apply eager_could_read with (l:=l). assumption.
    + repeat constructor. apply IHl with (s:=e). assumption.
    + constructor. apply IHl with (s:=s). assumption.
    + constructor. apply IHl with (s:=s). assumption.
Qed.


(* Buffered file system with lazy reading and writing *)

Record buf_state : Set := mkbuf {
  BufMem: option state;
  BufDisk: storage
}.

Definition buf_init := mkbuf None (st_init IS).

Definition buf_apply (s: buf_state) (i: invocation) (t: trace) : buf_state * trace :=
  match i with
  | do_read =>
    match (BufMem s) with
    | None => let io := IOread 0 (BufDisk s) in
              (mkbuf (Some (snd io)) (fst io), (Read (snd io)) :: t)
    | Some x => (s, (Read x) :: t)
    end
  | do_write n => (mkbuf (Some n) (BufDisk s), (Write n) :: t)
  | do_sync =>
    match (BufMem s) with
    | None => (s, Sync :: t)
    | Some x => let io := IOwrite 0 x (BufDisk s) in
                (mkbuf (Some x) (fst io), Sync :: t)
    end
  | do_crash => (mkbuf None (BufDisk s), Crash :: t)
  end.

Lemma buf_empty_no_write:
  forall (l: list invocation) (b: buf_state) (t:trace),
  fs_apply_list buf_state buf_init buf_apply l = (b, t) ->
  (BufMem b) = None -> no_write_since_crash t.
Proof.
  unfold no_write_since_crash. induction l.
  - crush. inversion H1.
  - destruct_invocation; intros; 
    destruct (BufMem b) eqn:Hb; crush; inversion H2.
    apply IHl in H; crush. exists x. assumption.
Qed.

(* when there is a write, cached state always reflects the written state *)
Lemma buf_mem_eq:
  forall (l:list invocation) (b:buf_state) (t:trace) (s ws:state),
  fs_apply_list buf_state buf_init buf_apply l = (b, t) ->
  (BufMem b) = Some s -> last_write_since_crash t ws -> s = ws.
Proof.
  induction l.
  - crush.
  - destruct_invocation; crush.
    + (* read *)
      destruct (BufMem b) eqn:Hb; crush.
      * destruct (write_complement t); inversion H2.
        apply IHl with (s:=s) (ws:=ws) in H; assumption.
        inversion H2. write_contradict.
      * apply buf_empty_no_write with (l:=l) (b:=b) (t:=t) in Hb.
        inversion H2. write_contradict. assumption.
    + (* write *)
      inversion H2. reflexivity.
    + (* sync *)
      destruct (BufMem b) eqn:Hb; crush.
      inversion H2. apply IHl with (s:=s) (ws:=ws) in H; assumption.
Qed.

(* when no write, cached state always reflects disk state *)
Lemma buf_disk_eq:
  forall (l:list invocation) (b:buf_state) (t:trace) (s:state),
  fs_apply_list buf_state buf_init buf_apply l = (b, t) ->
  (BufMem b) = Some s -> no_write_since_crash t -> s = (BufDisk b 0).
Proof.
  induction l.
  - crush.
  - destruct_invocation; crush.
    + (* read *)
      destruct (BufMem b) eqn:Hb; crush.
      destruct (write_complement t).
      * destruct H0. unfold no_write_since_crash in H2.
        contradict H2. exists x. constructor. assumption.
      * apply IHl with (t:=t) in H1; assumption.
    + (* write *)
       unfold no_write_since_crash in H2.
      contradict H2. exists s0. constructor.
    + (* sync *)
      destruct (BufMem b) eqn:Hb; crush.
Qed.

(* state stored in disk is always valid *)
Lemma buf_disk_persist:
  forall (l: list invocation) (b: buf_state) (t:trace),
  fs_apply_list buf_state buf_init buf_apply l = (b, t) ->
  could_persist t (BufDisk b 0).
Proof.
  induction l. crush.
  destruct_invocation; crush.
    - (* read *)
      destruct (BufMem b) eqn:Hb; crush.
      + destruct (write_complement t).
        * assert (Hx:=H); apply IHl in H. apply persist_read_intro.
          destruct H0. replace x with s in H0. assumption.
          apply buf_mem_eq with (l:=l) (b:=b0) (t:=t); assumption.
          assumption.
        * assert (s=(BufDisk b0 0)).
          apply buf_disk_eq with (l:=l) (t:=t); assumption. crush.
      + apply persist_read.
        apply buf_empty_no_write with (l:=l) (b:=b); assumption. crush.
    - (* sync *)
      destruct (BufMem b) eqn:Hb; crush.
      + destruct (write_complement t).
        * inversion H0.  apply persist_sync.
          replace x with s in H1. assumption.
          apply buf_mem_eq with (l:=l) (b:=b) (t:=t); assumption.
        * apply persist_sync_intro. assumption.
          assert (Hx:=H); apply IHl in H. 
          replace s with (BufDisk b 0). assumption.
          apply eq_sym. apply buf_disk_eq with (l:=l) (t:=t); assumption.
      + assert (Hx:=H); apply IHl in H. apply persist_sync_intro.
        apply buf_empty_no_write with (l:=l) (b:=b0).
        assumption. assumption. assumption.
Qed.

(* after crash or before warm up, disk state is always valid *)
Lemma buf_could_read_disk:
  forall (l: list invocation) (b: buf_state) (t:trace),
  fs_apply_list buf_state buf_init buf_apply l = (b, t) ->
  (BufMem b) = None ->  could_read t (BufDisk b 0).
Proof.
  induction l.
  - crush.
  - destruct_invocation; intros; destruct (BufMem b) eqn:Hb; crush.
    + constructor. apply buf_disk_persist with (l:=l). assumption.
    + apply IHl in H. constructor. apply could_read_persist.
      assumption. assumption.
Qed.

(* state cached in the memory is always valid *)
Lemma buf_could_read_mem:
  forall (l: list invocation) (b: buf_state) (t:trace) (s:state),
  fs_apply_list buf_state buf_init buf_apply l = (b, t) ->
  (BufMem b) = Some s ->  could_read t s.
Proof.
  induction l. crush.
  destruct_invocation; crush.
  - (* read *)
    destruct (BufMem b) eqn:Hb; crush.
    + assert (Hx:=H1). apply IHl with (t:=t) (s:=s) in H.
      induction BufMem; crush. assumption.
    + constructor. apply buf_could_read_disk with (l:=l); assumption.
  - (* sync *)
    destruct (BufMem b) eqn:Hb; crush.
    + constructor. apply IHl with (s:=s) in H; assumption.
Qed.

Theorem buf_correct:
  fs_legal buf_state buf_init buf_apply.
Proof.
    unfold fs_legal.  induction l.
  - crush.
  - destruct_invocation; crush.
    + destruct (BufMem b) eqn:Hb ; inversion H0; simpl; subst.
      * apply could_read_legal with (t:=t) (s:=s0). 
        assert (Hx:=H); apply IHl with (s:=s). assumption.
        apply buf_could_read_mem with (l:=l) (b:=s) (s:=s0); assumption.
      * apply could_read_legal. apply IHl in H. assumption.
        apply buf_could_read_disk with (l:=l) (b:=b); assumption.
    + constructor. apply IHl with (s:=b). assumption.
    + destruct BufMem.
      * crush. constructor. apply IHl with (s:=b). assumption.
      * crush. constructor. apply IHl with (s:=s). assumption.
    + constructor. apply IHl with (s:=b). assumption.
Qed.


(* The most robust fs in the world *)

Definition nil_state := state.

Definition nil_init := IS.

Definition nil_apply (s: nil_state) (i: invocation) (t: trace) : nil_state * trace :=
  match i with
  | do_read    => (IS, t)
  | do_write n => (IS, (Write n) :: t)
  | do_sync    => (IS, Sync :: t)
  | do_crash   => (IS, Crash :: t)
  end.

Theorem nil_correct:
  fs_legal nil_state nil_init nil_apply.
Proof.
  unfold fs_legal. induction l.
  - crush.
  - destruct_invocation; crush; apply IHl in H; crush.
Qed.

