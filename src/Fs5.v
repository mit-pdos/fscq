Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

(* Disk with atomicity of n writes. Histories are "backwards": writing and then
reading a block with value n is represented by: (Read d n) :: (Write d n) ::
nil. *)

Definition value := nat.
Definition block := nat.
Definition trans := nat.

Inductive event : Set :=
  | Read: block -> value -> event
  | Write: block -> value -> event
  | Sync: block -> event   (* XXX don't apply to transactions; i.e., TEnd syncs *)
  | TBegin: trans -> event
  | TEnd: trans -> event
  | TSync: trans -> event
  | Crash: event.    (* what does it mean in begin and end: ignore? *)

Definition history := list event.

(* could start a transation means we are now outside any transaction *)
Inductive could_begin: history -> Prop :=
  | TBegin_nil:
    could_begin nil
  | TBegin_tend: forall h t,
    could_begin ((TEnd t) :: h)
  | TBegin_crash: forall h,
    could_begin (Crash :: h)
  | TBegin_read: forall h b v,
    could_begin h -> could_begin (Read b v :: h)
  | TBegin_write: forall h b v,
    could_begin h -> could_begin (Write b v :: h)
  | TBegin_sync: forall h b,
    could_begin h -> could_begin (Sync b :: h)
  | TBegin_tsync: forall h t,
    could_begin h -> could_begin (TSync t :: h).

(* we are now inside a transaction *)
Inductive in_tx: history -> trans -> Prop :=
  | InTX_tbegin: forall h t,
    in_tx (TBegin t :: h) t
  | InTX_read: forall h t b v,
    in_tx h t -> in_tx (Read b v :: h) t
  | InTX_write: forall h t b v,
    in_tx h t -> in_tx (Write b v :: h) t.

Lemma no_nested_tx:
  forall h t, could_begin h -> ~ in_tx h t.
Proof.
  induction h; intuition; intros.
  - inversion H0.
  - destruct a; inversion H; inversion H0; apply IHh with (t:=t); assumption.
Qed.

(* lastw b v holds when there is a write b v in h since the last crash *)
Inductive lastw: history -> block -> value -> Prop :=
  | LW_write: forall h b v,
    lastw (Write b v :: h) b v
  | LW_write_other: forall h b v wb wv,
    wb <> b -> lastw h b v -> lastw (Write wb wv :: h) b v
  | LW_read: forall h b v rb rv,
    lastw h b v -> lastw (Read rb rv :: h) b v
  | LW_sync: forall h b v sb,
    lastw h b v -> lastw (Sync sb :: h) b v
  | LW_tbegin: forall h b v t,
    lastw h b v -> lastw (TBegin t :: h) b v
  | LW_tend: forall h b v t,
    lastw h b v -> lastw (TEnd t :: h) b v
  | LW_tsync: forall h b v t,
    lastw h b v -> lastw (TSync t :: h) b v.

Let no_write h b : Prop := ~ exists v, lastw h b v.

Lemma lastw_unique:
  forall h b v v', lastw h b v -> lastw h b v' -> v = v'.
Proof.
  induction h; intros; [ inversion H | destruct a ];
  inversion H; inversion H0; crush; apply IHh with (b:=b); assumption.
Qed.

(* lastw for b is decidable: there is a unique last write to b or no write to b. *)
Lemma lastw_dec:
  forall h b, (exists v, lastw h b v) + no_write h b.
Proof.
  induction h; unfold no_write in *.
  - right; intuition; inversion H; inversion H0.
  - intros; destruct IHh with (b:=b); destruct a eqn:DA;
    (* trivial cases *)
    match goal with
    | [ DA: _ = Write _ _ |- _ ] => idtac
    | [ DA: _ = Crash     |- _ ] => right; intuition; inversion H; inversion H0
    | [ e: exists _, _ |- _ ] => 
        left; inversion e; exists x; constructor; assumption
    | [ e: ~ exists _, _ |- _ ] =>
        right; intuition; inversion H; inversion H0; apply n; exists x; assumption
    end.
    (* writes *)
    + left; destruct (eq_nat_dec b b0).
      * rewrite e0; exists v; constructor.
      * inversion e; exists x; constructor; auto; assumption.
    + destruct (eq_nat_dec b b0).
      * left; rewrite e; exists v; constructor.
      * right; intuition; apply n; inversion H; exists x. inversion H0; crush.
Qed.

(* what's a block's value after a transaction? *)
Inductive tx_write: history -> trans -> block -> value -> Prop :=
  | TW_write: forall h t b v,
    in_tx h t -> tx_write (Write b v :: h) t b v
  | TW_write_other: forall h t b v wb wv,
    wb <> b -> tx_write h t b v -> tx_write (Write wb wv :: h) t b v
  | TW_read: forall h t b v rb rv,
    tx_write h t b v -> tx_write (Read rb rv :: h) t b v
  | TW_sync: forall h t b v sb,
    tx_write h t b v -> tx_write (Sync sb :: h) t b v
  | TW_tbegin: forall h b v t ot,
    ot <> t -> tx_write h t b v -> tx_write (TBegin ot :: h) t b v
  | TW_tend: forall h b v t ot,
    tx_write h t b v -> tx_write (TEnd ot :: h) t b v
  | TW_tsync: forall h b v t ot,
    ot <> t -> tx_write h t b v -> tx_write (TSync ot :: h) t b v.

Inductive could_ondisk: history -> block -> value -> Prop :=
  | OD_nil: forall b,
    could_ondisk nil b 0
  (* write *)
  | OD_write: forall h b v t,
    ~ in_tx h t -> could_ondisk (Write b v :: h) b v
  | OD_write_other: forall h b v wb wv,
    could_ondisk h b v -> could_ondisk (Write wb wv :: h) b v
  (* sync *)
  | OD_sync_w: forall h b v,
    lastw h b v -> could_ondisk (Sync b :: h) b v
  | OD_sync_nw: forall h b v,
    no_write h b -> could_ondisk h b v -> could_ondisk (Sync b :: h) b v
  | OD_sync_other: forall h b v sb,
    sb <> b -> could_ondisk h b v -> could_ondisk (Sync sb :: h) b v
  (* read *)
  | OD_read_w: forall h b v wv,
    lastw h b wv -> could_ondisk h b v -> could_ondisk (Read b wv:: h) b v
  | OD_read_nw: forall h b v,
    no_write h b -> could_ondisk h b v -> could_ondisk (Read b v :: h) b v
  | OD_read_other: forall h b v rb rv,
    could_ondisk h b v -> could_ondisk (Read rb rv :: h) b v
  (* TSync *)
  | OD_tsync: forall h t b v,
    tx_write h t b v -> could_ondisk (TSync t :: h) b v
  | OD_tsync_other: forall h t b v,
    could_ondisk h b v -> could_ondisk (TSync t :: h) b v
  (* others *)
  | OD_crash: forall h b v,
    could_ondisk h b v -> could_ondisk (Crash :: h) b v
  | OD_tbegin: forall h b v t,
    could_ondisk h b v -> could_ondisk (TBegin t :: h) b v
  | OD_tend: forall h b v t,
    could_ondisk h b v -> could_ondisk (TEnd t :: h) b v.

Inductive could_read: history -> block -> value -> Prop :=
  | Read_write: forall h b v,
    lastw h b v -> could_read h b v
  | Read_crash: forall h b v,
    no_write h b -> could_ondisk h b v -> could_read h b v.

(* blegal h b means that h is legal for disk block b *)
Inductive blegal: history -> block -> Prop :=
  | BL_nil : forall b,
    blegal nil b
  | BL_read: forall h b rb rv,
    blegal h b -> blegal h rb -> could_read h rb rv -> blegal (Read rb rv :: h) b
  | BL_write: forall h b wb wv,
    blegal h b -> blegal h wb -> blegal (Write wb wv :: h) b
  | BL_sync: forall h b sb,
    blegal h b -> blegal h sb -> could_begin h -> blegal (Sync sb :: h) b
  | BL_crash: forall h b,
    blegal h b -> blegal (Crash :: h) b
  | BL_tbegin: forall h b t,
    blegal h b -> could_begin h -> blegal (TBegin t :: h) b
  | BL_tend: forall h b t,
    blegal h b -> in_tx h t -> blegal (TEnd t :: h) b
  | BL_tsync: forall h b t,
    blegal h b -> could_begin h -> blegal (TSync t :: h) b.

Let   legal h : Prop := forall b,   blegal h b.
Let illegal h : Prop := forall b, ~ blegal h b.

Example test_legal_1:
  legal [ Read 1 1 ;  Write 1 1 ].
Proof.
  intro.
  repeat constructor.
Qed.

Example test_legal_2:
  illegal [ Read 0 1 ;  Write 1 1 ].
Proof.
  intro. intuition.
  inversion H. inversion H6.
  - inversion H7.
    inversion H17.
  - inversion H8.
    inversion H17.
Qed.

Example test_legal_3:
  legal [ Read 0 1; Read 1 1 ; Write 0 1; Write 1 1 ].
Proof.
  intro.
  repeat constructor; auto.
Qed.

Example test_legal_4:
  legal [ Read 0 1 ; Read 1 1 ; TEnd 0; Write 0 1 ; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat constructor; auto.
Qed.

(* No syncs inside of a transaction: *)
Example test_legal_5:
  illegal [ Read 0 1 ; Read 1 1 ; TEnd 0; Write 0 1 ; Sync 1; Write 1 1 ; TBegin 0].
Proof.
  intro. intuition.
  inversion H. inversion H5. inversion H12. inversion H18. inversion H23.
Qed.

(* No writes of an incomplete transaction are visible after a crash: *)
Example test_legal_6:
  legal [ Read 1 0; Read 0 0 ; Crash; Write 1 1; Write 0 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor
  end.
Qed.

(* Results of a transactions are not durable: *)
Example test_legal_7:
  legal [ Read 0 0 ; Read 1 0 ; Crash; TEnd 0; Write 0 1 ; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor
  end.
Qed.

(* Sync makes transactions durable: *)
Example test_legal_8:
  legal [ Read 0 1 ; Read 1 1 ; Crash; TSync 0; TEnd 0; Write 0 1 ; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor; auto
  end.
Qed.

(* Sync makes all preceding transactions durable: *)
Example test_legal_9:
  legal [ Read 0 1 ; Read 1 1 ; Crash; TSync 1; TSync 0; TEnd 1; Write 0 1 ; TBegin 1; TEnd 0; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | [ |- could_ondisk _ _ _ ] => idtac
  | _ => constructor
  end; constructor.
  - apply OD_tsync_other; repeat constructor; auto.
  - apply OD_tsync_other; repeat constructor; auto.
  - repeat constructor; auto.
Qed.

(* After a crash, a new transaction must start with TBegin *)
Example test_legal_10:
   illegal [ Read 0 0 ; Read 0 0 ; TEnd 0; Write 0 1 ; Crash; Write 1 1 ; TBegin 0].
Proof.
  intro. intuition.
  inversion H. inversion H5. inversion H12. inversion H18. inversion H23.
Qed.

(* XXX [Sync 1; TEnd Write 1 1 TBegin] should be illegal.

(* XXX reads inside of a transaction should probably return the value of most
(perhaps unncommitted) write *)

(* A disk whose reads and writes don't fail *)

Definition addr := nat.
Definition val := nat.
Definition storage := addr -> val.

Parameter st_init  : storage.
Parameter st_write : storage -> addr -> val -> storage.
Parameter st_read  : storage -> addr -> val.

Axiom st_write_eq:
  forall s a v, st_write s a v a = v.

Axiom st_write_ne:
  forall s a v a', a <> a' -> st_write s a v a' = s a'.

Axiom st_read_eq:
  forall s a, st_read s a = s a.

Axiom st_read_init:
  forall a, st_read st_init a = 0.

Axiom disk_read_eq:
  forall s a v,
  st_read (st_write s a v) a = v.

Axiom disk_read_same:
  forall s a a' v,
  a = a' -> st_read (st_write s a' v) a = v.

Axiom disk_read_other:
  forall s a a' v,
  a <> a' -> st_read (st_write s a' v) a = st_read s a.

Lemma disk_read_write_commute:
  forall a a' v v' s,
  a <> a' -> st_read (st_write (st_write s a v) a' v') a =  st_read (st_write (st_write s a' v') a v) a.
Proof.
  intros.
  rewrite disk_read_eq.
  rewrite disk_read_other.
  rewrite disk_read_eq.
  trivial.
  trivial.
Qed.

(* The interface to an atomic disk: *)

Inductive invocation : Set :=
  | do_read: nat -> invocation
  | do_write: nat -> nat -> invocation
  | do_begin: invocation
  | do_end: invocation
  | do_crash: invocation.

(* An atomic abstract disk that implements the above interface with the above
spec. The abstract disk has a storage device and a list of actions in a
transactions that haven't been applied yet. They will be applied when the
transaction ends/commits atomically.  *)

Record TDisk: Set := mkTDisk {
  disk : storage;
  pending : list invocation   (* list of pending invocations in a transaction *)
}.

Definition Tdisk_apply (s: TDisk) (i: invocation) (h: history) : TDisk * history :=
  match i with
      | do_read d => (s, (Read d (st_read s.(disk) d)) :: h)
      | do_write d n => let disk1 := (st_write s.(disk) d n) in
                        ((mkTDisk disk1 s.(pending)),  (Write d n) :: h)
      | _ => (s, h)
  end.
  
Fixpoint apply_pending (s: TDisk) (l : list invocation) (h: history) : TDisk * history := 
  match l with
  | i :: rest =>
    let (s1, h1) := (apply_pending s rest h) in 
      (Tdisk_apply s1 i h1)
  | nil => (s, h)
  end.

Fixpoint apply_to_TDisk (s : TDisk) (l : list invocation) (h: history) : bool * TDisk * history := 
  match l with
  | i :: rest =>
    let (bDisk, h1) := (apply_to_TDisk s rest h) in
    let (intransaction, s1) := bDisk in
    match i with
    | do_begin => (true, s1, (TBegin :: h1))
    | do_end => (* apply pending list *)
      let (s2, h2) := (apply_pending s1 s1.(pending) h1) in
              (false, s2, (TEnd :: h2))
    | do_crash => (false, (mkTDisk s1.(disk) []), (Crash :: h1))    (* reset pending list *)
    | _ => 
      match intransaction with
      | true => (true, (mkTDisk s1.(disk) (i :: s1.(pending))), h1)
      | _ => let (s2, h2) := (Tdisk_apply s1 i h1) in
        (false, s2, h2)
      end
    end
  | nil => (false, s, h)
  end.

(* plan for getting some confidence (ie., fix spec and implementation): *)
Theorem TDisk_legal_1:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  crush.
  constructor.
Qed.

Theorem TDisk_legal_2:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [do_read 0; do_write 0 1] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  inversion H.
  rewrite disk_read_eq.
  repeat constructor.
Qed.

Theorem TDisk_legal_3:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [do_read 1; do_read 0; do_end; do_write 1 1; do_write 0 1; do_begin] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  inversion H.
  repeat rewrite disk_read_eq.
  rewrite disk_read_write_commute.
  repeat rewrite disk_read_eq.
  repeat constructor.
  trivial.
Qed.

Theorem TDisk_legal_4:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [do_read 0; do_crash; do_write 0 1; do_begin] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  inversion H.
  rewrite st_read_init.
  repeat constructor.
Qed.

(* the main unproven theorem: *)
Theorem TDisk_legal:
  forall (l: list invocation) (h: history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) l [] = (b, s, h) -> legal h d.
Proof.
  induction l; [crush; constructor | idtac].
  destruct a; case_eq (apply_to_TDisk (mkTDisk st_init []) l []);
  intros; simpl; inversion H0; rewrite H in H2; destruct p.
  - destruct b0.
    + inversion H2.  apply IHl with (s:=t) (b:=b).
      rewrite <- H5. rewrite <- H3. assumption.
    + inversion H2. 
      constructor; [ auto | apply IHl with (s:=t) (b:=false); assumption | idtac ].
      admit. (* need lemmas on legal -> could_read *)
  - destruct b0.
    + inversion H2. apply IHl with (s:=t) (b:=true). rewrite <- H5. assumption.
    + inversion H2.
      constructor; auto; apply IHl with (s:=t) (b:=false); assumption.
  - crush. constructor. apply IHl with (s:=s) (b:=b0). assumption.
  - admit. (* need lemmas on apply_pending -> legal *)
  - crush. constructor. apply IHl with (s:=t) (b:=b0). assumption.
Qed.

(* Use two disks to implement to implement the same behavior as Tdisk but with a
disk for which read or write to disk can crash (jelle's disk).  *)

Record AtomicDisk : Set := mkAtomicLazy2 {
  LogDisk : storage_fail;
  DataDisk : storage_fail
}.

Definition AtomicLazy2_init := mkAtomicLazy2 st_fail_init st_fail_init.

(* An implementation of the interface using logging.  Tend writes a commit
record, and then applies to the logged updates to the data disk.  On recovery,
atomic disk applies any committed logdisk updates to data disk. *)

(* A refinement proof that every state AtomicDisk can be in is a legal state of
Tdisk. The mapping function is something along the line if there is a commit
record, then the atomic disks DataDisk is Tdisk.disk with pending applied.  If
there is no commit record, then the atomic DataDisk is Tdisk.disk (i.e., w/o
pending applied) Maybe a la Nickolai's coqfs implementation? *)

(* Standard refinement conclusion: because AtomicDisk implements TDisk and Tdisk
is correct, then AtomicDisk is correct. *)
