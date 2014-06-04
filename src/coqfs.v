Require Import Arith.
Require Import CpdtTactics.

Inductive diskblock :=
  | Data : nat -> diskblock.

Definition disk := nat -> diskblock.

Definition empty_disk : disk :=
  fun n => Data 0.

Definition disk_write (addr:nat) (val:nat) (d:disk) : disk :=
  fun n => if eq_nat_dec n addr then Data val else d n.

Definition disk_read (addr:nat) (d:disk) : nat :=
  match d addr with
  | Data n => n
  end.


Inductive flaky_disk :=
  | FlakyDisk : disk -> nat -> flaky_disk
  | GoodDisk : disk -> flaky_disk.

Definition flaky_init (d:disk) (n:nat) := FlakyDisk d n.

Definition flaky_fix (fd:flaky_disk) : flaky_disk :=
  match fd with
  | FlakyDisk d _ => GoodDisk d
  | GoodDisk d => GoodDisk d
  end.

Definition flaky_write (addr:nat) (val:nat) (fd:flaky_disk) : flaky_disk :=
  match fd with
  | FlakyDisk _ 0 => fd
  | FlakyDisk d (S k) => FlakyDisk (disk_write addr val d) k
  | GoodDisk d => GoodDisk (disk_write addr val d)
  end.

Definition flaky_read (addr:nat) (fd:flaky_disk) : nat :=
  match fd with
  | FlakyDisk d _ => disk_read addr d
  | GoodDisk d => disk_read addr d
  end.


Definition inc (addr:nat) (fd:flaky_disk) : flaky_disk :=
  let old := flaky_read addr fd in
  flaky_write addr (old+1) fd.


Theorem inc_ok:
  forall fd fd' addr k,
  flaky_read addr fd = k /\ inc addr fd = fd' ->
  flaky_read addr fd = k \/ flaky_read addr fd = (k+1).
Proof.
  crush.
Qed.


Definition log_apply (fd:flaky_disk) : flaky_disk :=
  match flaky_read 0 fd with
  | 0 => fd
  | S _ =>
    let a0 := flaky_read 1 fd in
    let a1 := flaky_read 2 fd in
    let d0 := flaky_read 3 fd in
    let d1 := flaky_read 4 fd in
    flaky_write 0 0 (flaky_write a0 d0 (flaky_write a1 d1 fd))
  end.

Definition log_doubleinc (addr:nat) (fd:flaky_disk) : flaky_disk :=
  let fd0 := log_apply fd in
  let d0 := flaky_read (addr+5) fd0 in
  let d1 := flaky_read (addr+6) fd0 in
  let fd1 := flaky_write 0 1
            (flaky_write 1 (addr+5)
            (flaky_write 2 (addr+6)
            (flaky_write 3 (d0+1)
            (flaky_write 4 (d1+1) fd0)))) in
  log_apply fd1.

Definition log_read (addr:nat) (fd:flaky_disk) : nat :=
  let fd0 := log_apply fd in
  flaky_read (addr+5) fd0.


Lemma disk_read_eq:
  forall d a x,
  disk_read a (disk_write a x d) = x.
Proof.
  intros; unfold disk_read; unfold disk_write.
  destruct (eq_nat_dec a a); crush.
Qed.

Lemma disk_read_same:
  forall d a a' x,
  a = a' -> disk_read a (disk_write a' x d) = x.
Proof.
  intros; unfold disk_read; unfold disk_write.
  destruct (eq_nat_dec a a'); crush.
Qed.

Lemma disk_read_other:
  forall d a a' x,
  a <> a' -> disk_read a (disk_write a' x d) = disk_read a d.
Proof.
  intros; unfold disk_read; unfold disk_write.
  destruct (eq_nat_dec a a'); crush.
Qed.

(*
 * Sketchy heuristics for what is "same" and what is "other".
 * Can easily run into non-provable situations (e.g. applying
 * disk_read_other when the addresses are actually equal..)
 *)
Ltac rewrite_disk_ops :=
  simpl;
  repeat (rewrite disk_read_eq in *);
  repeat (rewrite disk_read_other with (a:=S _) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+1) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+2) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=0) (a':=S _) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=0) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=0) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=1) (a':=2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=2) (a':=1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=3) (a':=1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=3) (a':=2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=4) (a':=1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=4) (a':=2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=4) (a':=3) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=S (_+1)) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=S _) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=S (_+1)) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+1) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+2) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=0) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=S _) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+1) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+2) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+5) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+1+5) (a':=_+1+5) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+1+5) (a':=_+6) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+5) (a':=_+1+5) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+1+5) (a':=_+5) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+5) (a':=_+5) in *; [idtac|crush]).

Theorem doubleinc_init_nocrash:
  forall fd addr,
  log_doubleinc addr (flaky_fix (flaky_init empty_disk 0)) = fd ->
  log_read addr     fd = 1 /\
  log_read (addr+1) fd = 1.
Proof.
  intros.
  unfold log_doubleinc in H.
  unfold log_apply in H.
  unfold flaky_read in H.
  unfold log_read.
  unfold log_apply.
  rewrite <- H; clear H.

  repeat rewrite_disk_ops; auto.
Qed.

Theorem doubleinc_nocrash:
  forall fd' fd addr a b,
  flaky_read 0 fd' = 0 ->
  log_read addr     fd' = a ->
  log_read (addr+1) fd' = b ->
  log_doubleinc addr (flaky_fix fd') = fd ->
  log_read addr     fd = (a+1) /\
  log_read (addr+1) fd = (b+1).
Proof.
  (* XXX *)
Abort.

(*
Theorem doubleinc_init_crash:
  forall n fd addr,
  log_doubleinc addr (flaky_init empty_disk n) = fd ->
  (log_read addr     (flaky_fix fd) = 0 /\
   log_read (addr+1) (flaky_fix fd) = 0) \/
  (log_read addr     (flaky_fix fd) = 1 /\
   log_read (addr+1) (flaky_fix fd) = 1).
Proof.
  intros.
  destruct (lt_dec n 1).

  (* crash before commit point *)
  left.  destruct n; crush.

  (* crash after commit point *)
  right.
  unfold log_doubleinc in H.
  unfold log_apply in H.
  unfold flaky_read in H.
  unfold log_read.
  unfold log_apply.
  rewrite <- H; clear H.
  simpl.

  destruct n.  crush.
  repeat rewrite_disk_ops.
  destruct n.
  repeat rewrite_disk_ops; auto.
  repeat rewrite_disk_ops.
  destruct n.
  repeat rewrite_disk_ops; auto.
  repeat rewrite_disk_ops.
  destruct n.
  repeat rewrite_disk_ops; auto.
  repeat rewrite_disk_ops; auto.
Qed.

Theorem log_apply_crash:
  forall fd,
  log_apply (flaky_fix (log_apply fd)) = log_apply (flaky_fix fd).
Proof.
  (* XXX *)
Abort.
*)
