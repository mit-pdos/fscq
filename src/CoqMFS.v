Require Import Arith.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.


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

Ltac destruct_eq_nat :=
  match goal with
  | [ |- context[if (eq_nat_dec ?X ?Y) then _ else _] ] => destruct (eq_nat_dec X Y)
  end.

Ltac crush_eq := repeat ( crush; destruct_eq_nat ).

Lemma disk_rw:
  forall a a' v d,
  (disk_read a (disk_write a' v d)) = 
  if eq_nat_dec a a' then v else disk_read a d.
Proof.
  unfold disk_read; unfold disk_write; crush_eq.
Qed.

Hint Rewrite disk_rw.

Opaque disk.
Opaque disk_read.
Opaque disk_write.


Inductive fdisk :=
  | FlakyDisk : disk -> nat -> fdisk.

Definition fdisk_reset (fd:fdisk) (n:nat) :=
  match fd with
  | FlakyDisk d _ => FlakyDisk d n
  end.

Definition fdisk_write (addr:nat) (val:nat) (fd:fdisk) : option fdisk :=
  match fd with
  | FlakyDisk _ 0 => None
  | FlakyDisk d (S k) => Some (FlakyDisk (disk_write addr val d) k)
  end.

Definition fdisk_read (addr:nat) (fd:fdisk) : nat :=
  match fd with
  | FlakyDisk d _ => disk_read addr d 
  end.

Lemma fdisk_rw:
  forall a a' v fd fd',
  fdisk_write a' v fd = Some fd' ->
  fdisk_read a fd' = if eq_nat_dec a a' then v else fdisk_read a fd.
Proof.
  destruct fd; destruct n; crush.
Qed.

Lemma fdisk_crash:
  forall a v fd,
  fdisk_write a v fd = None ->
  forall a' v',
  fdisk_write a' v' fd = None.
Proof.
  destruct fd; destruct n; crush.
Qed.


(* Monadic flaky disk *)
Definition mfdisk (R:Type) := fdisk -> (fdisk * option R).

Definition mret {R:Type} (x:R) : mfdisk R :=
  fun fd => (fd, Some x).

Definition mbind {A:Type} {B:Type} (a:mfdisk A) (f:A->mfdisk B) : mfdisk B :=
  fun fd =>
    match a fd with
    | (fd', Some av) => f av fd'
    | (fd', None) => (fd', None)
    end.

Definition mfdisk_write (addr:nat) (val:nat) : mfdisk unit :=
  fun fd =>
    match fdisk_write addr val fd with
    | None => (fd, None)
    | Some fd' => (fd', Some tt)
    end.

Definition mfdisk_read (addr:nat) : mfdisk nat :=
  fun fd =>
    (fd, Some (fdisk_read addr fd)).

Notation "a >>= f" := (mbind a f) (left associativity, at level 50).

Notation "'do' x <- y ; z" := (mbind y (fun x => z))
  (left associativity, at level 200, x ident, y at level 100, z at level 200).

Lemma mon_left_id:
  forall (A:Type) (a:A) (R:Type) (f:A->mfdisk R),
  mret a >>= f = f a.
Proof.
  crush.
Qed.

Lemma mon_right_id:
  forall (A:Type) (a:mfdisk A),
  a >>= mret = a.
Proof.
  intros; unfold mbind; apply functional_extensionality; intros.
  destruct (a x); destruct o; crush.
Qed.

Lemma mon_assoc:
  forall (A:Type) (a:mfdisk A)
         (B:Type) (f:A->mfdisk B)
         (C:Type) (g:B->mfdisk C),
  (a >>= f) >>= g = a >>= (fun x => (f x >>= g)).
Proof.
  intros; unfold mbind; apply functional_extensionality; intros.
  destruct (a x); destruct o; crush.
Qed.


Definition mfdisk_test_inc (addr:nat) : mfdisk unit :=
  do x <- mfdisk_read addr;
  do _ <- mfdisk_write addr (x+1);
  mret tt.

Lemma mfdisk_test_inc_works:
  forall fd fd' a,
  fd' = fst (mfdisk_test_inc a fd) ->
  (forall a', a <> a' -> fdisk_read a' fd' = fdisk_read a' fd) /\
  (fdisk_read a fd' = fdisk_read a fd \/
   fdisk_read a fd' = fdisk_read a fd + 1).
Proof.
  destruct fd; destruct n; crush_eq.
Qed.


(* A log partition *)
Definition log_blocks := 10.

Definition ldisk_log_read (addr: {a:nat|a<log_blocks}) :=
  mfdisk_read (proj1_sig addr).
Definition ldisk_log_write (addr: {a:nat|a<log_blocks}) (val:nat) :=
  mfdisk_write (proj1_sig addr) val.

Definition ldisk_data_read (addr:nat) :=
  mfdisk_read (addr+log_blocks).
Definition ldisk_data_write (addr:nat) (val:nat) :=
  mfdisk_write (addr+log_blocks) val.

