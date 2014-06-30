Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Require Import Trans.
Load Closures.

(* language that implements the log as a disk *)

Inductive ddisk :=
  | NDataDisk
  | NLogDisk.
  

Inductive dprog :=
  | DRead   (d:ddisk) (b:block) (rx:value -> dprog)
  | DWrite  (d:ddisk) (b:block) ( v:value) (rx:dprog)
  | DHalt.
 

Definition ATx := 0.
Definition AEol := 1.
Definition ABlk (i:nat) := i * 2 + 2.
Definition AVal (i:nat) := i * 2 + 3.

Bind Scope dprog_scope with dprog.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : dprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : dprog_scope.

Open Scope dprog_scope.

Definition do_tread b rx : dprog :=
  v <- DRead NDataDisk b; rx v.

Definition do_twrite b v rx : dprog :=
  DWrite NDataDisk b v ;; rx.

(* XXX taddlog is atomic. *)
Definition do_taddlog b v rx : dprog :=
  idx <- DRead NLogDisk AEol;
  DWrite NLogDisk (AVal idx) v ;;
  DWrite NLogDisk (ABlk idx) b ;;
  DWrite NLogDisk AEol (S idx) ;;
  rx.

Definition do_tclrlog rx : dprog :=
  DWrite NLogDisk AEol 0 ;; rx.

Fixpoint dreadlog idx eol log rx: dprog :=
  match idx with
  | O => rx log
  | S n => 
    b <- DRead NLogDisk (ABlk (eol - idx));
    v <- DRead NLogDisk (AVal (eol - idx));
    dreadlog n eol (log ++ [(b, v)]) rx
  end.

Definition do_tgetlog rx : dprog :=
  eol <- DRead NLogDisk AEol;
  dreadlog eol eol nil rx.

Definition bool2nat (v : bool) : nat :=
   match v with
   | true => 1
   | _ => 0
   end.

Definition nat2bool (v : nat) : bool :=
   match v with
   | 1 => true
   | _ => false
   end.

Definition do_tcommit rx : dprog :=
  DWrite NLogDisk ATx (bool2nat true) ;; rx.

Definition do_tgetcommitted rx : dprog :=
  v <- DRead NLogDisk ATx; rx (nat2bool v).

Close Scope dprog_scope.

Fixpoint compile_pd (p:tprog) : dprog :=
  match p with
  | THalt         => DHalt
  | TRead b rx    => do_tread b (fun v => compile_pd (rx v))
  | TWrite b v rx => do_twrite b v (compile_pd rx)
  | TAddLog b v rx  => do_taddlog b v (compile_pd rx)
  | TClrLog rx      => do_tclrlog (compile_pd rx)
  | TCommit rx     => do_tcommit (compile_pd rx)
  | TGetCommitted rx    => do_tgetcommitted (fun v => compile_pd (rx v))
  | TGetLog rx      => do_tgetlog (fun v => compile_pd (rx v))
  end.

Record dstate := DSt {
  DSProg: dprog;
  DSDataDisk: storage;
  DSLogDisk: storage
}.

(* An interpreter for the language that implements a log as a disk *)

Fixpoint dexec (p:dprog) (s:dstate) {struct p} : dstate :=
  let (_, dd, ld) := s in
  match p with
  | DHalt           => s
  | DRead d b rx    =>
    match d with
    | NDataDisk => dexec (rx (st_read dd b)) (DSt (rx (st_read dd b)) dd ld)
    | NLogDisk  => dexec (rx (st_read ld b)) (DSt (rx (st_read ld b)) dd ld)
    end
  | DWrite d b v rx =>
    match d with
    | NDataDisk => dexec rx (DSt rx (st_write dd b v) ld)
    | NLogDisk => dexec rx (DSt rx dd (st_write ld b v))
    end
  end.

Definition log_init := DSt DHalt st_init st_init.

Inductive dsmstep : dstate -> dstate -> Prop :=
  | DsmHalt: forall d l,
    dsmstep (DSt DHalt d l) (DSt DHalt d l)
  | DsmRead: forall dd d l b rx,
       dsmstep (DSt (DRead dd b rx) d l)
               (match dd with 
                  | NDataDisk => (DSt (rx (st_read d b)) d l)
                  | NLogDisk =>  (DSt (rx (st_read l b)) d l)
               end)
  | DsmWrite: forall dd d l b v rx,
    dsmstep (DSt (DWrite dd b v rx) d l)
               (match dd with 
                  | NDataDisk => (DSt rx (st_write d b v) l)
                  | NLogDisk =>  (DSt rx d (st_write l b v))
               end)
  .


Inductive tdmatch : tstate -> dstate -> Prop :=
  | PDMatchState :
    forall tp tdisk tlg tcommit dp dd lgd
    (DD: tdisk = dd)
    (TX: tcommit = match lgd ATx with
         | 1 => true
         | _ => false
         end)
    (* XXX match lg with lgd *)
    (PD: compile_pd tp = dp) ,
    tdmatch (TSt tp tdisk tlg tcommit) (DSt dp dd lgd).
  

Theorem pd_forward_sim:
  forall P1 P2, tsmstep P1 P2 ->
  forall D1, tdmatch P1 D1 ->
  exists D2, star dsmstep D1 D2 /\ tdmatch P2 D2.
Proof.
  Ltac t2 := simpl in *; subst; try autorewrite with core in *;
            intuition (eauto; try congruence).
  Ltac cc2 := t2; try constructor; t2.

  induction 1; intros; inversion H.

  (* PRead *)
  eexists; split.
  eapply star_step.
  cc2.
  cc2.
  cc2.

  (* Pwrite *)
  eexists; split.
  eapply star_step.
  cc2.
  cc2.
  cc2.

  (* PHalt *)
  (* exists D1; t2; apply star_refl. *)
Admitted.

  
(* XXX need to reformulate as pd_atomicity
Theorem dcorrect:
  forall p dd dd' ld ld' lg lg' d tx s,
  
  star dsmstep_fail (DSt (compile_pd p) dd ld lg) (DSt DHalt dd' ld' lg') ->
  pexec p (PSt p d nil tx) = s ->
  pdmatch s (DSt DHalt dd' ld' lg').
Proof.
  intros; eexists.
  inversion H.
Admitted.
*)
