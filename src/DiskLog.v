Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Util.
Require Import Storage.
Require Import MemLog.
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

Bind Scope fscq_scope with dprog.

Open Scope fscq_scope.


Definition do_pread b rx : dprog :=
  v <- DRead NDataDisk b; rx v.

Definition do_pwrite b v rx : dprog :=
  DWrite NDataDisk b v ;; rx.

(* XXX paddlog is atomic. *)
Definition do_paddlog b v rx : dprog :=
  idx <- DRead NLogDisk AEol;
  DWrite NLogDisk (AVal idx) v ;;
  DWrite NLogDisk (ABlk idx) b ;;
  DWrite NLogDisk AEol (S idx) ;;
  rx.

Definition do_pclrlog rx : dprog :=
  DWrite NLogDisk AEol 0 ;; rx.

Fixpoint dreadlog idx eol log rx: dprog :=
  match idx with
  | O => rx log
  | S n => 
    b <- DRead NLogDisk (ABlk (eol - idx));
    v <- DRead NLogDisk (AVal (eol - idx));
    dreadlog n eol (log ++ [(b, v)]) rx
  end.

Definition do_pgetlog rx : dprog :=
  eol <- DRead NLogDisk AEol;
  dreadlog eol eol nil rx.

Definition do_psettx v rx : dprog :=
  DWrite NLogDisk ATx (bool2nat v) ;; rx.

Definition do_pgettx rx : dprog :=
  v <- DRead NLogDisk ATx; rx (nat2bool v).

Close Scope fscq_scope.

Fixpoint compile_pd (p:pprog) : dprog :=
  match p with
  | PHalt         => DHalt
  | PRead b rx    => do_pread b (fun v => compile_pd (rx v))
  | PWrite b v rx => do_pwrite b v (compile_pd rx)
  | PAddLog b v rx  => do_paddlog b v (compile_pd rx)
  | PClrLog rx      => do_pclrlog (compile_pd rx)
  | PSetTx v rx     => do_psettx v (compile_pd rx)
  | PGetTx rx       => do_pgettx (fun v => compile_pd (rx v))
  | PGetLog rx      => do_pgetlog (fun v => compile_pd (rx v))
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

Inductive dstep : dstate -> dstate -> Prop :=
  | DsmRead: forall dd d l b rx,
       dstep (DSt (DRead dd b rx) d l)
               (match dd with 
                  | NDataDisk => (DSt (rx (st_read d b)) d l)
                  | NLogDisk =>  (DSt (rx (st_read l b)) d l)
               end)
  | DsmWrite: forall dd d l b v rx,
    dstep (DSt (DWrite dd b v rx) d l)
               (match dd with 
                  | NDataDisk => (DSt rx (st_write d b v) l)
                  | NLogDisk =>  (DSt rx d (st_write l b v))
               end)
  .


Inductive pdmatch : pstate -> dstate -> Prop :=
  | PDMatchState :
    forall pp pdisk lg tx pd dd lgd
    (DD: pdisk = dd)
    (TX: tx = match lgd ATx with
         | 1 => true
         | _ => false
         end)
    (* XXX match lg with lgd *)
    (PD: compile_pd pp = pd) ,
    pdmatch (PSt pp pdisk lg tx) (DSt pd dd lgd)
  .

Theorem pd_forward_sim:
  forall P1 P2, pstep P1 P2 ->
  forall D1, pdmatch P1 D1 ->
  exists D2, star dstep D1 D2 /\ pdmatch P2 D2.
Proof.
  Ltac t2 := simpl in *; subst; try autorewrite with core in *;
            intuition (eauto; try congruence).
  Ltac cc2 := t2; try constructor; t2.

  induction 1; intros; inversion H.

(*
  (* PHalt *)
  exists D1; t2; apply star_refl.
*)

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
Admitted.

  
(* XXX need to reformulate as pd_atomicity
Theorem dcorrect:
  forall p dd dd' ld ld' lg lg' d tx s,
  
  star dstep_fail (DSt (compile_pd p) dd ld lg) (DSt DHalt dd' ld' lg') ->
  pexec p (PSt p d nil tx) = s ->
  pdmatch s (DSt DHalt dd' ld' lg').
Proof.
  intros; eexists.
  inversion H.
Admitted.
*)
