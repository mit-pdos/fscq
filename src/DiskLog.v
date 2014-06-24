Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Require Import MemLog.
Load Closures.


(* language that implements the log as a disk *)

Inductive ddisk :=
  | NDataDisk
  | NLogDisk
  .

Inductive dprog :=
  | DRead   (d:ddisk) (b:block) (rx:value -> dprog)
  | DWrite  (d:ddisk) (b:block) ( v:value) (rx:dprog)
  | DAddLog (b:block) (v:value) (rx:dprog)
  | DClrLog (rx:dprog)
  | DGetLog (rx:list (block * value) -> dprog)
  | DHalt
  .


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

Definition do_pread (cc:pprog -> dprog) b rx : dprog :=
  v <- DRead NDataDisk b; cc (rx v).

Definition do_pwrite (cc:pprog -> dprog) b v rx : dprog :=
  DWrite NDataDisk b v ;; cc rx.

(* XXX paddlog is atomic. *)
Definition do_paddlog (cc:pprog -> dprog) b v rx : dprog :=
  idx <- DRead NLogDisk AEol;
  DWrite NLogDisk (AVal idx) v ;;
  DWrite NLogDisk (ABlk idx) b ;;
  DAddLog b v ;;
  DWrite NLogDisk AEol (S idx) ;;
  cc rx.

Definition do_pclrlog (cc:pprog -> dprog) rx : dprog :=
  DWrite NLogDisk AEol 0 ;; DClrLog ;; cc rx.

Definition do_pgetlog (cc:pprog -> dprog) (rx: list(block*value) -> pprog) : dprog :=
  l <- DGetLog ; cc (rx l).

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

Definition do_psettx (cc:pprog -> dprog) v rx : dprog :=
  DWrite NLogDisk ATx (bool2nat v) ;; cc rx.

Definition do_pgettx (cc:pprog -> dprog) rx : dprog :=
  v <- DRead NLogDisk ATx; cc (rx (nat2bool v)).

Fixpoint dreadlog idx eol: dprog :=
  match idx with
  | O => DHalt
  | S n => 
    b <- DRead NLogDisk (ABlk (eol - idx));
    v <- DRead NLogDisk (AVal (eol - idx));
    DAddLog b v ;;
    dreadlog n eol
  end.

Definition do_precover : dprog :=
  eol <- DRead NLogDisk AEol;
  DClrLog ;; dreadlog eol eol.

Close Scope dprog_scope.

Fixpoint compile_pd (p:pprog) : dprog :=
  match p with
  | PHalt         => DHalt
  | PRead b rx    => do_pread compile_pd b rx
  | PWrite b v rx => do_pwrite compile_pd b v rx
  | PAddLog b v rx  => do_paddlog compile_pd b v rx
  | PClrLog rx      => do_pclrlog compile_pd rx
  | PSetTx v rx     => do_psettx compile_pd v rx
  | PGetTx rx       => do_pgettx compile_pd rx
  | PGetLog rx      => do_pgetlog compile_pd rx
  end.

Record dstate := DSt {
  DSProg: dprog;
  DSDataDisk: storage;
  DSLogDisk: storage;
  DSLog: list (block * value)
}.

Definition log_init := DSt DHalt st_init st_init nil.

Inductive dsmstep : dstate -> dstate -> Prop :=
  | DsmHalt: forall d l ml,
    dsmstep (DSt DHalt d l ml) (DSt DHalt d l ml)
  | DsmRead: forall dd d l ml b rx,
       dsmstep (DSt (DRead dd b rx) d l ml)
               (match dd with 
                  | NDataDisk => (DSt (rx (st_read d b)) d l ml)
                  | NLogDisk =>  (DSt (rx (st_read l b)) d l ml)
               end)
  | DsmWrite: forall dd d l ml b v rx,
    dsmstep (DSt (DWrite dd b v rx) d l ml)
               (match dd with 
                  | NDataDisk => (DSt rx (st_write d b v) l ml)
                  | NLogDisk =>  (DSt rx d (st_write l b v) ml)
               end)
  | DsmAddLog: forall d l lm b v rx,
    dsmstep (DSt (DAddLog b v rx) d l lm)
            (DSt rx d l (lm ++ [(b, v)]))
  | DsmClrLog: forall d l lm rx,
    dsmstep (DSt (DClrLog rx) d l lm)
            (DSt rx d l nil)
  | DsmGetLog: forall d l lm rx,
    dsmstep (DSt (DGetLog rx) d l lm)
            (DSt (rx lm) d l lm)
  .


Inductive pdmatch : pstate -> dstate -> Prop :=
  | PDMatchState :
    forall pp pdisk lg tx pd dd lgd lgm
    (DD: pdisk = dd)
    (TX: tx = match lgd ATx with
         | 1 => true
         | _ => false
         end)
    (LGM: lg = lgm) 
    (PD: compile_pd pp = pd) ,
    pdmatch (PSt pp pdisk lg tx) (DSt pd dd lgd lgm)
  .

Theorem pd_forward_sim:
  forall P1 P2, psmstep P1 P2 ->
  forall D1, pdmatch P1 D1 ->
  exists D2, star dsmstep D1 D2 /\ pdmatch P2 D2.
Proof.
  Ltac t2 := simpl in *; subst; try autorewrite with core in *;
            intuition (eauto; try congruence).
  Ltac cc2 := t2; try constructor; t2.

  induction 1; intros; inversion H.

  (* PHalt *)
  exists D1; t2; apply star_refl.

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

  (* PAddLog *)
  eexists; split.
  do 5 (eapply star_step; [ cc2 | idtac ]).
  cc2.
  t2.
  
  cc2.
  admit.  (* for different addresses the state isn't effected; ATx is different address ...*)
  
  (* PClrLog *)
  eexists; split.
  eapply star_two.
  cc2.
  cc2.
  cc2.

  admit.
  admit.
  admit.

Qed.

(* An interpreter for the language that implements a log as a disk *)

Fixpoint dexec (p:dprog) (s:dstate) {struct p} : dstate :=
  let (_, dd, ld, lg) := s in
  match p with
  | DHalt           => s
  | DRead d b rx    =>
    match d with
    | NDataDisk => dexec (rx (st_read dd b)) (DSt (rx (st_read dd b)) dd ld lg)
    | NLogDisk  => dexec (rx (st_read ld b)) (DSt (rx (st_read ld b)) dd ld lg)
    end
  | DWrite d b v rx =>
    match d with
    | NDataDisk => dexec rx (DSt rx (st_write dd b v) ld lg)
    | NLogDisk => dexec rx (DSt rx dd (st_write ld b v) lg)
    end
  | DAddLog b v rx  => dexec rx (DSt rx dd ld (lg ++ [(b, v)]))
  | DClrLog rx      => dexec rx (DSt rx dd ld nil)
  | DGetLog rx      => dexec (rx lg) (DSt (rx lg) dd ld lg)
  end.

(* recovery of in-memory log from log disk *)

Inductive dsmstep_fail : dstate -> dstate -> Prop :=
  | DsmNormal: forall s s',
    dsmstep s s' -> dsmstep_fail s s'
  | DsmCrash: forall s,
    dsmstep_fail s (dexec do_precover s)
  .

(* XXX must show that if dsmstep is true, then also lgmem_lgdisk_match is true *)
Inductive lgmem_lgdisk_match : storage -> (list (block * value)) -> Prop :=  
  | NIL: forall lgd,
           st_read lgd AEol = 0 ->
           lgmem_lgdisk_match lgd nil
  | NONNIL: forall lgm lgd b v n,
              lgmem_lgdisk_match lgd lgm -> 
              n = st_read lgd AEol ->
              b = st_read lgd (ABlk n) ->
              v = st_read lgd (AVal n) ->
              lgmem_lgdisk_match (st_write (st_write (st_write lgd (AVal n) v) (ABlk n) b) AEol (S n)) (lgm ++ [(b, v)]). 
   
Lemma correct_pd_recover_memory_log:
  forall p p' dd lgd lgm lgm',
    lgmem_lgdisk_match lgd lgm ->
    dexec do_precover (DSt p dd lgd nil) = (DSt p' dd lgd lgm') ->
    lgm = lgm'.
Proof.
  intros.
  induction lgm.

  (* lgm = nil *)
  inversion H.
  unfold dexec.

  admit. (* must be true because H1 holds *)

  (* general case *) 

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
