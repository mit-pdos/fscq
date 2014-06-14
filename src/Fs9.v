Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition value := nat.
Definition addr := nat.
Definition block := nat.

(* Storage *)

Definition storage := block -> value.
Definition st_init : storage := fun _ => 0.
Definition st_read (s:storage) (b:block) : value := s b.
Definition st_write (s:storage) (b:block) (v:value) : storage :=
  fun b' => if eq_nat_dec b' b then v else s b'.

(** high-level language for a transactional disk *)

(* return values *)
Inductive trs :=
  | TRValue (v:value)
  | TRSucc
  | TRFail.
  
Inductive tprog :=
  | TRead  (b:block) (rx:trs -> tprog)
  | TWrite (b:block) ( v:value) (rx:trs -> tprog)
  | TBegin (rx:trs -> tprog)
  | TEnd   (rx:trs -> tprog)
  | THalt
  .

Record tstate := TSt {
  TSDisk: storage;            (* main disk *)
  TSAltDisk: option storage   (* alternative disk for transactions *)
}.

(* high level interpreter *)
Fixpoint texec (p:tprog) (s:tstate) : tstate :=
  let (d, ad) := s in
  match p with
  | THalt         => s
  | TRead b rx    =>
    match ad with
    | None   => texec (rx (TRValue (st_read d b))) (TSt d ad)
    | Some x => texec (rx (TRValue (st_read x b))) (TSt d ad)
    end
  | TWrite b v rx =>
    match ad with
    | None   => texec (rx TRSucc) (TSt (st_write d b v) ad)
    | Some x => texec (rx TRSucc) (TSt d (Some (st_write x b v)))
    end
  | TBegin rx     =>
    match ad with
    | None   => texec (rx TRSucc) (TSt d (Some d))
    | Some _ => texec (rx TRFail) (TSt d ad)
    end
  | TEnd rx       =>
    match ad with
    | Some d => texec (rx TRSucc) (TSt d None)
    | None   => texec (rx TRFail) (TSt d ad)
    end
  end.

Inductive tsmstep : tstate -> tprog -> tstate -> tprog -> Prop :=
  | TsmRead: forall d b rx,
    tsmstep (TSt d None) (TRead b rx)
            (TSt d None) (rx (TRValue (st_read d b)))
  | TsmReadTx: forall d ad b rx,
    tsmstep (TSt d (Some ad)) (TRead b rx)
            (TSt d (Some ad)) (rx (TRValue (st_read ad b)))
  | TsmWrite: forall d b v rx,
    tsmstep (TSt d None) (TWrite b v rx)
            (TSt (st_write d b v) None) (rx TRSucc)
  | TsmWriteTx: forall d ad b v rx,
    tsmstep (TSt d (Some ad)) (TWrite b v rx)
            (TSt d (Some (st_write ad b v))) (rx TRSucc)
  | TsmBegin: forall d rx,
    tsmstep (TSt d None) (TBegin rx) (TSt d (Some d)) (rx TRSucc)
  | TsmBeginTx: forall d ad rx,
    tsmstep (TSt d (Some ad)) (TBegin rx) (TSt d (Some ad)) (rx TRFail)
  | TsmEnd: forall d rx,
    tsmstep (TSt d None) (TEnd rx) (TSt d None) (rx TRFail)
  | TsmEndTx: forall d ad rx,
    tsmstep (TSt d (Some ad)) (TEnd rx) (TSt ad None) (rx TRSucc)
  .

Eval simpl in texec THalt (TSt st_init None).
Eval simpl in texec (TWrite 0 1 (fun trs => THalt)) (TSt st_init None).

Bind Scope tprog_scope with tprog.


Notation "a ;; b" := (a (fun trs => 
                           match trs with 
                             | TRValue v => THalt
                             | TRSucc => (b)
                             | TRFail => THalt
                           end))
                       (right associativity, at level 60) : tprog_scope.

Notation "v <- a ; b" := (a (fun ra => 
                           match ra with 
                             | TRValue v => (b)
                             | TRSucc => THalt
                             | TRFail => THalt
                           end))
                             (right associativity, at level 60) : tprog_scope.




Open Scope tprog_scope.

Eval simpl in texec THalt (TSt st_init None).
Eval simpl in texec (TBegin ;; THalt) (TSt st_init None).
Eval simpl in texec (v <- (TRead 0) ; (TWrite 0 v) ;; THalt) (TSt st_init None).
Eval simpl in texec (TWrite 0 1 ;; (v <- (TRead 0) ; (TWrite 1 v) ;; THalt)) (TSt st_init None).
Eval simpl in texec (TBegin ;; TWrite 0 1 ;; TWrite 1 1 ;; TEnd ;; THalt) (TSt st_init None).
Eval simpl in texec (TBegin ;; TWrite 0 1 ;; TWrite 1 1 ;; THalt) (TSt st_init None).

(* Follow adam's suggestion of "proving" this high-level language interpreter
correct by building a simple app for which we can state the properties
independent of the high-level language. *)

Definition do_transfer (src:nat) (dst:nat) (k: nat) (s: tstate) : tstate :=
 texec (TBegin ;; v <- (TRead src) ; TWrite src (v-k) ;; v1 <- (TRead dst) ; (TWrite dst (v1+k)) ;; TEnd ;; THalt) s.

Definition read_account (s: tstate) (n: nat) : value := (st_read s.(TSDisk) n).

Definition initial := 100.

Definition create_account (n : nat) (v : nat) (s: tstate): tstate :=
  texec (TBegin;; TWrite n initial ;; TEnd ;; THalt) s.

Definition transfer (src:nat) (dst:nat) (v:nat): value * value :=
  let s := create_account src 100 (TSt st_init None) in 
     let s1 := create_account dst 100 s in
     let s2 := do_transfer src dst v s1 in
         (read_account s2 src, read_account s2 dst).

Example legal_transfer1:
  forall k1 k2,
    transfer 0 1 10 = (k1, k2) -> k1 = initial - 10 /\ k2 = initial + 10.
Proof.
  intros; inversion H.
  crush.
Qed.

Close Scope tprog_scope.


(* language that manipulates a disk and an in-memory pending log *)

Inductive pprog :=
  | PRead   (b:block) (rx:value -> pprog)
  | PWrite  (b:block) ( v:value) (rx:pprog)
  | PAddLog (b:block) ( v:value) (rx:pprog)
  | PClrLog (rx:pprog)
  | PGetLog (rx:list (block * value) -> pprog)
  | PSetTx  (v:bool) (rx:pprog)
  | PGetTx  (rx:bool -> pprog)
  | PHalt
  .

Record pstate := PSt {
  PSDisk: storage;
  PSLog: list (block * value);
  PSTx: bool
}.

Bind Scope pprog_scope with pprog.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : pprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : pprog_scope.

Open Scope pprog_scope.

Fixpoint pfind (p:list (block * value)) (b:block) : option value :=
  match p with
  | nil => None
  | (b', v) :: rest =>
    match (pfind rest b) with
    | None => if eq_nat_dec b b' then Some v else None
    | x    => x
    end
  end.

Fixpoint pflush (p:list (block*value)) rx : pprog :=
  match p with
  | nil            => rx
  | (b, v) :: rest => PWrite b v ;; pflush rest rx
  end.

Definition do_tbegin (cc:tprog -> pprog) rx : pprog :=
   tx <- PGetTx;
   if tx then 
    cc (rx TRFail)
   else
    PClrLog ;; PSetTx true ;; cc (rx TRSucc)
.

Definition do_tread (cc:tprog -> pprog) b rx : pprog :=
  tx <- PGetTx;
  if tx then
    l <- PGetLog;
    match (pfind l b) with
    | Some v => cc (rx (TRValue v))
    | None   => v <- PRead b; cc (rx (TRValue v))
    end
  else
    v <- PRead b; cc (rx (TRValue v))
.

Definition do_twrite (cc:tprog -> pprog) b v rx : pprog :=
  tx <- PGetTx;
  if tx then
    PAddLog b v ;; cc (rx TRSucc)
  else
    PWrite b v;; cc (rx TRSucc)
.

Definition do_tend (cc:tprog -> pprog) rx : pprog :=
  tx <- PGetTx;
  if tx then 
    PSetTx false ;; l <- PGetLog ; pflush l ;; PClrLog ;; cc (rx TRSucc)
  else
    cc (rx TRFail)
.

Definition do_trecover rx : pprog :=
  tx <- PGetTx;
  if tx then
    PClrLog ;; PSetTx false ;; rx
  else
    l <- PGetLog ; pflush l ;; PClrLog ;; rx
.

Close Scope pprog_scope.

Fixpoint compile_tp (p:tprog) : pprog :=
  match p with
  | THalt         => PHalt
  | TBegin rx     => do_tbegin compile_tp rx
  | TRead b rx    => do_tread  compile_tp b rx
  | TWrite b v rx => do_twrite compile_tp b v rx
  | TEnd rx       => do_tend   compile_tp rx
  end.

Fixpoint pexec (p:pprog) (s:pstate) : pstate :=
  let (d, l, c) := s in
  match p with
  | PHalt           => s
  | PRead b rx      => pexec (rx (st_read d b)) (PSt d l c)
  | PWrite b v rx   => pexec rx (PSt (st_write d b v) l c)
  | PAddLog b v rx  => pexec rx (PSt d (l ++ [(b, v)]) c)
  | PClrLog rx      => pexec rx (PSt d nil c)
  | PGetLog rx      => pexec (rx l) (PSt d l c)
  | PSetTx v rx     => pexec rx (PSt d l v)
  | PGetTx rx       => pexec (rx c) (PSt d l c)
  end.

Inductive pstep : pstate -> pprog -> pstate -> Prop :=
  | PsHalt: forall s,
    pstep s PHalt s
  | PsRead: forall d l c b rx s,
    pstep (PSt d l c) (rx (st_read d b)) s ->
    pstep (PSt d l c) (PRead b rx) s
  | PsWrite: forall d l c b v rx s,
    pstep (PSt (st_write d b v) l c) rx s ->
    pstep (PSt d l c) (PWrite b v rx) s
  | PsAddLog: forall d l c b v rx s,
    pstep (PSt d (l ++ [(b, v)]) c) rx s ->
    pstep (PSt d l c) (PAddLog b v rx) s
  | PsClrLog: forall d l c rx s,
    pstep (PSt d nil c) rx s ->
    pstep (PSt d l c) (PClrLog rx) s
  | PsGetLog: forall d l c rx s,
    pstep (PSt d l c) (rx l) s ->
    pstep (PSt d l c) (PGetLog rx) s
  | PsSetTx: forall d l c v rx s,
    pstep (PSt d l v) rx s ->
    pstep (PSt d l c) (PSetTx v rx) s
  | PsGetTx: forall d l c rx s,
    pstep (PSt d l c) (rx c) s ->
    pstep (PSt d l c) (PGetTx rx) s
  | PsCrash: forall s p,  (* assuming the recovery process does not fail *)
    pstep s p (pexec (do_trecover PHalt) s)
  .
(*| PsCrash: forall s p s',  (* we can run recovery at anytime and continue *)
    pstep s (do_trecover p) s' ->
    pstep s p s'. *)

Inductive tpmatch : tstate -> tprog -> pstate -> pprog -> Prop :=
  | tpmatch_state :
    forall td tad tp pd lg (tx:bool) pp ad
    (DD: td = pd)
    (TX: tad = if tx then Some ad else None)
    (PP: compile_tp tp = pp /\ pp = PHalt) ,
    tpmatch (TSt td ad) tp (PSt pd lg tx) pp.

Inductive psmstep : pstate -> pprog -> pstate -> pprog -> Prop :=
  | PsmRead: forall d l c b rx,
    psmstep (PSt d l c) (PRead b rx) (PSt d l c) (rx (st_read d b))
  | PsmWrite: forall d l c b v rx,
    psmstep (PSt d l c) (PWrite b v rx) (PSt (st_write d b v) l c) rx
  | PsmAddLog: forall d l c b v rx,
    psmstep (PSt d l c) (PAddLog b v rx) (PSt d (l ++ [(b, v)]) c) rx
  | PsmClrLog: forall d l c rx,
    psmstep (PSt d l c) (PClrLog rx) (PSt d nil c) rx
  | PsmGetLog: forall d l c rx,
    psmstep (PSt d l c) (PGetLog rx) (PSt d l c) (rx l)
  | PsmSetTx: forall d l c v rx,
    psmstep (PSt d l c) (PSetTx v rx) (PSt d l v) rx
  | PsmGetTx: forall d l c rx,
    psmstep (PSt d l c) (PGetTx rx) (PSt d l c) (rx c)
  | PsmCrash: forall s p,
    psmstep s p (pexec (do_trecover PHalt) s) PHalt
  .

(*
   Backward small-step simulation:
   Each step in pprog maps to zero or a single step in tprog.

   Note that the 0-step case requires an additional premise showing that
   pprog actually makes progress, otherwise there would be the case that
   pprog does not terminate while tprog does, known as the stuttering problem.
   This is impossible because our continuation-style program has
   an ever-increasing program counter.
*)

Theorem tp_backsim:
  forall ts tp ps pp ps' pp',
  tpmatch ts tp ps pp ->
  psmstep ps pp ps' pp' ->
  (* 0-step *) tpmatch ts tp ps' pp' \/
  (* 1-step *) exists ts' tp', tsmstep ts tp ts' tp' /\ tpmatch ts' tp' ps' pp'.
Proof.
  
Qed.


(** Main correctness theorem *)

(* language that implements the log as a disk *)

Definition DSDataDisk := 0.
Definition DSBlockDisk := 1.
Definition DSValueDisk := 2.
Definition DSTxDisk := 3.

Inductive dprog :=
  | DRead   (d:nat) (b:block) (rx:value -> dprog)
  | DWrite  (d:nat) (b:block) ( v:value) (rx:dprog)
  | DGetEndOfLog (rx:nat -> dprog)
  | DHalt.
  

(* A logging disk has an index disk (which stores the block number b to be
written) and a value disk that stores the value to be written to block b.  It
also stores the end of the log, index, which will be recovered on reboot. *)
Record LogDisk : Set := mkLogDisk {
  Index : nat;
  LogIndexDisk : storage;  (* XXX block *)
  LogValueDisk : storage 
}.

Definition LogDisk_init := mkLogDisk 0 st_init st_init.

Record dstate := DSt {
  DSDisk: storage;
  DSLog: LogDisk;
  DSEoL: nat;
  DSTx: storage  (* bool disk *)
}.

Definition log_init := DSt st_init LogDisk_init 0 st_init.

Bind Scope dprog_scope with dprog.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : dprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : dprog_scope.

Open Scope dprog_scope.

Definition do_pread (cc:pprog -> dprog) b rx : dprog :=
  v <- DRead DSDataDisk b; cc (rx v).

Definition do_pwrite (cc:pprog -> dprog) b v rx : dprog :=
  DWrite DSDataDisk b v ;; cc rx.

Definition do_paddlog (cc:pprog -> dprog) b v rx : dprog :=
  index <- DGetEndOfLog;
  DWrite DSValueDisk index v ;; DWrite DSBlockDisk index b ;; cc rx.

(* 0 indicates end of log XXX have a log disk type with a EoL marker *)
Definition do_pclrlog (cc:pprog -> dprog) rx : dprog :=
  DWrite DSBlockDisk 0 0 ;; cc rx.

(* Read log from block and value disk *)
Fixpoint do_readlog (index:nat) (log: list (block*value)) (cc:pprog -> dprog) rx : dprog :=
  match index with
  | O => cc (rx log)
  | S n => 
    b <- DRead DSBlockDisk index;
    if eq_nat_dec b 0 then cc (rx log)
    else v <- DRead DSValueDisk index ; do_readlog n ((b, v) :: log) cc rx
  end.

Definition do_pgetlog (cc:pprog -> dprog) rx : dprog :=
  index <- DGetEndOfLog;
  do_readlog index nil cc rx.

Definition do_psettx (cc:pprog -> dprog) v rx : dprog :=
  DWrite DSTxDisk 0 v ;; cc rx.

Definition do_pgettx (cc:pprog -> dprog) rx : dprog :=
  v <- DRead DSTxDisk 0; cc (rx v).

Close Scope dprog_scope.

Fixpoint compile_pp (p:pprog) : dprog :=
  match p with
  | PHalt         => DHalt
  | PRead b rx    => do_pread compile_pp b rx
  | PWrite b v rx => do_pwrite compile_pp b v rx
  | PAddLog b v rx  => do_paddlog compile_pp b v rx
  | PClrLog rx      => do_pclrlog compile_pp rx
  | PGetLog rx      => do_pgetlog compile_pp rx
  | PSetTx v rx     => do_psettx compile_pp v rx
  | PGetTx rx       => do_pgettx compile_pp rx
  end.

Fixpoint dexec (p:dprog) (s:dstate) : pstate :=
  let (d, l, c) := s in
  match p with
  | PHalt           => s
  | PRead b rx      => pexec (rx (st_read d b)) (PSt d l c)
  | PWrite b v rx   => pexec rx (PSt (st_write d b v) l c)
  | PGetEndLog rx   => pexec (rx eol) (PSt d l c)
  end.

