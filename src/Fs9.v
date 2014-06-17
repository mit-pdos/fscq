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
  | TRSucc
  | TRFail.
  
Inductive tprog :=
  | TRead  (b:block) (rx:value -> tprog)
  | TWrite (b:block) ( v:value) (rx:trs -> tprog)
  | TBegin (rx:trs -> tprog)
  | TEnd   (rx:trs -> tprog)
  | THalt
  .

Record tstate := TSt {
  TSProg: tprog;
  TSDisk: storage;            (* main disk *)
  TSAltDisk: option storage   (* alternative disk for transactions *)
}.

(* high level interpreter *)
Fixpoint texec (p:tprog) (s:tstate) {struct p} : tstate :=
  let (_, d, ad) := s in
  match p with
  | THalt         => s
  | TRead b rx    =>
    match ad with
    | None   => texec (rx (st_read d b)) (TSt (rx (st_read d b)) d ad)
    | Some x => texec (rx (st_read x b)) (TSt (rx (st_read x b)) d ad)
    end
  | TWrite b v rx =>
    match ad with
    | None   => texec (rx TRSucc) (TSt (rx TRSucc) (st_write d b v) ad)
    | Some x => texec (rx TRSucc) (TSt (rx TRSucc) d (Some (st_write x b v)))
    end
  | TBegin rx     =>
    match ad with
    | None   => texec (rx TRSucc) (TSt (rx TRSucc) d (Some d))
    | Some _ => texec (rx TRFail) (TSt (rx TRFail) d ad)
    end
  | TEnd rx       =>
    match ad with
    | Some d => texec (rx TRSucc) (TSt (rx TRSucc) d None)
    | None   => texec (rx TRFail) (TSt (rx TRFail) d ad)
    end
  end.


Inductive tsmstep : tstate -> tstate -> Prop :=
  | TsmHalt: forall d ad,
    tsmstep (TSt THalt d ad) (TSt THalt d ad)
  | TsmRead: forall d b rx,
    tsmstep (TSt (TRead b rx) d None)
            (TSt (rx (st_read d b)) d None)
  | TsmReadTx: forall d ad b rx,
    tsmstep (TSt (TRead b rx) d (Some ad))
            (TSt (rx (st_read ad b)) d (Some ad))
  | TsmWrite: forall d b v rx,
    tsmstep (TSt (TWrite b v rx) d None)
            (TSt (rx TRSucc) (st_write d b v) None)
  | TsmWriteTx: forall d ad b v rx,
    tsmstep (TSt (TWrite b v rx) d (Some ad))
            (TSt (rx TRSucc) d (Some (st_write ad b v)))
  | TsmBegin: forall d rx,
    tsmstep (TSt (TBegin rx) d None) (TSt (rx TRSucc) d (Some d))
  | TsmBeginTx: forall d ad rx,
    tsmstep (TSt (TBegin rx) d (Some ad)) (TSt (rx TRFail) d (Some ad))
  | TsmEnd: forall d rx,
    tsmstep (TSt (TEnd rx) d None) (TSt (rx TRFail) d None)
  | TsmEndTx: forall d ad rx,
    tsmstep (TSt (TEnd rx) d (Some ad)) (TSt (rx TRSucc) ad None)
  .

Bind Scope tprog_scope with tprog.


Notation "a ;; b" := (a (fun trs => 
                           match trs with 
                             | TRSucc => (b)
                             | TRFail => THalt
                           end))
                       (right associativity, at level 60) : tprog_scope.

Notation "ra <- a ; b" := (a (fun ra => b))
                             (right associativity, at level 60) : tprog_scope.


Open Scope tprog_scope.

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
  let s := create_account src 100 (TSt THalt st_init None) in 
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
    v <- PRead b;
    match (pfind l b) with
    | Some v => cc (rx v)
    | None   => cc (rx v)
    end
  else
    v <- PRead b; cc (rx v)
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

Record pstate := PSt {
  PSProg: pprog;
  PSDisk: storage;
  PSLog: list (block * value);
  PSTx: bool
}.

Fixpoint pexec (p:pprog) (s:pstate) {struct p} : pstate :=
  let (_, d, l, c) := s in
  match p with
  | PHalt           => s
  | PRead b rx      => pexec (rx (st_read d b)) (PSt (rx (st_read d b)) d l c)
  | PWrite b v rx   => pexec rx (PSt rx (st_write d b v) l c)
  | PAddLog b v rx  => pexec rx (PSt rx d (l ++ [(b, v)]) c)
  | PClrLog rx      => pexec rx (PSt rx d nil c)
  | PGetLog rx      => pexec (rx l) (PSt (rx l) d l c)
  | PSetTx v rx     => pexec rx (PSt rx d l v)
  | PGetTx rx       => pexec (rx c) (PSt (rx c) d l c)
  end.

(*
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
*)


Inductive psmstep : pstate -> pstate -> Prop :=
  | PsmHalt: forall d l c,
    psmstep (PSt PHalt d l c) (PSt PHalt d l c)
  | PsmRead: forall d l c b rx,
    psmstep (PSt (PRead b rx) d l c)
            (PSt (rx (st_read d b)) d l c)
  | PsmWrite: forall d l c b v rx,
    psmstep (PSt (PWrite b v rx) d l c)
            (PSt rx (st_write d b v) l c)
  | PsmAddLog: forall d l c b v rx,
    psmstep (PSt (PAddLog b v rx) d l c)
            (PSt rx d (l ++ [(b, v)]) c)
  | PsmClrLog: forall d l c rx,
    psmstep (PSt (PClrLog rx) d l c)
            (PSt rx d nil c)
  | PsmGetLog: forall d l c rx,
    psmstep (PSt (PGetLog rx) d l c)
            (PSt (rx l) d l c)
  | PsmSetTx: forall d l c v rx,
    psmstep (PSt (PSetTx v rx) d l c)
            (PSt rx d l v)
  | PsmGetTx: forall d l c rx,
    psmstep (PSt (PGetTx rx) d l c)
            (PSt (rx c) d l c)
  .

Fixpoint log_flush (p:list (block*value)) (d:storage) : storage :=
  match p with
  | nil            => d
  | (b, v) :: rest => log_flush rest (st_write d b v)
  end.

Inductive tpmatch : tstate -> pstate -> Prop :=
  | TPMatchState :
    forall td tp pd lg (tx:bool) pp ad
    (DD: td = pd)
    (AD: ad = if tx then Some (log_flush lg td) else None)
    (TX: tx = match ad with
         | Some _ => true
         | None => false
         end)
    (PP: compile_tp tp = pp) ,
    tpmatch (TSt tp td ad) (PSt pp pd lg tx)
  .

Inductive psmstep_fail : pstate -> pstate -> Prop :=
  | PsmNormal: forall s s',
    psmstep s s' -> psmstep_fail s s'
  | PsmCrash: forall s,
    psmstep_fail s (pexec (do_trecover PHalt) s)
  .

Inductive tpmatch_fail : tstate -> pstate -> Prop :=
  | TPMatchNormal :
    forall t p, tpmatch t p -> tpmatch_fail t p
  | TPMatchFail :
    forall td tp pd lg (tx:bool) ad,
    tpmatch_fail (TSt tp td ad) (PSt PHalt pd lg tx)
  .



Section CLOSURES.

Variable state: Type.
Variable step: state -> state -> Prop.

Inductive star: state -> state -> Prop :=
  | star_refl: forall s,
      star s s
  | star_step: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> star s1 s3
  .

Lemma star_one:
  forall s1 s2, step s1 s2 -> star s1 s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl.
Qed.

Lemma star_two:
  forall s1 s2 s3,
  step s1 s2 -> step s2 s3 -> star s1 s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto. 
Qed.

Lemma star_three:
  forall s1 s2 s3 s4,
  step s1 s2 -> step s2 s3 -> step s3 s4 -> star s1 s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto.
Qed.

Lemma star_trans:
  forall s1 s2, star s1 s2 ->
  forall s3, star s2 s3 -> star s1 s3.
Proof.
  induction 1; intros.
  simpl. auto.
  eapply star_step; eauto.
Qed.

Lemma star_right:
  forall s1 s2 s3,
  star s1 s2 -> step s2 s3 -> star s1 s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto.
Qed.

Inductive plus : state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> plus s1 s3
  .

End CLOSURES.




Lemma writeLog_flush : forall l tx rx m m',
  m' = log_flush l m ->
  psmstep (PSt (pflush l rx) m l tx) (PSt rx m' l tx).
Proof.
  (* XXX:  Main unproven lemma *)
Admitted.

(** Pulling out the effect of the last log entry *)
Lemma writeLog_final : forall a v l m,
  log_flush (l ++ [(a, v)]) m = st_write (log_flush l m) a v.
Proof.
  induction l; intuition; simpl; auto.
Qed.


(** [readLog] interacts properly with [writeLog]. *)
Lemma readLog_correct : forall b ls d,
  st_read (log_flush ls d) b = match pfind ls b with
                            | Some v => v
                            | None => st_read d b
                          end.
Proof.

  Ltac t' := simpl in *;
    repeat (match goal with
            | [ H : ?x = _ |- _ ] => subst x
            | [ |- context[match ?E with pair _ _ => _ end] ] => destruct E
            | [ |- context[if eq_nat_dec ?X ?Y then _ else _] ] => destruct (eq_nat_dec X Y)
          end; simpl).

  Ltac t1 := simpl in *; intros; t';
    try autorewrite with core in *; intuition (eauto; try congruence); t'.

  induction ls; t1.

  destruct (pfind ls b0); eauto.
  rewrite IHls.
  unfold st_read, st_write; t1.

 destruct (pfind ls b); eauto.
  rewrite IHls.
  unfold st_read, st_write; t1.
Qed.


(*
   Forward small-step simulation:
   If no crash, each step in tprog maps to zero+ steps in pprog.

   Note that the 0-step case requires an additional premise showing that
   tprog actually makes progress, otherwise there would be the case that
   tprog does not terminate while pprog does, known as the stuttering problem.
   This is impossible because our continuation-style program has
   an ever-increasing program counter.
*)


Theorem tp_forward_sim:
  forall T1 T2, tsmstep T1 T2 ->
  forall P1, tpmatch T1 P1 ->
  exists P2, star psmstep P1 P2 /\ tpmatch T2 P2.
Proof.
  Ltac t := simpl in *; subst; try autorewrite with core in *;
            intuition (eauto; try congruence).
  Ltac cc := t; try constructor; t.

  induction 1; intros; inversion H; econstructor; split; try (t; inversion AD; t).

  destruct tx; cc. auto.

  eapply star_two; cc.
  unfold do_tread; cc.

  eapply star_right. eapply star_right. eapply star_right.
  constructor. constructor. constructor. constructor. cc.
  rewrite readLog_correct.
  destruct (pfind lg b) eqn:F; t.

  eapply star_two; cc. cc.

  eapply star_two; cc. cc.
  rewrite <- writeLog_final. auto.

  eapply star_three; cc. cc.

  eapply star_one; cc. cc.

  eapply star_one; cc. cc.

  do 4 (eapply star_step; [ cc | idtac ]).
  eapply writeLog_flush. eauto.
  eapply star_one; cc. cc.
Qed.


(** Main correctness theorem *)




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

Definition do_paddlog (cc:pprog -> dprog) b v rx : dprog :=
  idx <- DRead NLogDisk AEol;
  DWrite NLogDisk (AVal idx) v ;;
  DWrite NLogDisk (ABlk idx) b ;;
  DWrite NLogDisk AEol (S idx) ;;
  DAddLog b v ;;
  cc rx.

(* 0 indicates end of log XXX have a log disk type with a EoL marker *)
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

Inductive lg_lgd_match : (list (block * value)) -> storage -> Prop :=  
  | NIL: forall lgd,
           st_read lgd AEol = 0 ->
           lg_lgd_match nil lgd
  | NONNIL: forall lg lgd b v n,
              lg_lgd_match lg lgd -> 
              n = st_read lgd AEol ->
              b = st_read lgd (ABlk n) ->
              v = st_read lgd (AVal n) ->
              lg_lgd_match (lg ++ [(b, v)]) 
                           (st_write (st_write (st_write lgd (AVal n) v) (ABlk n) b) AEol (S n)).
   
                           
Inductive pdmatch : pstate -> dstate -> Prop :=
  | PDMatchState :
    forall pp pdisk lg tx pd dd lgd lgm
    (DD: pdisk = dd)
    (TX: tx = match lgd ATx with
         | 1 => true
         | _ => false
         end)
    (LGM: lg = lgm)   (* XXX only after drecovery *)
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

Fixpoint dexec (p:dprog) (s:dstate) : dstate := s.

(*
  let (dd, ld, lg) := s in
  match p with
  | DHalt           => s
  | DRead d b rx    =>
    match d with
    | NDataDisk => dexec (rx (st_read dd b)) s
    | NLogDisk  => dexec (rx (st_read ld b)) s
    end
  | DWrite d b v rx =>
    match d with
    | NDataDisk => dexec rx (DSt (st_write dd b v) ld lg)
    | NLogDisk => dexec rx (DSt dd (st_write ld b v) lg)
    end
  | DAddLog b v rx  => dexec rx (DSt dd ld (lg ++ [(b, v)]))
  | DClrLog rx      => dexec rx (DSt dd ld nil)
  | DGetLog rx      => dexec (rx lg) (DSt dd ld lg)
  end.
*)

Lemma correct_pd_recover_memory_log:
  forall p p' dd ld lg lg',
    dexec do_precover (DSt p dd ld lg) = (DSt p' dd ld lg') ->
    lg_lgd_match lg' ld.
Proof.
Admitted.
  



