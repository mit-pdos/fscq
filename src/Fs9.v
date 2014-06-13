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
  | TRFail
  .

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

Definition read (s: tstate) (b:block) : value := (st_read s.(TSDisk) b).

Definition create_account (n : nat) (v : nat) (s: tstate): tstate :=
  texec (TBegin;; TWrite n 100 ;; TEnd ;; THalt) s.

Definition transfer (src:nat) (dst:nat) (v:nat): value * value :=
  let s := create_account src 100 (TSt st_init None) in 
     let s1 := create_account dst 100 s in
     let s2 := do_transfer src dst v s1 in
         (read s2 src, read s2 dst).

Example legal_transfer1:
  forall k1 k2,
    transfer 0 1 10 = (k1, k2) -> k1 = 90 /\ k2 = 110.
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



Ltac t' := simpl in *;
  repeat (match goal with
            | [ H : ?x = _ |- _ ] => subst x
            | [ |- context[match ?E with pair _ _ => _ end] ] => destruct E
            | [ |- context[if eq_nat_dec ?X ?Y then _ else _] ] => destruct (eq_nat_dec X Y)
          end; simpl).
Ltac t := simpl in *; intros;
  t'; try autorewrite with core in *; intuition (eauto; try congruence); t'.

Ltac step := repeat 
  (match goal with
   | [ H : pstep _ _ _ |- _ ] => inversion H; [|]; clear H; intros
   end); t.

(** A quick useful list lemma *)
Theorem app_comm_cons : forall A (ls1 : list A) x ls2,
  ls1 ++ x :: ls2 = (ls1 ++ x :: nil) ++ ls2.
Proof.
  induction ls1; t; rewrite IHls1; t.
Qed.

(** There's no point in two consecutive writes to the same address. *)
Lemma upd_upd_eq : forall m a v v',
  st_write (st_write m a v) a v' = st_write m a v'.
Proof.
  unfold st_write; intros; extensionality a'; t.
Qed.

Hint Rewrite upd_upd_eq.

(** Writes to unequal addresses commute. *)
Lemma upd_upd_neq : forall m a a' v v',
  a <> a'                      
  -> st_write (st_write m a v) a' v' = st_write (st_write m a' v') a v.
Proof.
  unfold st_write; intros; extensionality a''; t.
Qed.

Hint Rewrite upd_upd_eq.


Fixpoint log_flush (p:list (block*value)) (d:storage) : storage :=
  match p with
  | nil            => d
  | (b, v) :: rest => log_flush rest (st_write d b v)
  end.

(** When we're writing from the log, initial memory values don't matter in
  * positions that will be overwritten later. *)
Lemma writeLog_overwrite : forall a l m m' v,
  (forall a', a' <> a -> m a' = m' a')
  -> st_write (log_flush l m) a v = st_write (log_flush l m') a v.
Proof.
  induction l; t.
  unfold st_write; extensionality a'; t.
  apply IHl; t.
  unfold st_write; t.
Qed.

(** The starting value of a memory cell is irrelevant if we are writing from
  * a log that ends in a mapping for that cell. *)
Lemma writeLog_last : forall a v l m v',
  log_flush (l ++ (a, v) :: nil) (st_write m a v') = st_write (log_flush l m) a v.
Proof.
  induction l; t.
  destruct (eq_nat_dec a b); subst.
  rewrite IHl.
  apply writeLog_overwrite; unfold st_write; t.
  rewrite upd_upd_neq by assumption; eauto.
Qed.

Hint Rewrite writeLog_last.

(** Decomposing a writing process *)
Lemma writeLog_app : forall l2 l1 m m',
  log_flush l1 m = m'
  -> log_flush (l1 ++ l2) m = log_flush l2 m'.
Proof.
  induction l1; t.
Qed.

(** [flush] implements [writeLog] in the failure-free semantics. *)
Lemma flush_nofail : forall l m l' c,
  pexec (pflush l (PClrLog PHalt)) (PSt m l' c) = PSt (log_flush l m) nil c.
Proof.
  induction l; t.
Qed.

Hint Rewrite flush_nofail app_nil_r.

(** [flush] implements [writeLog] in the failure-allowed semantics. *)
Lemma flush_writeLog' : forall l m l' m' l1 c1,
  pstep (PSt m (l' ++ l) false) (pflush l PHalt) (PSt m' l1 c1)
  -> log_flush l' m = m
  -> m' = log_flush l m.
Proof.
  induction l; t; step.
  rewrite app_comm_cons in *. eapply IHl. eauto. t.
  inversion H4.
  erewrite writeLog_app by eassumption. t.
Qed.

Lemma flush_writeLog : forall l m m' l1 c1,
  pstep (PSt m l false) (pflush l PHalt) (PSt m' l1 c1)
  -> m' = log_flush l m.
Proof.
  intros; eapply flush_writeLog' with (l':=nil) (l1:=l1) (c1:=c1); t.
Qed.

Hint Resolve flush_writeLog.

(** [readLog] interacts properly with [writeLog]. *)
Lemma readLog_correct : forall b ls d,
  st_read (log_flush ls d) b = match pfind ls b with
                            | Some v => v
                            | None => st_read d b
                          end.
Proof.
  induction ls; t.

  destruct (pfind ls b0); eauto.
  rewrite IHls.
  unfold st_read, st_write; t.

  destruct (pfind ls b); eauto.
  rewrite IHls.
  unfold st_read, st_write; t.
Qed.

(** Pulling out the effect of the last log entry *)
Lemma writeLast_final : forall a v l m,
  log_flush (l ++ (a, v) :: nil) m = st_write (log_flush l m) a v.
Proof.
  induction l; t.
Qed.

Hint Rewrite writeLast_final.

Theorem correct_tx' : forall d p l d' l' c',
  pstep (PSt d l true) (compile_tp p) (PSt d' l' c')
  -> d' = d \/ exists ad, (TSt d' ad) = texec p (TSt d (Some (log_flush l d))).
Proof.
  induction p; t; step.

  (* read *)
  generalize (readLog_correct b l d).
  destruct (pfind l b); t.
  subst; eauto.
  rewrite H0; inversion H11; t.
  (* write *) eapply H in H13. t.
  (* end *)
  admit.
  admit.
Admitted.

Theorem correct_tx : forall d p d' l' c',
  pstep (PSt d nil true) (compile_tp p) (PSt d' l' c')
  -> d' = d \/ exists ad, (TSt d' ad) = texec p (TSt d (Some d)).
Proof.
  intros. apply correct_tx' in H . auto.
Qed.


Theorem correct_notx : forall d p d' l' c',
  pstep (PSt d nil false) (compile_tp p) (PSt d' l' c')
  -> d' = d \/ exists ad, (TSt d' ad) = texec p (TSt d None).
Proof.
  induction p; t; step.
  (* XXX:
     need to show that run a high-level program on a changed storage
     will produce the same result as running the low-level program
     on that storage ... *)
  admit.
  
  eapply correct_tx. eassumption.
Qed.


(** Main correctness theorem *)
