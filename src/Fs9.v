Require Import List.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Definition value := nat.
Definition block := nat.

(* Storage *)

Parameter storage : Set.
Parameter st_init  : storage.
Parameter st_write : storage -> block -> value -> storage.
Parameter st_read  : storage -> block -> value.

Axiom st_read_same:
  forall s a v,
  st_read (st_write s a v) a = v.

Axiom st_read_other:
  forall s a a' v,
  st_read (st_write s a' v) a = st_read s a.

Axiom st_read_init:
  forall a v, st_read st_init a = v -> v = 0.

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
  end
.

Eval simpl in texec THalt (TSt st_init None).
Eval simpl in texec (TWrite 0 1 (fun trs => THalt)) (TSt st_init None).

Bind Scope tprog_scope with tprog.


Notation "a ;; b" := (a (fun trs => 
                           match trs with 
                             | TRValue v => THalt
                             | TRSucc => b
                             | TRFail => THalt
                           end))
                       (right associativity, at level 60) : tprog_scope.

Notation "v <- a ; b" := (a (fun ra => 
                           match ra with 
                             | TRValue v => b
                             | TRSucc => THalt
                             | TRFail => THalt
                           end))
                             (right associativity, at level 60) : tprog_scope.


Open Scope tprog_scope.

Hint Rewrite st_read_init.
Hint Rewrite st_read_same.
Hint Rewrite st_read_other.

Eval simpl in texec THalt (TSt st_init None).
Eval simpl in texec (TBegin ;; THalt) (TSt st_init None).
Eval simpl in texec (v <- (TRead 0) ; (TWrite 0 v) ;; THalt) (TSt st_init None).
Eval simpl in texec (TWrite 0 1 ;; (v <- (TRead 0) ; (TWrite 1 v) ;; THalt)) (TSt st_init None).
Eval simpl in texec (TBegin ;; TWrite 0 1 ;; TWrite 1 1 ;; TEnd ;; THalt) (TSt st_init None).
Eval simpl in texec (TBegin ;; TWrite 0 1 ;; TWrite 1 1 ;; THalt) (TSt st_init None).

Fixpoint find_last_committed_write (p:tprog) (s:tstate) (bw:block) (vu:nat) (vc:nat) :=
  let (d, ad) := s in
  match p with
  | THalt => vc
  | TRead b rx => find_last_committed_write (rx (TRValue (st_read d b))) (TSt d ad) bw vu vc
  | TWrite b v rx =>
    match ad with
      | None   => find_last_committed_write (rx TRSucc) (TSt (st_write d b v) ad) bw v v
      | Some x => find_last_committed_write (rx TRSucc) (TSt d (Some (st_write x b v))) bw (if eq_nat_dec bw b then v else vu) vc 
    end
  | TBegin rx => 
    match ad with
    | None   => find_last_committed_write (rx TRSucc) (TSt d (Some d)) bw vu vc
    | Some _ => find_last_committed_write (rx TRFail) (TSt d ad) bw vu vc
    end
  | TEnd rx =>
    match ad with
    | Some d => find_last_committed_write (rx TRSucc) (TSt d None) bw vc vc
    | None   => find_last_committed_write (rx TRFail) (TSt d ad) bw vu vc
    end
  end.

Theorem trans_committed_last_write:
  forall s prog b,
    texec prog (TSt st_init None) = s ->
    find_last_committed_write prog s b 0 0 = st_read s.(TSDisk) b.
Proof.
  intro.
  induction prog.
  intuition.
  (* read *)
  - intros.
    admit.
  (* write *)
  - intros.
    admit.
  (* begin *)
  - intros.
    admit.
  (* end *)
  - intros.
    admit.
  (* halt *)
  - intros.
Admitted.

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
    PSetTx true ;; PClrLog ;; cc (rx TRSucc)
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
    PClrLog ;; rx
  else
    l <- PGetLog; pflush l ;; rx
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
  | PsCrash: forall p d l c l' c',
    (* XXX need some theorem about recovery *)
    pstep (PSt d l c) p (PSt (PSDisk (pexec (do_trecover p) (PSt d l c))) l' c')
    (* XXX: how to continue running after recovery ? *).

Fixpoint log_flush (p:list (block*value)) (d:storage) : storage :=
  match p with
  | nil            => d
  | (b, v) :: rest => log_flush rest (st_write d b v)
  end.

Theorem correct' : forall d p l d' l' c',
  pstep (PSt d l false) (compile_tp p) (PSt d' l' c')
  -> d' = d \/ d' = TSDisk (texec p (TSt (log_flush l d) None)).
Proof.
  induction p; intros; auto.
Admitted.

(** Main correctness theorem *)
Theorem correct : forall d p d' l' c',
  pstep (PSt d nil false) (compile_tp p) (PSt d' l' c')
  -> d' = d \/ d' = TSDisk (texec p (TSt d None)).
Proof.
  intros. apply correct' in H. auto.
Qed.