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


(** small step helpers *)

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

Hypothesis step_determ : (forall s t t', step s t -> step s t' -> t = t').

Lemma star_inv:
  forall s1 s2 s3,
  star s1 s3 -> step s1 s2 -> s1 <> s3 -> star s2 s3.
Proof.
  intros; inversion H. contradiction.
  subst; assert (s2=s4). eapply step_determ; eauto. subst; auto.
Qed.

Lemma star_stuttering:
  forall s1 s2,
  star s1 s2 -> step s1 s1 -> s1 = s2.
Proof.
  intros s1 s2.
  induction 1; intros; auto.
  assert (s1=s2); [ eapply step_determ; eauto | subst ].
  apply IHstar; auto.
Qed.

Inductive plus : state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> plus s1 s3
  .

End CLOSURES.



(** File-specific automation tactic *)
Ltac t' := simpl in *;
  repeat (match goal with
            | [ H : ?x = _ |- _ ] => subst x
            | [ |- context[match ?E with pair _ _ => _ end] ] => destruct E
            | [ |- context[if eq_nat_dec ?X ?Y then _ else _] ] => destruct (eq_nat_dec X Y)
          end; simpl).
Ltac t := simpl in *; intros;
  t'; try autorewrite with core in *; intuition (eauto; try congruence); t'.


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


(** If no failure, tsmstep and texec are equivalent *)
Lemma texec_smstep :
  forall p d ad s',
  texec p (TSt p d ad) = s' -> star tsmstep (TSt p d ad) s'.
Proof.
Admitted.

Lemma tsmstep_determ:
  forall s0 s s',
  tsmstep s0 s -> tsmstep s0 s' -> s = s'.
Proof.
  intro s0; case_eq s0; intros.
  repeat match goal with
  | [ H: tsmstep _ _ |- _ ] => inversion H; clear H
  end; t.
Qed.

Lemma smstep_texec :
  forall p d ad d' ad',
  star tsmstep (TSt p d ad) (TSt THalt d' ad') ->
  texec p (TSt p d ad) = (TSt THalt d' ad').
Proof.
  induction p;  intros;  destruct ad;
  match goal with
  | [ |- texec THalt _ = _ ] =>
    simpl; eapply star_stuttering; [ apply tsmstep_determ | eauto | constructor ]
  | [ H: context [star tsmstep _ _ -> texec _ _ = _ ] |- _] =>
    apply H; eapply star_inv; [ apply tsmstep_determ | t | constructor | t ]
  | _ => idtac
  end.
Qed.


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

Fixpoint pexec (p:pprog) (s:pstate) {struct p} : pstate :=
  let (_, d, l, c) := s in
  match p with
  | PHalt           => (PSt p d l c)
  | PRead b rx      => pexec (rx (st_read d b)) (PSt (rx (st_read d b)) d l c)
  | PWrite b v rx   => pexec rx (PSt rx (st_write d b v) l c)
  | PAddLog b v rx  => pexec rx (PSt rx d (l ++ [(b, v)]) c)
  | PClrLog rx      => pexec rx (PSt rx d nil c)
  | PGetLog rx      => pexec (rx l) (PSt (rx l) d l c)
  | PSetTx v rx     => pexec rx (PSt rx d l v)
  | PGetTx rx       => pexec (rx c) (PSt (rx c) d l c)
  end.

(** If no failure, psmstep and pexec are equivalent *)
Lemma pexec_smstep :
  forall p d l tx s',
  pexec p (PSt p d l tx) = s' -> star psmstep (PSt p d l tx) s'.
Proof.
  induction p; intros;
  eapply star_step; t; try constructor.
  eapply star_one; rewrite <- H; constructor.
Qed.

Lemma psmstep_determ:
  forall s0 s s',
  psmstep s0 s -> psmstep s0 s' -> s = s'.
Proof.
  intro s0; case_eq s0; intros.
  induction PSProg0; intros;
  repeat match goal with
  | [ H: psmstep _ _ |- _ ] => inversion H; clear H
  end; subst; reflexivity.
Qed.

Lemma smstep_pexec :
  forall p d l tx d' l' tx',
  star psmstep (PSt p d l tx) (PSt PHalt d' l' tx') ->
  pexec p (PSt p d l tx) = (PSt PHalt d' l' tx').
Proof.
  induction p;  intros;
  match goal with
  | [ |- pexec PHalt _ = _ ] =>
    simpl; eapply star_stuttering; [ apply psmstep_determ | eauto | constructor ]
  | [ H: context [star psmstep _ _ -> pexec _ _ = _ ] |- _] =>
    apply H; eapply star_inv; [ apply psmstep_determ | t | constructor | t ]
  end.
Qed.

(* failure semantics *)

Inductive psmstep_fail : pstate -> pstate -> Prop :=
  | PsmNormal: forall s s',
    psmstep s s' -> psmstep_fail s s'
  | PsmCrash: forall s,
    psmstep_fail s (pexec (do_trecover PHalt) s)
  .

(* state matching *)

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

Inductive tpmatch_fail : tstate -> pstate -> Prop :=
  | TPMatchNormal :
    forall t p, tpmatch t p -> tpmatch_fail t p
  | TPMatchFail :
    forall td tp pd lg (tx:bool) ad,
    tpmatch_fail (TSt tp td ad) (PSt PHalt pd lg tx)
  .


(** A quick useful list lemma *)
Theorem app_comm_cons : forall A (ls1 : list A) x ls2,
  ls1 ++ x :: ls2 = (ls1 ++ x :: nil) ++ ls2.
Proof.
  induction ls1; t; rewrite IHls1; t.
Qed.

(** There's no point in two consecutive writes to the same address. *)
Lemma st_write_eq : forall d b v v',
  st_write (st_write d b v) b v' = st_write d b v'.
Proof.
  unfold st_write; intros; extensionality b'; t.
Qed.

Hint Rewrite st_write_eq.

(** Writes to unequal addresses commute. *)
Lemma st_write_neq : forall d b b' v v',
  b <> b' ->
  st_write (st_write d b v) b' v' = st_write (st_write d b' v') b v.
Proof.
  unfold st_write; intros; extensionality b''; t.
Qed.

(** When we're writing from the log, initial memory values don't matter in
  * positions that will be overwritten later. *)
Lemma writeLog_overwrite : forall b l d d' v,
  (forall b', b' <> b -> d b' = d' b')
  -> st_write (log_flush l d) b v = st_write (log_flush l d') b v.
Proof.
  induction l; t.
  unfold st_write; extensionality b'; t.
  apply IHl; t.
  unfold st_write; t.
Qed.

(** The starting value of a memory cell is irrelevant if we are writing from
  * a log that ends in a mapping for that cell. *)
Lemma writeLog_last : forall b v l d v',
  log_flush (l ++ (b, v) :: nil) (st_write d b v') = st_write (log_flush l d) b v.
Proof.
  induction l; t.
  destruct (eq_nat_dec b b0); subst.
  rewrite IHl.
  apply writeLog_overwrite; unfold st_write; t.
  rewrite st_write_neq by assumption; eauto.
Qed.

Hint Rewrite writeLog_last.

(** [pflush] implements [log_flush] in the failure-free semantics. *)
Lemma writeLog_flush' : forall l l' tx rx d d',
  d = log_flush l' d ->
  d' = log_flush l d ->
  star psmstep (PSt (pflush l rx) d (l' ++ l) tx) (PSt rx d' (l' ++ l) tx).
Proof.
  induction l; t.
  apply star_refl.
  eapply star_step. econstructor.
  rewrite app_comm_cons in *. eapply IHl; t.
Qed.

Lemma writeLog_flush : forall tx rx d d' l,
  d' = log_flush l d ->
  star psmstep (PSt (pflush l rx) d l tx) (PSt rx d' l tx).
Proof.
  intros; apply writeLog_flush' with (l':=nil); t.
Qed.


(** Pulling out the effect of the last log entry *)
Lemma writeLog_final : forall b v l d,
  log_flush (l ++ [(b, v)]) d = st_write (log_flush l d) b v.
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

  induction ls; t.

  destruct (pfind ls b0); eauto.
  rewrite IHls.
  unfold st_read, st_write; t.

  destruct (pfind ls b); eauto.
  rewrite IHls.
  unfold st_read, st_write; t.
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

Ltac tt := simpl in *; subst; try autorewrite with core in *;
            intuition (eauto; try congruence).
Ltac cc := tt; try constructor; tt.

Theorem tp_forward_sim:
  forall T1 T2, tsmstep T1 T2 ->
  forall P1, tpmatch T1 P1 ->
  exists P2, star psmstep P1 P2 /\ tpmatch T2 P2.
Proof.

  induction 1; intros; inversion H;
  econstructor; split; try (tt; inversion AD; tt).

  destruct tx; cc. auto.

  eapply star_two; cc.
  unfold do_tread; cc.

  eapply star_right. eapply star_right. eapply star_right.
  constructor. constructor. constructor. constructor. cc.
  rewrite readLog_correct.
  destruct (pfind lg b) eqn:F; tt.

  eapply star_two; cc. cc.

  eapply star_two; cc. cc.
  rewrite <- writeLog_final. auto.

  eapply star_three; cc. cc.

  eapply star_one; cc. cc.

  eapply star_one; cc. cc.

  do 3 (eapply star_step; [ cc | idtac ]); tt.
  eapply star_right.
  eapply writeLog_flush. cc. cc. cc.
Qed.


Lemma flush_nofail : forall l m l' tx,
  pexec (pflush l (PClrLog PHalt)) (PSt (pflush l (PClrLog PHalt)) m l' tx) =
                         (PSt PHalt (log_flush l m) nil tx).
Proof.
  induction l; t.
Qed.

Hint Rewrite flush_nofail app_nil_r.

(** Decomposing a writing process *)
Lemma writeLog_app : forall l2 l1 m m',
  log_flush l1 m = m' -> log_flush (l1 ++ l2) m = log_flush l2 m'.
Proof.
  induction l1; t.
Qed.

Lemma pexec_term':
  forall p d l tx s',
  pexec p (PSt p d l tx) = s' -> PSProg s' = PHalt.
Proof.
  intro. induction p; t. destruct s'; t.
Qed.

Lemma pexec_term:
  forall p s s',
  pexec p s = s' -> PSProg s' = PHalt.
Proof.
  destruct s as [p' d l tx].
  induction p; t; match goal with
  | [ H: pexec _ _ = _ |- _ ] => apply pexec_term' in H; auto
  | _ => try inversion H; auto
  end.
Qed.

Lemma trecover_final:
  forall p m l tx s,
  s = pexec (do_trecover PHalt) (PSt p m l tx) ->
  s = (PSt PHalt m nil false) \/
  s = (PSt PHalt (log_flush l m) nil false).
Proof.
  destruct tx; t.
Qed.

Lemma trecover_id:
  forall s1 s2 s3,
  s2 = pexec (do_trecover PHalt) s1 ->
  s3 = pexec (do_trecover PHalt) s2 -> s2 = s3.
Proof.
  intros. destruct s1.
  apply trecover_final in H.
  destruct H; destruct s2 as [p m l tx] eqn:S; inversion H; subst; clear H; t.
Qed.

Lemma pfail_dec':
  forall s s',
  (PSProg s) = PHalt ->
  star psmstep_fail s s' ->
  s' = s \/ s' = pexec (do_trecover PHalt) s.
Proof.
  intros. induction H0.
  left; trivial.
  inversion H0. subst.
  inversion H2; try (destruct s1; inversion H3; subst; discriminate).
  assert (PSProg s2 = PHalt); [ t | apply IHstar in H5 ; destruct H5 ].
  left; t. right; rewrite H4; auto.
  assert (PSProg s2 = PHalt) as T;
  [ eapply pexec_term; eauto | apply IHstar in T ; destruct T ].
  right; t.
  apply eq_sym in H3; right; rewrite <- H3.
  apply eq_sym; apply trecover_id with (s1:=s1); auto.
Qed.


Lemma flush_writeLog_fail' : forall l m l' m' tx l0,
  star psmstep_fail (PSt (pflush l PHalt) m (l' ++ l) tx)
                    (PSt PHalt m' l0 tx)
  -> log_flush l' m = m
  -> m' = log_flush l m.
Proof.
  induction l; t. admit.

  inversion H; inversion H1; t.
  inversion H5; t; rewrite <- H3 in *.
  rewrite app_comm_cons in *.
  eapply IHl; [ eauto | t ].

  clear H H1; destruct tx; t;
  rewrite <- H6 in *; clear H6.
  admit.
  
  inversion H2; t.
  erewrite writeLog_app by eassumption; t.
  admit.
Qed.

Lemma flush_writeLog_fail : forall l m m' tx,
  star psmstep_fail (PSt (pflush l PHalt) m l tx) (PSt PHalt m' l tx)
  -> m' = log_flush l m.
Proof.
  intros; eapply flush_writeLog_fail' with (l':=nil); t.
Qed.


(** Main correctness theorem *)

Theorem correct:
  forall p d d' l' tx',
  star psmstep_fail (PSt (compile_tp p) d nil false) (PSt PHalt d' l' tx') ->
  exists ad, texec p (TSt p d None) = TSt THalt d' ad.
Proof.
  intros; eexists.
  inversion H.
Admitted.

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
  admit. (* must be true because H1 holds *)

  (* general case *) 

Admitted.
  



