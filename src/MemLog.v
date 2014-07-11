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


(* language that manipulates a disk and a persistent log *)

Inductive pprog :=
  | PRead   (b:block) (rx:value -> pprog)
  | PWrite  (b:block) ( v:value) (rx:pprog)
  | PAddLog (b:block) ( v:value) (rx:pprog)
  | PClrLog (rx:pprog)
  | PGetLog (rx:list (block * value) -> pprog)
  | PSetTx  (v:bool) (rx:pprog)
  | PGetTx  (rx:bool -> pprog)
  | PHalt.

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


Definition do_tread b rx : pprog :=
  l <- PGetLog;
  v <- PRead b;
  match (pfind l b) with
  | Some v' => rx v'
  | None    => rx v
  end.

Definition do_twrite b v rx : pprog :=
  PAddLog b v ;; rx.

Definition do_apply_log rx : pprog :=
  l <- PGetLog ; pflush l ;; PClrLog ;; rx.

Definition do_tbegin rx : pprog :=
  do_apply_log (PSetTx true ;; rx).

Definition do_tcommit rx : pprog :=
  PSetTx false ;; do_apply_log rx.

Definition do_tabort rx : pprog :=
  tx <- PGetTx;
  if tx then
    PClrLog ;; PSetTx false ;; rx
  else
    rx.

Definition do_precover : pprog :=
  tx <- PGetTx;
  if tx then
    PClrLog ;; PSetTx false ;; PHalt
  else
    do_apply_log PHalt.

Close Scope pprog_scope.

Fixpoint compile_tp (p:tprog) : pprog :=
  match p with
  | THalt         => PHalt
  | TBegin rx     => do_tbegin (compile_tp rx)
  | TRead b rx    => do_tread  b (fun v => compile_tp (rx v))
  | TWrite b v rx => do_twrite b v (compile_tp rx)
  | TCommit rx    => do_tcommit (compile_tp rx)
  | TAbort rx     => do_tabort (compile_tp rx)
  end.

Record pstate := PSt {
  PSProg: pprog;
  PSDisk: storage;
  PSLog: list (block * value);
  PSInTrans: bool
}.

Inductive psmstep : pstate -> pstate -> Prop :=
  | PsmHalt: forall d l it,
    psmstep (PSt PHalt d l it) (PSt PHalt d l it)
  | PsmRead: forall d l b rx it,
    psmstep (PSt (PRead b rx) d l it)
            (PSt (rx (st_read d b)) d l it)
  | PsmWrite: forall d l b v rx it,
    psmstep (PSt (PWrite b v rx) d l it)
            (PSt rx (st_write d b v) l it)
  | PsmAddLog: forall d l b v rx it,
    psmstep (PSt (PAddLog b v rx) d l it)
            (PSt rx d (l ++ [(b, v)]) it)
  | PsmClrLog: forall d l rx it,
    psmstep (PSt (PClrLog rx) d l it)
            (PSt rx d nil it)
  | PsmGetLog: forall d l rx it,
    psmstep (PSt (PGetLog rx) d l it)
            (PSt (rx l) d l it)
  | PsmSetTx: forall d l v rx it,
    psmstep (PSt (PSetTx v rx) d l it)
            (PSt rx d l v)
  | PsmGetTx: forall d l rx it,
    psmstep (PSt (PGetTx rx) d l it)
            (PSt (rx it) d l it).

Fixpoint pexec (p:pprog) (s:pstate) {struct p} : pstate :=
  let (_, d, l, it) := s in
  match p with
  | PHalt           => (PSt p d l it)
  | PRead b rx      => pexec (rx (st_read d b)) (PSt (rx (st_read d b)) d l it)
  | PWrite b v rx   => pexec rx (PSt rx (st_write d b v) l it)
  | PAddLog b v rx  => pexec rx (PSt rx d (l ++ [(b, v)]) it)
  | PClrLog rx      => pexec rx (PSt rx d nil it)
  | PGetLog rx      => pexec (rx l) (PSt (rx l) d l it)
  | PSetTx v rx     => pexec rx (PSt rx d l v)
  | PGetTx rx       => pexec (rx it) (PSt (rx it) d l it)
  end.

(** If no failure, psmstep and pexec are equivalent *)
Lemma pexec_smstep :
  forall p d l it s',
  pexec p (PSt p d l it) = s' -> star psmstep (PSt p d l it) s'.
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
  forall p d l it d' l' it',
  star psmstep (PSt p d l it) (PSt PHalt d' l' it') ->
  pexec p (PSt p d l it) = (PSt PHalt d' l' it').
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
    psmstep_fail s (pexec do_precover s).

(* state matching *)

Fixpoint log_flush (p:list (block*value)) (d:storage) : storage :=
  match p with
  | nil            => d
  | (b, v) :: rest => log_flush rest (st_write d b v)
  end.


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

Hint Rewrite st_write_eq.

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

Lemma app_comm_cons : forall A (ls1 : list A) x ls2,
  ls1 ++ x :: ls2 = (ls1 ++ x :: nil) ++ ls2.
Proof.
  intros.
  apply (app_assoc ls1 [x] ls2).
Qed.

(** [pflush] implements [log_flush] in the failure-free semantics. *)
Lemma writeLog_flush':
  forall l l' tx rx d d',
  d = log_flush l' d ->
  d' = log_flush l d ->
  star psmstep (PSt (pflush l rx) d (l' ++ l) tx) (PSt rx d' (l' ++ l) tx).
Proof.
  induction l; t.
  apply star_refl.
  eapply star_step. econstructor.
  rewrite app_comm_cons in *. eapply IHl; t.
Qed.

Lemma writeLog_flush:
  forall rx d d' l tx,
  d' = log_flush l d ->
  star psmstep (PSt (pflush l rx) d l tx) (PSt rx d' l tx).
Proof.
  intros; apply writeLog_flush' with (l':=nil); t.
Qed.


(** Pulling out the effect of the last log entry *)
Lemma writeLog_final:
  forall b v l d,
  log_flush (l ++ [(b, v)]) d = st_write (log_flush l d) b v.
Proof.
  induction l; intuition; simpl; auto.
Qed.

(** [readLog] interacts properly with [writeLog]. *)
Lemma readLog_correct:
  forall b ls d,
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


Inductive tpmatch : tstate -> pstate -> Prop :=
  | TPMatchStateTx:
    forall td tp pd lg pp ad
    (DD: td = pd)
    (AD: ad = log_flush lg td)
    (PP: compile_tp tp = pp),
    tpmatch (TSt tp td (Some ad)) (PSt pp pd lg true)
  | TPMatchStateNoTx:
    forall td tp pd lg pp
    (DD: td = log_flush lg pd)
    (PP: compile_tp tp = pp),
    tpmatch (TSt tp td None) (PSt pp pd lg false).

Hint Constructors tpmatch.

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
  induction 1; intros; inversion H.

  - (* Halt, in txn *)
    eexists; cc.
  - (* Halt, no txn *)
    eexists; cc.

  - (* Read, in txn *)
    tt; unfold do_tread; eexists; split.
    eapply star_right. eapply star_right.
    constructor. constructor. constructor. cc.
    rewrite readLog_correct.
    destruct (pfind lg b) eqn:F; tt.

  - (* Write, in txn *)
    tt; eexists; split.
    eapply star_one; cc.
    rewrite <- writeLog_final; cc.

  - (* Commit, in txn *)
    tt; eexists; split.
    do 2 (eapply star_step; [ cc | idtac ]); tt.
    eapply star_right.
    eapply writeLog_flush; cc. cc. cc.

  - (* Abort, in txn *)
    eexists; split.
    eapply star_three; cc. cc.
  - (* Abort, no txn *)
    eexists; split.
    eapply star_one; cc. cc.

  - (* Begin, no txn *)
    eexists; split.
    eapply star_step; [ cc | idtac ].
    eapply star_trans.
    apply writeLog_flush; auto.
    eapply star_two; cc. cc.
Qed.


Lemma flush_nofail:
  forall l m l' tx,
  pexec (pflush l (PClrLog PHalt))
   (PSt (pflush l (PClrLog PHalt)) m l' tx) =
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
  destruct s as [p' d l].
  induction p; t; match goal with
  | [ H: pexec _ _ = _ |- _ ] => apply pexec_term' in H; auto
  | _ => try inversion H; auto
  end.
Qed.

(*
Lemma trecover_final:
  forall p m l tx s,
  s = pexec (do_trecover) (PSt p m l tx) ->
  s = (PSt PHalt m nil false) \/
  s = (PSt PHalt (log_flush l m) nil false).
Proof.
  destruct tx; t.
Qed.

Lemma trecover_id:
  forall s1 s2 s3,
  s2 = pexec (do_trecover) s1 ->
  s3 = pexec (do_trecover) s2 -> s2 = s3.
Proof.
  intros. destruct s1.
  apply trecover_final in H.
  destruct H; destruct s2 as [p m l tx] eqn:S; inversion H; subst; clear H; t.
Qed.

Lemma pfail_dec:
  forall s s',
  (PSProg s) = PHalt ->
  star psmstep_fail s s' ->
  s' = s \/ s' = pexec (do_trecover) s.
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
  induction l; t.
  apply pfail_dec in H; intuition; try congruence.
  apply trecover_final in H1; t.

  inversion H; inversion H1; t.
  inversion H5; t; rewrite <- H3 in *.
  rewrite app_comm_cons in *.
  eapply IHl; [ eauto | t ].

  clear H H1; destruct tx; t;
  rewrite <- H6 in *; clear H6.
  apply pfail_dec in H2; intuition; try congruence.
  apply trecover_final in H; t.

  inversion H2; t.
  erewrite writeLog_app by eassumption; t.
  apply pfail_dec in H2; t;
  inversion H3; t; rewrite app_comm_cons; apply writeLog_app;
  rewrite <- H0; rewrite <- writeLog_final; t.
Qed.

Lemma flush_writeLog_fail : forall l m m' tx,
  star psmstep_fail (PSt (pflush l PHalt) m l tx) (PSt PHalt m' l tx)
  -> m' = log_flush l m.
Proof.
  intros; eapply flush_writeLog_fail' with (l':=nil); t.
Qed.
*)

(** Main correctness theorem *)

Lemma phalt_inv_eq:
  forall s s', (PSProg s) = PHalt ->
  star psmstep s s' ->  s = s'.
Proof.
  intros; destruct s as [ p d ad dt ]; t.
  inversion H0; t. inversion H. rewrite H2 in H.
  eapply star_stuttering; eauto; [ exact psmstep_determ | constructor ].
Qed.


Lemma psmstep_loopfree:
  forall pA pB d1 d2 d3 l1 l2 l3 t1 t2 t3,
  star psmstep (PSt pA d1 l1 t1) (PSt pB d2 l2 t2) ->
  star psmstep (PSt pB d2 l2 t2) (PSt pA d3 l3 t3) ->
  (PSt pA d1 l1 t1) = (PSt pB d2 l2 t2).
Proof.
  admit.
Qed.


Inductive tpmatch_fail : tstate -> pstate -> Prop :=
  | TPMatchFail :
    forall td tp pd pp oad
    (DD: td = pd)
    (PP: pp = PHalt),
    tpmatch_fail (TSt tp td oad) (PSt pp pd nil false).

Hint Constructors tpmatch_fail.


Lemma flush_twice:
  forall lg pd,
  log_flush lg (log_flush lg pd) = log_flush lg pd.
Proof.
  admit.
Qed.

Hint Rewrite flush_twice.

Lemma flush_failures':
  forall lg l0 l1 rx pd s tp,
  lg = l0 ++ l1 ->
  star psmstep (PSt (pflush l1 ;; rx) (log_flush l0 pd) lg false) s ->
  star psmstep s (PSt rx (log_flush lg pd) lg false) ->
  tpmatch_fail (TSt tp (log_flush lg pd) None) (pexec do_precover s).
Proof.
  induction l1.
  - intros. assert (s=(PSt rx (log_flush l0 pd) l0 false)). destruct s.
    apply psmstep_loopfree with (d3:=PSDisk0) (l3:=PSLog0) (t3:=PSInTrans0); crush.
    repeat subst. simpl. rewrite flush_nofail. constructor; auto.
    admit.
  - (* XXX *)
Abort.

Lemma flush_terminates:
  forall lg rx pd s s2,
  star psmstep (PSt (pflush lg ;; rx) pd lg false) s ->
  star psmstep s s2 ->
  (star psmstep (PSt (pflush lg ;; rx) pd lg false)
                (PSt rx (log_flush lg pd) lg false) /\
   star psmstep (PSt rx (log_flush lg pd) lg false) s2 /\
   ((star psmstep s (PSt rx (log_flush lg pd) lg false)) \/
    (star psmstep (PSt rx (log_flush lg pd) lg false) s))).
Proof.
  admit.
Qed.

Lemma flush_failures:
  forall lg rx pd s tp,
  star psmstep (PSt (pflush lg ;; rx) pd lg false) s ->
  star psmstep s (PSt rx (log_flush lg pd) lg false) ->
  tpmatch_fail (TSt tp (log_flush lg pd) None) (pexec do_precover s).
Proof.
  admit.
Qed.


Theorem tp_atomicity:
  forall ts1 ts2 ps1 ps2 s s'
    (HS: tsmstep ts1 ts2)
    (M1: tpmatch ts1 ps1)
    (M2: tpmatch ts2 ps2)
    (NS1: star psmstep ps1 s)
    (NS2: star psmstep s ps2)
    (RC: s' = pexec do_precover s),
    tpmatch_fail ts1 s' \/ tpmatch_fail ts2 s'.
Proof.
  (* figure out ps1, the matching state for ts1 *)
  intros; inversion M1; repeat subst;

  (* step the high level program to get ts2 *)
  inversion HS; repeat subst; clear M1 HS.

  Ltac iv := match goal with
  | [ H: _ = ?a , HS: star psmstep ?a _ |- _ ] => rewrite <- H in HS; clear H
  | [ H: psmstep _ _ |- _ ] => inversion H; t; []; clear H
  | [ H: star psmstep _ _ |- _ ] => inversion H; t; []; clear H
  end.

  - (* THalt, in txn *)
    do 2 iv. right.
    cut (s2=s).  crush.
    destruct s; destruct s2.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=true); crush.

  - (* TRead, in txn *)
    do 5 iv. right.
    cut (s0=s).  crush.
    destruct s; destruct s0.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=true);
    [ crush | rewrite readLog_correct in *; destruct (pfind lg b); crush ].

  - (* TWrite, in txn *)
    do 2 iv. right.
    cut (s2=s).  crush.
    destruct s; destruct s2.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=true); crush.

  - (* TCommit, in txn *)
    do 2 iv.
    right.  (* COMMIT POINT *)
    do 3 iv.
    destruct flush_terminates with (lg:=lg) (rx:=PClrLog (compile_tp rx))
                                   (pd:=pd) (s:=s) (s2:=ps2); [ crush | crush | idtac ].
    destruct H2.  destruct H3.
    apply flush_failures with (rx:=PClrLog (compile_tp rx)); crush.

    clear H. clear H0. clear H1. clear H2.
    do 2 iv.
    cut (s3=s). crush.
    destruct s; destruct s3.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=false); crush.

  - (* TAbort, in txn *)
    do 8 iv. right.
    cut (s3=s).  crush.
    destruct s; destruct s3.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=false); crush.

  - (* THalt, no txn *)
    do 2 iv. right.
    cut (s2=s). crush. rewrite flush_nofail. crush.
    destruct s; destruct s2.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=false); crush.

  - (* TAbort, no txn *)
    do 2 iv. right.
    cut (s2=s). crush. rewrite flush_nofail. crush.
    destruct s; destruct s2.
    inversion M2; clear M2; repeat subst.
    apply psmstep_loopfree with (d3:=pd0) (l3:=lg0) (t3:=false); crush.

  - (* TBegin, no txn *)
    do 2 iv. left.
    destruct flush_terminates with (lg:=lg) (rx:=PClrLog (PSetTx true (compile_tp rx)))
                                   (pd:=pd) (s:=s) (s2:=ps2); [ crush | crush | idtac ].
    destruct H2; destruct H3.
    apply flush_failures with (rx:=PClrLog (PSetTx true (compile_tp rx))); crush.

    clear H. clear H0. clear H1. clear H2.
    do 5 iv.
    cut (s3=s). crush.
    destruct s; destruct s3.
    inversion M2; clear M2; repeat subst.
    inversion H0; repeat subst.
    apply psmstep_loopfree with (d3:=log_flush lg pd) (l3:=lg0) (t3:=true); crush.
Qed.
