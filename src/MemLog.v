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


Definition do_tread b rx : pprog :=
  tx <- PGetTx;
  if tx then
    l <- PGetLog;
    v <- PRead b;
    match (pfind l b) with
    | Some v => rx v
    | None   => rx v
    end
  else
    v <- PRead b; rx v
.

Definition do_twrite b v rx : pprog :=
  tx <- PGetTx;
  if tx then
    PAddLog b v ;; rx
  else
    PClrLog ;; PSetTx true ;;
    PAddLog b v ;; rx
.

Definition do_tcommit rx : pprog :=
  PSetTx false ;; l <- PGetLog ; pflush l ;; PClrLog ;; rx
.

Definition do_tabort rx : pprog :=
  PSetTx false ;; PClrLog ;; rx
.

Definition do_trecover : pprog :=
  tx <- PGetTx;
  if tx then
    PClrLog ;; PHalt
  else
    l <- PGetLog ; pflush l ;; PClrLog ;; PHalt
.

Close Scope pprog_scope.

Fixpoint compile_tp (p:tprog) : pprog :=
  match p with
  | THalt         => PHalt
  | TRead b rx    => do_tread  b (fun v => compile_tp (rx v))
  | TWrite b v rx => do_twrite b v (compile_tp rx)
  | TCommit rx    => do_tcommit (compile_tp rx)
  | TAbort rx     => do_tabort (compile_tp rx)
  end.

Record pstate := PSt {
  PSProg: pprog;
  PSDisk: storage;
  PSLog: list (block * value);
  PSTInTrans: bool
}.

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
    psmstep_fail s (pexec do_trecover s)
  .

(* state matching *)

Fixpoint log_flush (p:list (block*value)) (d:storage) : storage :=
  match p with
  | nil            => d
  | (b, v) :: rest => log_flush rest (st_write d b v)
  end.

Inductive tpmatch : tstate -> pstate -> Prop :=
  | TPMatchState :
    forall td tp pd lg (tx:bool) pp ad dt
    (DD: td = pd)
    (AD: ad = if tx then (log_flush lg td) else td)
    (TX: tx = dt)
    (PP: compile_tp tp = pp) ,
    tpmatch (TSt tp td ad dt) (PSt pp pd lg tx)
  .


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

Theorem tp_forward_sim:
  forall T1 T2, tsmstep T1 T2 ->
  forall P1, tpmatch T1 P1 ->
  exists P2, star psmstep P1 P2 /\ tpmatch T2 P2.
Proof.
  induction 1; intros; inversion H; eexists.

  (* Halt *)
  destruct tx; cc.

  (* Read *)
  cc. admit.
  
  (* Write *)
  cc; admit.

  (* Commit *)
  cc; admit.

  (* Abort *)
  

(*
  destruct tx; tt.
  unfold do_tread.
  eapply star_right. eapply star_right. eapply star_right. eapply star_right.
  constructor. constructor. constructor. constructor. cc.
  destruct (pfind lg b) eqn:F; tt.

  eapply star_two; cc.
  unfold do_tread; cc.

  eapply star_right. eapply star_right. eapply star_right.
  constructor. constructor. constructor. constructor. cc.
  rewrite readLog_correct.
  destruct (pfind lg b) eqn:F; tt.

  split.
  eapply star_two. cc. cc. tt.
  rewrite <- writeLog_final. cc.

  split. admit. eapply star_two; cc. cc.
  rewrite <- writeLog_final. auto.

  eapply star_three; cc. cc.

  eapply star_one; cc. cc.

  eapply star_one; cc. cc.

  do 3 (eapply star_step; [ cc | idtac ]); tt.
  eapply star_right.
  eapply writeLog_flush. cc. cc. cc.
*)
Admitted.



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


Inductive tpmatch_fail : tstate -> pstate -> Prop :=
  | TPMatchFail :
    forall td tp pd lg (tx:bool) pp ad dt
    (DD: td = pd)
    (AD: ad = if tx then (log_flush lg td) else td)
    (* XXX fix the following also in tpmatch: *)
    (* LG: lg = contains all blocks that have been changed in ad but not in td *)
    (TX: tx = dt)
    (PP: pp = PHalt) ,
    tpmatch_fail (TSt tp td ad dt) (PSt pp pd lg tx).
  

Theorem tp_atomicity:
  forall ts1 ts2 ps1 pf1 pf2 s s'
    (HS: tsmstep ts1 ts2)
    (HH: (TSProg ts2) = THalt)
    (M1: tpmatch ts1 ps1)
    (MF1: tpmatch_fail ts1 pf1)
    (MF2: tpmatch_fail ts2 pf2)
    (NS: star psmstep ps1 s)
    (RC: s' = pexec do_trecover s),
    s' = pf1 \/ s' = pf2.
Proof.
  (* figure out ts1, the matching state for as1 *)
  intros; inversion M1; repeat subst.

  (* step the high level program to get as2 *)
  (* ... and figure out tf1 tf2 *)
  inversion HS; repeat subst;
  inversion MF1; inversion MF2; repeat subst;
  clear M1 HS MF1 MF2.

  (* THalt *)
  inversion NS; t.
  clear NS.
  destruct dt.   (* destruct on InTrans *)

Admitted.