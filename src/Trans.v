Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Require Import Bank.
Load Closures.


Section TransactionLanguage.

(** high-level language for a transactional disk *)

Inductive tprog :=
  | TRead  (b:block) (rx:value -> tprog)
  | TWrite (b:block) ( v:value) (rx:tprog)
  | TCommit (rx:tprog)
  | TAbort  (rx:tprog)
  | THalt
  .

Bind Scope tprog_scope with tprog.


Notation "a ;; b" := (a (b))
                       (right associativity, at level 60) : tprog_scope.

Notation "ra <- a ; b" := (a (fun ra => b))
                             (right associativity, at level 60) : tprog_scope.


Open Scope tprog_scope.

Fixpoint compile_at (p:aproc) : tprog :=
  match p with
    | AHalt => THalt
    | ASetAcct a v rx => TWrite a v ;; TCommit ;; compile_at rx
    | ATransfer src dst v rx => r <- TRead src ; TWrite src (r-v) ;;
                   r1 <- TRead dst ; TWrite dst (r1+v) ;; TCommit ;; compile_at rx
  end.

Close Scope tprog_scope.

Record tstate := TSt {
  TSProg: tprog;
  TSDisk: storage;       (* main disk *)
  TSAltDisk: storage;    (* alternative disk for transactions *)
  TSDirty: bool
}.


(* high level interpreter *)
Fixpoint texec (p:tprog) (s:tstate) {struct p} : tstate :=
  let (_, d, ad, dt) := s in
  match p with
  | THalt         => s
  | TRead b rx    => texec (rx (st_read ad b)) (TSt (rx (st_read ad b)) d ad dt)
  | TWrite b v rx => texec rx (TSt rx d (st_write ad b v) true)
  | TCommit rx    => texec rx (TSt rx ad ad false)
  | TAbort rx     => texec rx (TSt rx d d false)
  end.


Inductive tsmstep : tstate -> tstate -> Prop :=
  | TsmHalt: forall d ad dt,
    tsmstep (TSt THalt d ad dt) (TSt THalt d ad dt)
  | TsmRead: forall d ad b dt rx,
    tsmstep (TSt (TRead b rx) d ad dt)    (TSt (rx (st_read ad b)) d ad dt)
  | TsmWrite: forall d ad b v dt rx,
    tsmstep (TSt (TWrite b v rx) d ad dt) (TSt rx d (st_write ad b v) true)
  | TsmCommit:  forall d ad dt rx,
    tsmstep (TSt (TCommit rx) d ad dt)    (TSt rx ad ad false)
  | TsmAbort:  forall d ad dt rx,
    tsmstep (TSt (TAbort rx) d ad dt)     (TSt rx d d false)
  .


Lemma tsmstep_determ:
  forall s0 s s',
  tsmstep s0 s -> tsmstep s0 s' -> s = s'.
Proof.
  intro s0; case_eq s0; intros.
  repeat match goal with
  | [ H: tsmstep _ _ |- _ ] => inversion H; clear H
  end; t.
Qed.

End TransactionLanguage.


Inductive atmatch : astate -> tstate -> Prop :=
  | ATMatchState :
    forall d ap tp ad dd
    (DD: d = dd)
    (AD: d = ad)
    (PP: compile_at ap = tp),
    atmatch (ASt ap d) (TSt tp dd ad false)
  .


Inductive atmatch_fail : astate -> tstate -> Prop :=
  | ATMatchFail :
    forall d ap tp ad dd
    (DD: d = dd)
    (AD: d = ad)
    (PP: tp = THalt),
    atmatch_fail (ASt ap d) (TSt tp dd ad false)
  .


Theorem at_forward_sim:
  forall T1 T2, asmstep T1 T2 ->
  forall P1, atmatch T1 P1 ->
  exists P2, star tsmstep P1 P2 /\ atmatch T2 P2.
Proof.
  induction 1; intros; inversion H; tt.

  econstructor; split; cc.

  econstructor; split; tt.
  eapply star_two; cc. cc.
  
  econstructor; split; tt.
  do 5 (eapply star_step; [ cc | idtac ]).
  cc. cc.
Qed.

Lemma thalt_inv_eq:
  forall s s', (TSProg s) = THalt ->
  star tsmstep s s' ->  s = s'.
Proof.
  intros; destruct s as [ p d ad dt ]; t.
  inversion H0; t. inversion H. rewrite H2 in H.
  eapply star_stuttering; eauto; [ exact tsmstep_determ | constructor ].
Qed.

Definition do_arecover : tprog := TAbort THalt.  (* throw away the ad *)

Theorem at_atomicity:
  forall as1 as2 ts1 tf1 tf2 s s'
    (HS: asmstep as1 as2)
    (HH: (ASProg as2) = AHalt)
    (M1: atmatch as1 ts1)
    (MF1: atmatch_fail as1 tf1)
    (MF2: atmatch_fail as2 tf2)
    (NS: star tsmstep ts1 s)
    (RC: s' = texec do_arecover s),
    s' = tf1 \/ s' = tf2.
Proof.

  (* figure out ts1, the matching state for as1 *)
  intros; inversion M1; repeat subst.

  (* step the high level program to get as2 *)
  (* ... and figure out tf1 tf2 *)
  inversion HS; repeat subst;
  inversion MF1; inversion MF2; repeat subst;
  clear M1 HS MF1 MF2.

  Ltac iv := match goal with
  | [ H: _ = ?a , HS: star tsmstep ?a _ |- _ ] => rewrite <- H in HS; clear H
  | [ H: tsmstep _ _ |- _ ] => inversion H; t; []; clear H
  | [ H: star tsmstep _ _ |- _ ] => inversion H; t; []; clear H
  end.

  (**** step over *)
  (*==== halt *)
  iv. iv.
  right. assert (s2=s); eapply thalt_inv_eq; eauto; crush.

  (*==== set account *)
  iv. iv. iv. iv. iv.
  right. assert (s0=s); eapply thalt_inv_eq; eauto; crush.

  (*==== transfer *)
  do 17 iv.
  right. assert (s6=s); eapply thalt_inv_eq; eauto; crush.
Qed.

