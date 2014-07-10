Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Require Import Bank.
Load Closures.

Require Import Disk.
Require Import Trans2.


Section TransactionLanguage.

(** language for a transactional disk *)

Inductive tprog :=
  | TBegin (rx:tprog)
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
    | ASetAcct a v rx => TBegin ;; TWrite a v ;; TCommit ;; compile_at rx
    | AGetAcct a rx => TBegin ;; v <- TRead a; TCommit ;; compile_at (rx v)
    | ATransfer src dst v rx => TBegin ;; r <- TRead src ; TWrite src (r-v) ;;
                   r1 <- TRead dst ; TWrite dst (r1+v) ;; TCommit ;; compile_at rx
  end.

Fixpoint do_t2dprog (d:dprog) (rx:tprog) : tprog :=
  match d with
  | DHalt => rx
  | DWrite b v drx => TWrite b v ;; do_t2dprog drx rx
  | DRead b drx => v <- TRead b ; do_t2dprog (drx v) rx
  end.

Fixpoint compile_t2t (t2:t2prog) : tprog :=
  match t2 with
  | T2Halt => THalt
  | T2Begin rx => TBegin (compile_t2t rx)
  | T2Commit rx => TCommit (compile_t2t rx)
  | T2Abort rx => TAbort (compile_t2t rx)
  | T2DProg d rx => do_t2dprog d (compile_t2t rx)
  end.

Close Scope tprog_scope.

Record tstate := TSt {
  TSProg: tprog;
  TSDisk: storage;       (* main disk *)
  TSAltDisk: storage;    (* alternative disk for transactions *)
  TSInTrans: bool        (* in transaction? the first write starts the transaction *)
}.


(* high level interpreter *)
Fixpoint texec (p:tprog) (s:tstate) {struct p} : tstate :=
  let (_, d, ad, dt) := s in
  match p with
  | THalt         => s
  | TRead b rx    => texec (rx (st_read ad b)) (TSt (rx (st_read ad b)) d ad dt)
  | TWrite b v rx => texec rx (TSt rx d (st_write ad b v) dt)
  | TBegin rx     => texec rx (TSt rx d ad true)
  | TCommit rx    => texec rx (TSt rx ad ad false)
  | TAbort rx     => texec rx (TSt rx d d false)
  end.


Inductive tsmstep : tstate -> tstate -> Prop :=
  | TsmHalt: forall d ad dt,
    tsmstep (TSt THalt d ad dt)             (TSt THalt d ad dt)
  | TsmRead: forall d ad b rx,
    tsmstep (TSt (TRead b rx) d ad true)    (TSt (rx (st_read ad b)) d ad true)
  | TsmWrite: forall d ad b v rx,
    tsmstep (TSt (TWrite b v rx) d ad true) (TSt rx d (st_write ad b v) true)
  | TsmCommit:  forall d ad rx,
    tsmstep (TSt (TCommit rx) d ad true)    (TSt rx ad ad false)
  | TsmAbort:  forall d ad rx,
    tsmstep (TSt (TAbort rx) d ad true)     (TSt rx d d false)
  | TsmBegin: forall d ad rx,
    tsmstep (TSt (TBegin rx) d ad false)    (TSt rx d ad true).

Hint Constructors tsmstep.


Lemma tsmstep_determ:
  forall s0 s s',
  tsmstep s0 s -> tsmstep s0 s' -> s = s'.
Proof.
  intro s0; case_eq s0; intros.
  repeat match goal with
  | [ H: tsmstep _ _ |- _ ] => inversion H; clear H
  end; t.
Qed.

Lemma tsmstep_loopfree:
  forall a b,
  star tsmstep a b -> star tsmstep b a -> a = b.
Proof.
  admit.
Qed.

End TransactionLanguage.


Inductive atmatch : astate -> tstate -> Prop :=
  | ATMatchState :
    forall d ap tp ad dd
    (DD: d = dd)
    (AD: d = ad)
    (PP: compile_at ap = tp),
    atmatch (ASt ap d) (TSt tp dd ad false).

Inductive t2tmatch : t2state -> tstate -> Prop :=
  | T2TMatchState:
    forall tp t2p dd ad it
    (PP: compile_t2t t2p = tp),
    t2tmatch (T2St t2p dd ad it) (TSt tp dd ad it).


Inductive atmatch_fail : astate -> tstate -> Prop :=
  | ATMatchFail :
    forall d ap tp ad dd
    (DD: d = dd)
    (AD: d = ad)
    (PP: tp = THalt),
    atmatch_fail (ASt ap d) (TSt tp dd ad false).

Inductive t2tmatch_fail : t2state -> tstate -> Prop :=
  | T2TMatchFail:
    forall tp t2p dd ad it
    (PP: tp = THalt),
    t2tmatch_fail (T2St t2p dd ad it) (TSt tp dd ad it).

Hint Constructors t2tmatch.
Hint Constructors t2tmatch_fail.


Theorem at_forward_sim:
  forall T1 T2, asmstep T1 T2 ->
  forall P1, atmatch T1 P1 ->
  exists P2, star tsmstep P1 P2 /\ atmatch T2 P2.
Proof.
  induction 1; intros; inversion H; tt.

  - econstructor; split; cc.

  - econstructor; split; tt.
    eapply star_three; cc. cc.

  - econstructor; split; tt.
    eapply star_three; cc. cc.
  
  - econstructor; split; tt.
    do 6 (eapply star_step; [ cc | idtac ]).
    cc. cc.
Qed.

Theorem t2t_forward_sim:
  forall T1 T2,
  t2smstep T1 T2 ->
  forall P1, t2tmatch T1 P1 ->
  exists P2, star tsmstep P1 P2 /\ t2tmatch T2 P2.
Proof.
  induction 1; intros; inversion H; tt.

  (* T2Halt *)
  - econstructor; split; cc.

  (* T2Begin *)
  - econstructor; split; tt.
    eapply star_one; cc.

  (* T2DProg *)
  - exists (TSt (compile_t2t rx) d (drun dp ad) true); split.

    generalize H; clear H;
    generalize ad; clear ad.
    induction dp; simpl; intros.
    + eapply star_step; [ constructor | crush ].
    + eapply star_step; [ constructor | crush ].
    + apply star_refl.
    + crush.

  (* T2Commit *)
  - econstructor; split; tt.
    eapply star_one; cc.

  (* T2Abort *)
  - econstructor; split; tt.
    eapply star_one; cc.
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

(* a few important assumptions are built into this theorem:

- at this level, failures happen only between t language instructions

- failures are fail-stop

- type storage maintains its content across failures

XXX it would be nice to formulate this failure model more explicitly.

*)

Theorem at_atomicity:
  forall as1 as2 ts1 ts2 tf1 tf2 s s'
    (HS: asmstep as1 as2)
    (M1: atmatch as1 ts1)
    (M2: atmatch as2 ts2)
    (MF1: atmatch_fail as1 tf1)
    (MF2: atmatch_fail as2 tf2)
    (NS: star tsmstep ts1 s)
    (NS2: star tsmstep s ts2)
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

  Ltac tsmstep_end := inversion M2; subst;
    try match goal with
    | [ H0: ?a = ?b,
        H1: star tsmstep _ {| TSProg := _; TSDisk := ?a; TSAltDisk := ?b; TSInTrans := _ |}
        |- _ ] => rewrite <- H0 in H1
    end; apply tsmstep_loopfree; auto.

  (**** step over *)
  (*==== halt *)
  - iv. iv.
    right. assert (s2=s); [ tsmstep_end | crush ].

  (*==== set account *)
  - iv. iv. iv. iv. iv. iv. iv. iv.
    right. assert (s3=s); [ tsmstep_end | crush ].

  (*==== get account *)
  - iv. iv. iv. iv. iv. iv. iv. iv.
    right. assert (s3=s); [ tsmstep_end | crush ].

  (*==== transfer *)
  - do 17 iv.
    right. assert (s6=s); [ tsmstep_end | crush ].
Qed.
