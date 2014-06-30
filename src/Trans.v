Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Require Import Bank.
Load Closures.


Section TransactionLanguage.

(** language for a logging transaction *)

Inductive tprog :=
  | THalt
  | TCommit (rx:tprog)
  | TRead  (b:block) (rx:value -> tprog)
  | TWrite (b:block) ( v:value) (rx:tprog)
  | TAddLog (b:block) (v:nat) (rx:tprog)
  | TClrLog (rx:tprog)
  | TGetLog (rx:list (block * value) -> tprog)
  | TGetCommitted (rx:bool -> tprog).
  

Bind Scope tprog_scope with tprog.


Notation "a ;; b" := (a (b))
                       (right associativity, at level 60) : tprog_scope.

Notation "ra <- a ; b" := (a (fun ra => b))
                             (right associativity, at level 60) : tprog_scope.


Open Scope tprog_scope.

Fixpoint log_read (p:list (block * value)) (b:block) : option value :=
  match p with
  | nil => None
  | (b', v) :: rest =>
    match (log_read rest b) with
    | None => if eq_nat_dec b b' then Some v else None
    | x    => x
    end
  end.


Definition do_tread b rx : tprog :=
  l <- TGetLog;
  match (log_read l b) with
    | Some v => rx v
    | None   => v <- TRead b; rx v
  end.

Fixpoint flush_tprog (p:list (block*value)) rx : tprog :=
  match p with
  | nil            => rx
  | (b, v) :: rest => TWrite b v ;; flush_tprog rest rx
  end.

  
Fixpoint compile_at (p:aproc) : tprog :=
  match p with
    | ACommit => TCommit;; THalt
    | ASetAcct a v rx => TAddLog a v ;; compile_at rx
    | AGetAcct a rx => do_tread  a (fun v => compile_at (rx v))
    | ATransfer src dst v rx => r <- TRead src ; TAddLog src (r-v) ;;
                   r1 <- TRead dst ; TAddLog dst (r1+v) ;; compile_at rx
  end.

Definition do_trecover : tprog := 
  c <- TGetCommitted;
  if c then
    l <- TGetLog ; flush_tprog l ;; TClrLog ;; TCommit ;; THalt
  else
    TClrLog ;; THalt.   (* maybe not necessary *)

Close Scope tprog_scope.

Record tstate := TSt {
  TSProg: tprog;
  TSDisk: storage;       (* main disk *)
  TSLog: list (block * value);  (* log of uncommited writes *)
  TSCommit: bool  (* has transaction committed? *)
}.

Fixpoint log_flush (p:list (block*value)) (d:storage) : storage :=
  match p with
  | nil            => d
  | (b, v) :: rest => log_flush rest (st_write d b v)
  end.

(* interpreter for logging language *)
Fixpoint texec (p:tprog) (s:tstate) {struct p} : tstate :=
  let (_, d, l, c) := s in
  match p with
  | THalt => s
  | TCommit rx => texec rx (TSt rx (log_flush l d) nil true)
  | TRead b rx    => texec (rx (st_read d b)) (TSt (rx (st_read d b)) d l c)
  | TWrite b v rx => texec rx (TSt rx (st_write d b v) l c)
  | TAddLog b v rx  => texec rx (TSt rx d (l ++ [(b, v)]) c)
  | TClrLog rx      => texec rx (TSt rx d nil c)
  | TGetLog rx      => texec (rx l) (TSt (rx l) d l c)
  | TGetCommitted rx    => texec (rx c) (TSt (rx c) d l c)
  end.

Inductive tsmstep : tstate -> tstate -> Prop :=
  | TsmRead: forall d l b c rx,
    tsmstep (TSt (TRead b rx) d l c)    (TSt (rx (st_read d b)) d l c)
  | TsmWrite: forall d l b v c rx,
    tsmstep (TSt (TWrite b v rx) d l c) (TSt rx (st_write d b v) l c)
  | TsmAddLog: forall d l b v c rx,
    tsmstep (TSt (TAddLog b v rx) d l c)
            (TSt rx d (l ++ [(b, v)]) c)
  | TsmClrLog: forall d l c rx,
    tsmstep (TSt (TClrLog rx) d l c)
            (TSt rx d nil c)
  | TsmGetLog: forall d l c rx,
    tsmstep (TSt (TGetLog rx) d l c)
            (TSt (rx l) d l c)
  | TsmCommit:  forall d l c rx,
    tsmstep (TSt (TCommit rx) d l c) (TSt rx (log_flush l d) nil true)
  | TsmGetCommit: forall d l c rx,
    tsmstep (TSt (TGetCommitted rx) d l c)
            (TSt (rx c) d l c)
  | TsmCrash:
      forall d l c rx,
        tsmstep (TSt rx d l c)  (TSt THalt d l c).
     
End TransactionLanguage.



Hint Rewrite st_write_eq.

(** The starting value of a memory cell is irrelevant if we are writing from
  * a log that ends in a mapping for that cell. *)
Lemma writeLog_last : forall b v l d,
  log_flush (l ++ [(b, v)]) d = st_write (log_flush l d) b v.
Proof.
  induction l; t.
Admitted.

Lemma app_comm_cons : forall A (ls1 : list A) x ls2,
  ls1 ++ x :: ls2 = (ls1 ++ x :: nil) ++ ls2.
Proof.
  intros.
  apply (app_assoc ls1 [x] ls2).
Qed.

(** [readLog] interacts properly with [writeLog]. *)
Lemma readLog_correct : forall b ls d,
  st_read (log_flush ls d) b = match log_read ls b with
                            | Some v => v
                            | None => st_read d b
                          end.
Proof.

  induction ls; t.

  destruct (log_read ls b0); eauto.
  rewrite IHls.
  unfold st_read, st_write; t.

  destruct (log_read ls b); eauto.
  rewrite IHls.
  unfold st_read, st_write; t.
Qed.

Hint Rewrite writeLog_last.
Hint Rewrite readLog_correct.

(* Strengthen induction for main theorem (in main theorem: l = nil) *)
Lemma correct : forall p d da l t t',
  da = aexec p (log_flush l d) -> 
  (TSProg t) = THalt ->
  star tsmstep (TSt (compile_at p) d l false) t ->
  t' = texec do_trecover t ->
  (TSDisk t') = d \/ (TSDisk t') = da.
Proof.
  induction p.

  (* ACommit *)
  - intros.
    admit.

  (* ASetAcct *)
  - intros.
    admit.

  (* AGetAcct *)
  - intros.
    admit.

  (* ATransfer *)
  - intros.
    admit.
  
Admitted.


(* XXX not used:

(* recursive case *)

Inductive atmatch : astate -> tstate -> Prop :=
  | ATMatchState :
    forall ad ap (ac:bool) tp td tl (tc:bool)
    (DD: ad = if ac then log_flush tl td else td)
    (TC: ac = tc)
    (PP: compile_at ap = tp),
    atmatch (ASt ap ad ac) (TSt tp td tl tc).
  

Inductive atmatch_fail : astate -> tstate -> Prop :=
  | ATMatchFail :
    forall ad ap ac tp td tl (tc:bool)
    (DD: ad = if tc then log_flush tl td else td)
    (TC: ac = tc)
    (PP: tp = TAbort),
    atmatch_fail (ASt ap ad ac) (TSt tp td tl tc).




Lemma thalt_inv_eq:
  forall s s', (TSProg s) = TAbort ->
  star tsmstep s s' ->  s = s'.
Proof.
  intros; destruct s as [ p d ad dt ]; t.
  inversion H0; t. inversion H. rewrite H2 in H.
  eapply star_stuttering; eauto; [ exact tsmstep_determ | constructor ].
Qed.



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
    (RC: s' = texec do_trecover s),
    s' = tf1 \/ s' = tf2.
Proof.

  (* figure out ts1, the matching state for as1 *)
  intros; inversion M1; repeat subst.

  (* step the high level program to get as2 *)
  (* ... and figure out tf1 tf2 *)
  inversion HS; subst.
  inversion MF1; inversion MF2; repeat subst.
  clear M1 HS MF1 MF2.

  Ltac iv := match goal with
  | [ H: _ = ?a , HS: star tsmstep ?a _ |- _ ] => rewrite <- H in HS; clear H
  | [ H: tsmstep _ _ |- _ ] => inversion H; t; []; clear H
  | [ H: star tsmstep _ _ |- _ ] => inversion H; t; []; clear H
  end.

  Ltac tsmstep_end := inversion M2; subst;
    try match goal with
    | [ H0: ?a = ?b,
        H1: star tsmstep _ {| TSProg := _; TSDisk := ?a; TSLog := ?b |}
        |- _ ] => rewrite <- H0 in H1
    end; apply tsmstep_loopfree; auto.

  (**** step over *)
  (*==== halt *)
  inversion NS; t.
  cc; t.
  admit.

  (*==== set account *)
  inversion NS; t.

  iv. iv. iv. iv. iv.
  right. assert (s0=s); [ tsmstep_end | crush ].

  (*==== get account *)
  iv. iv.
  right. assert (s2=s); [ tsmstep_end | crush ].

  (*==== transfer *)
  do 14 iv.
  right. assert (s5=s); [ tsmstep_end | crush ].

Admitted.

*)