Require Import FunctionalExtensionality.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import List.
Require Import Mem.
Require Import PredCrash.
Require Import AsyncDisk.
Require Import Word.
Require Automation.

Import ListNotations.

Set Implicit Arguments.

(** * The programming language *)

(** single program *)
Inductive prog : Type -> Type :=
  | Ret T (v: T) : prog T
  | Read (a: addr) : prog valu
  | Write (a: addr) (v: valu) : prog unit
  | Sync : prog unit
  | Trim (a: addr) : prog unit
  | Hash (sz: nat) (buf: word sz) : prog (word hashlen)
  | Bind T T' (p1: prog T) (p2: T -> prog T') : prog T'.

Arguments Ret {T} v.

Inductive outcome (T : Type) :=
  | Failed
  | Finished (m: rawdisk) (hm: hashmap) (v: T)
  | Crashed (m: rawdisk) (hm: hashmap).

Inductive step : forall T,
    rawdisk -> hashmap -> prog T ->
    rawdisk -> hashmap -> T -> Prop :=
| StepRead : forall m a v x hm,
    m a = Some (v, x) ->
    step m hm (Read a) m hm v
| StepWrite : forall m a v v0 x hm,
    m a = Some (v0, x) ->
    step m hm (Write a v) (upd m a (v, v0 :: x)) hm tt
| StepSync : forall m hm,
    step m hm (Sync) (sync_mem m) hm tt
| StepTrim : forall m a vs vs' hm,
    m a = Some vs ->
    step m hm (Trim a) (upd m a vs') hm tt
| StepHash : forall m sz (buf : word sz) h hm,
    hash_safe hm h buf ->
    hash_fwd buf = h ->
    step m hm (Hash buf) m (upd_hashmap' hm h buf) h.

Inductive fail_step : forall T,
    rawdisk -> prog T -> Prop :=
| FailRead : forall m a,
    m a = None ->
    fail_step m (Read a)
| FailWrite : forall m a v,
    m a = None ->
    fail_step m (Write a v).

Inductive crash_step : forall T, prog T -> Prop :=
| CrashRead : forall a,
    crash_step (Read a)
| CrashWrite : forall a v,
    crash_step (Write a v).

Module StepPresync.

  Import Automation.

  Hint Constructors step.
  Hint Resolve possible_sync_trans.
  Hint Resolve ListUtils.incl_cons2.

  Theorem possible_sync_after_sync : forall A AEQ (m m': @mem A AEQ _),
      possible_sync (sync_mem m) m' ->
      m' = sync_mem m.
  Proof.
    unfold possible_sync, sync_mem; intros.
    extensionality a.
    specialize (H a).
    destruct matches in *; intuition eauto;
      repeat deex;
      try congruence.
    inversion H1; subst; eauto.
    apply ListUtils.incl_in_nil in H3; subst; eauto.
  Qed.

  Lemma possible_sync_respects_upd : forall A AEQ (m m': @mem A AEQ _)
                                       a v l l',
      possible_sync m m' ->
      incl l' l ->
      possible_sync (upd m a (v, l)) (upd m' a (v,l')).
  Proof.
    unfold possible_sync; intros.
    destruct (AEQ a a0); subst; autorewrite with upd;
      intuition eauto.
    specialize (H a0); intuition auto.
    right; repeat eexists; eauto.
    repeat deex.
    right; repeat eexists; eauto.
  Qed.

  Hint Resolve incl_refl.

  Lemma possible_sync_respects_sync_mem : forall A AEQ (m m': @mem A AEQ _),
      possible_sync m m' ->
      possible_sync (sync_mem m) (sync_mem m').
  Proof.
    unfold possible_sync, sync_mem; intros.
    specialize (H a).
    destruct matches; subst; intuition eauto;
      try congruence;
      repeat deex;
      right;
      cleanup.
    do 3 eexists; intuition eauto.
  Qed.

  Hint Resolve possible_sync_respects_upd.
  Hint Resolve possible_sync_respects_sync_mem.

  Theorem step_presync : forall T (m m' m'' m''': rawdisk) hm (p: prog T) hm' v,
      possible_sync (AEQ:=Nat.eq_dec) m m' ->
      step m' hm p m'' hm' v ->
      possible_sync (AEQ:=Nat.eq_dec) m'' m''' ->
      exists (m'2: rawdisk),
        step m hm p m'2 hm' v /\
        possible_sync (AEQ:=Nat.eq_dec) m'2 m'''.
  Proof.
    intros.
    inversion H0; subst; repeat sigT_eq; cleanup.
    - exists m; intuition eauto.
      specialize (H a); intuition auto; repeat deex; try congruence.
      assert (v = v0) by congruence; subst.
      eauto.
    - pose proof (H a); intuition auto; try congruence.
      repeat deex.
      cleanup.
      exists (upd m a (v0, v::l)).
      intuition eauto.
    - exists (sync_mem m).
      intuition eauto.
    - pose proof (H a); intuition auto; try congruence.
      repeat deex.
      cleanup.
      exists (upd m a vs').
      intuition eauto.
      eapply possible_sync_trans; eauto.
      destruct vs'.
      eapply possible_sync_respects_upd; eauto.
    - exists m; intuition eauto.
  Qed.
End StepPresync.

Inductive exec : forall T, rawdisk -> hashmap -> prog T -> outcome T -> Prop :=
| XRet : forall T m hm (v: T),
    exec m hm (Ret v) (Finished m hm v)
| XStep : forall T m hm (p: prog T) m' m'' hm' v,
    step m hm p m' hm' v ->
    possible_sync m' m'' ->
    exec m hm p (Finished m'' hm' v)
| XBindFinish : forall m hm T (p1: prog T) m' hm' (v: T)
                  T' (p2: T -> prog T') out,
    exec m hm p1 (Finished m' hm' v) ->
    exec m' hm' (p2 v) out ->
    exec m hm (Bind p1 p2) out
| XBindFail : forall m hm T (p1: prog T)
                T' (p2: T -> prog T'),
    exec m hm p1 (Failed T) ->
    (* note p2 need not execute at all if p1 fails, a form of lazy
    evaluation *)
    exec m hm (Bind p1 p2) (Failed T')
| XBindCrash : forall m hm T (p1: prog T) m' hm'
                 T' (p2: T -> prog T'),
    exec m hm p1 (Crashed T m' hm') ->
    exec m hm (Bind p1 p2) (Crashed T' m' hm')
| XFail : forall m hm T (p: prog T),
    fail_step m p ->
    exec m hm p (Failed T)
| XCrash : forall m hm T (p: prog T),
    crash_step p ->
    exec m hm p (Crashed T m hm).

(** program with recovery *)
Inductive recover_outcome (TF TR: Type) :=
  | RFailed
  | RFinished (m: rawdisk) (hm: hashmap) (v: TF)
  | RRecovered (m: rawdisk) (hm: hashmap) (v: TR).

Inductive exec_recover (TF TR: Type)
    : rawdisk -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m hm p1 p2, exec m hm p1 (Failed TF)
    -> exec_recover m hm p1 p2 (RFailed TF TR)
  | XRFinished : forall m hm p1 p2 m' hm' (v: TF), exec m hm p1 (Finished m' hm' v)
    -> exec_recover m hm p1 p2 (RFinished TR m' hm' v)
  | XRCrashedFailed : forall m hm p1 p2 m' hm' m'r, exec m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r hm' p2 p2 (RFailed TR TR)
    -> exec_recover m hm p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR), exec m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r hm' p2 p2 (RFinished TR m'' hm'' v)
    -> exec_recover m hm p1 p2 (RRecovered TF m'' hm'' v)
  | XRCrashedRecovered : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR), exec m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r hm' p2 p2 (RRecovered TR m'' hm'' v)
    -> exec_recover m hm p1 p2 (RRecovered TF m'' hm'' v).

Hint Constructors exec.
Hint Constructors step.
Hint Constructors exec_recover.

(** program notations *)

Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).
Notation "^( a )" := (pair a tt).
Notation "^( a , .. , b )" := (pair a .. (pair b tt) .. ).

Notation "p1 ;; p2" := (Bind p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2)) (at level 60, right associativity,
                                                 format "'[v' x  <-  p1 ; '/' p2 ']'").
Notation "'let^' ( a ) <- p1 ; p2" :=
  (Bind p1
    (pair_args_helper (fun a (_:unit) => p2))
  )
  (at level 60, right associativity, a ident,
   format "'[v' let^ ( a )  <-  p1 ; '/' p2 ']'").

Notation "'let^' ( a , .. , b ) <- p1 ; p2" :=
  (Bind p1
    (pair_args_helper (fun a => ..
      (pair_args_helper (fun b (_:unit) => p2))
    ..))
  )
    (at level 60, right associativity, a closed binder, b closed binder,
     format "'[v' let^ ( a , .. , b )  <-  p1 ; '/' p2 ']'").