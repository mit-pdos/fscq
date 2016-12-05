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
    fail_step m (Write a v)
| FailTrim : forall m a,
    m a = None ->
    fail_step m (Trim a).

Inductive crash_step : forall T, prog T -> Prop :=
| CrashRead : forall a,
    crash_step (Read a)
| CrashWrite : forall a v,
    crash_step (Write a v).

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