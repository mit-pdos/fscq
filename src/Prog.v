Require Import FunctionalExtensionality.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import List.
Require Import Mem.
Require Import PredCrash.
Require Import AsyncDisk.
Require Import Word.

Import ListNotations.

Set Implicit Arguments.

(** * The programming language *)

Parameter vartype : Type.
Parameter vartype_eq_dec : forall (x y : vartype), {x=y}+{x<>y}.

Inductive var_value : Type :=
  | Any : forall (T : Type), T -> var_value.

(** single program *)
Inductive prog : Type -> Type :=
  | Ret T (v: T) : prog T
  | Read (a: addr) : prog valu
  | Write (a: addr) (v: valu) : prog unit
  | Sync : prog unit
  | Trim (a: addr) : prog unit
  | VarAlloc (T : Type) (v : T) : prog vartype
  | VarDelete (i : vartype) : prog unit
  | VarGet (i : vartype) (T : Type) : prog T
  | VarSet (i : vartype) (T : Type) (v : T) : prog unit
  | Hash (sz: nat) (buf: word sz) : prog (word hashlen)
  | Bind T T' (p1: prog T) (p2: T -> prog T') : prog T'.

Arguments Ret {T} v.
Arguments VarAlloc {T} v.
Arguments VarGet i {T}.
Arguments VarSet i {T} v.

Definition varmem := @mem vartype vartype_eq_dec var_value.

Inductive outcome (T : Type) :=
  | Failed
  | Finished (m: rawdisk) (v: varmem) (hm: hashmap) (v: T)
  | Crashed (m: rawdisk) (hm: hashmap).

Inductive step : forall T,
    rawdisk -> varmem -> hashmap -> prog T ->
    rawdisk -> varmem -> hashmap -> T -> Prop :=
| StepRead : forall m a v x vm hm,
    m a = Some (v, x) ->
    step m vm hm (Read a) m vm hm v
| StepWrite : forall m a v v0 x vm hm,
    m a = Some (v0, x) ->
    step m vm hm (Write a v) (upd m a (v, v0 :: x)) vm hm tt
| StepSync : forall m vm hm,
    step m vm hm (Sync) (sync_mem m) vm hm tt
| StepTrim : forall m a vs vs' vm hm,
    m a = Some vs ->
    step m vm hm (Trim a) (upd m a vs') vm hm tt
| StepHash : forall m sz (buf : word sz) h vm hm,
    hash_safe hm h buf ->
    hash_fwd buf = h ->
    step m vm hm (Hash buf) m vm (upd_hashmap' hm h buf) h
| StepVarAlloc : forall T d v vm i hm,
    vm i = None ->
    step d vm hm (@VarAlloc T v) d (insert vm i (@Any T v)) hm i
| StepVarDelete : forall d v vm i hm,
    vm i = Some v ->
    step d vm hm (VarDelete i) d (delete vm i) hm tt
| StepVarGet : forall T d v vm i hm,
    vm i = Some (@Any T v) ->
    step d vm hm (@VarGet i T) d vm hm v
| StepVarSet : forall T d v0 v vm i hm,
    vm i = Some v0 ->
    step d vm hm (@VarSet i T v) d (upd vm i (@Any T v)) hm tt.

Inductive fail_step : forall T,
    rawdisk -> varmem -> prog T -> Prop :=
| FailRead : forall m vm a,
    m a = None ->
    fail_step m vm (Read a)
| FailWrite : forall m vm a v,
    m a = None ->
    fail_step m vm (Write a v)
| FailTrim : forall m vm a,
    m a = None ->
    fail_step m vm (Trim a)
| FailVarDelete : forall m vm i,
    vm i = None ->
    fail_step m vm (VarDelete i)
| FailVarGetType : forall T T' m vm i (v : T'),
    T <> T' ->
    vm i = Some (Any v) ->
    fail_step m vm (@VarGet i T)
| FailVarGetNone : forall T m vm i,
    vm i = None ->
    fail_step m vm (@VarGet i T)
| FailVarSetNone : forall T m vm i (v : T),
    vm i = None ->
    fail_step m vm (VarSet i v).

Inductive crash_step : forall T, prog T -> Prop :=
| CrashRead : forall a,
    crash_step (Read a)
| CrashWrite : forall a v,
    crash_step (Write a v).

Inductive exec : forall T, rawdisk -> varmem -> hashmap -> prog T -> outcome T -> Prop :=
| XRet : forall T m vm hm (v: T),
    exec m vm hm (Ret v) (Finished m vm hm v)
| XStep : forall T m vm hm (p: prog T) m' m'' vm' hm' v,
    step m vm hm p m' vm' hm' v ->
    possible_sync m' m'' ->
    exec m vm hm p (Finished m'' vm' hm' v)
| XBindFinish : forall m vm hm T (p1: prog T) m' vm' hm' (v: T)
                  T' (p2: T -> prog T') out,
    exec m vm hm p1 (Finished m' vm' hm' v) ->
    exec m' vm' hm' (p2 v) out ->
    exec m vm hm (Bind p1 p2) out
| XBindFail : forall m vm hm T (p1: prog T)
                T' (p2: T -> prog T'),
    exec m vm hm p1 (Failed T) ->
    exec m vm hm (Bind p1 p2) (Failed T')
| XBindCrash : forall m vm hm T (p1: prog T) m' hm'
                 T' (p2: T -> prog T'),
    exec m vm hm p1 (Crashed T m' hm') ->
    exec m vm hm (Bind p1 p2) (Crashed T' m' hm')
| XFail : forall m vm hm T (p: prog T),
    fail_step m vm p ->
    exec m vm hm p (Failed T)
| XCrash : forall m vm hm T (p: prog T),
    crash_step p ->
    exec m vm hm p (Crashed T m hm).

(** program with recovery *)
Inductive recover_outcome (TF TR: Type) :=
  | RFailed
  | RFinished (m: rawdisk) (vm: varmem) (hm: hashmap) (v: TF)
  | RRecovered (m: rawdisk) (vm: varmem) (hm: hashmap) (v: TR).

Inductive exec_recover (TF TR: Type)
    : rawdisk -> varmem -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m vm hm p1 p2, exec m vm hm p1 (Failed TF)
    -> exec_recover m vm hm p1 p2 (RFailed TF TR)
  | XRFinished : forall m vm hm p1 p2 m' vm' hm' (v: TF), exec m vm hm p1 (Finished m' vm' hm' v)
    -> exec_recover m vm hm p1 p2 (RFinished TR m' vm' hm' v)
  | XRCrashedFailed : forall m vm hm p1 p2 m' hm' m'r, exec m vm hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r empty_mem hm' p2 p2 (RFailed TR TR)
    -> exec_recover m vm hm p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m vm hm p1 p2 m' hm' m'r m'' vm'' hm'' (v: TR), exec m vm hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r empty_mem hm' p2 p2 (RFinished TR m'' vm'' hm'' v)
    -> exec_recover m vm hm p1 p2 (RRecovered TF m'' vm'' hm'' v)
  | XRCrashedRecovered : forall m vm hm p1 p2 m' hm' m'r m'' vm'' hm'' (v: TR), exec m vm hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r empty_mem hm' p2 p2 (RRecovered TR m'' vm'' hm'' v)
    -> exec_recover m vm hm p1 p2 (RRecovered TF m'' vm'' hm'' v).

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
