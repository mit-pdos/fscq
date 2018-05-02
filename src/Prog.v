Require Import Mem.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.
Require Import Word.
Require Import PredCrash.
Require Export AsyncDisk.
Import ListNotations.
Set Implicit Arguments.

Parameter perm : Type.
Parameter perm_dec : forall (p p': perm), {p = p'}+{p <> p'}.
Parameter handle : Type.
Parameter dummy_handle : handle.
Parameter handle_eq_dec : forall (x y : handle), {x=y}+{x<>y}.
Parameter can_access: perm -> tag -> Prop.
Axiom can_access_public: forall pr, can_access pr Public.
Hint Resolve can_access_public.


Inductive op :=
| Sea : tag -> op
| Uns : tag -> op.

Definition op_dec : forall (o o': op), {o = o'}+{o <> o'}.
  intros.
  destruct o, o'; auto; try (solve [right; congruence] ||
  solve [destruct (tag_dec t t0); subst; auto; right; congruence]).
Defined.

Definition trace := list op.
Definition tagged_disk:= rawdisk.
Definition block_mem:= @Mem.mem handle handle_eq_dec tagged_block.

(* Axiom finite_map : forall A AEQ V (m : @mem A AEQ V), exists a, m a = None. *)


Inductive result {T: Type} : Type :=
| Finished : tagged_disk -> block_mem -> hashmap -> T -> result
| Crashed : tagged_disk -> block_mem -> hashmap -> result
| Failed : tagged_disk -> block_mem -> hashmap -> result.

Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : tag -> block -> prog handle
| Unseal : handle -> prog block
| Sync : prog unit
| Auth : tag -> prog bool
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.


Inductive exec:
  forall T, perm -> tagged_disk ->
       block_mem -> hashmap -> prog T ->  @result T -> trace -> Prop :=
| ExecRead    : forall pr d bm hm a i tb tbs,
                  bm i = None ->
                  d a = Some (tb, tbs) ->
                  exec pr d bm hm (Read a) (Finished d (upd bm i tb) hm i) nil                 
| ExecWrite   : forall pr d bm hm a i tb tbs,
                  bm i = Some tb ->
                  d a = Some tbs ->
                  exec pr d bm hm (Write a i) (Finished (upd d a (tb, vsmerge tbs)) bm hm tt) nil
                       
| ExecSeal : forall pr d bm hm i t b,
               bm i = None ->
               exec pr d bm hm (Seal t b) (Finished d (upd bm i (t, b)) hm i) [Sea t]
                    
| ExecUnseal : forall pr d bm hm i tb,
                 bm i = Some tb ->
                 exec pr d bm hm (Unseal i) (Finished d bm hm (snd tb)) [Uns (fst tb)]
                      
| ExecSync : forall pr d bm hm,
               exec pr d bm hm (Sync) (Finished (sync_mem d) bm hm tt) nil

| ExecAuthSucc : forall pr d bm hm t,
               can_access pr t ->
               exec pr d bm hm (Auth t) (Finished d bm hm true) nil

| ExecAuthFail : forall pr d bm hm t,
               ~can_access pr t ->
               exec pr d bm hm (Auth t) (Finished d bm hm false) nil
                    
| ExecRet : forall T pr d bm hm (r: T),
              exec pr d bm hm (Ret r) (Finished d bm hm r) nil
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm hm d' bm' hm' v r tr' tr'',
               exec pr d bm hm p1 (Finished d' bm' hm' v) tr' ->
               exec pr d' bm' hm' (p2 v) r tr'' ->
               exec pr d bm hm (Bind p1 p2) r (tr''++tr')
                      
| CrashRead : forall pr d bm hm a,
                exec pr d bm hm (Read a) (Crashed d bm hm) nil
                        
| CrashWrite : forall pr d bm hm a i,
                 exec pr d bm hm (Write a i) (Crashed d bm hm) nil
                       
| CrashSync : forall pr d bm hm,
                exec pr d bm hm (Sync) (Crashed d bm hm) nil

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' hm hm' tr',
                exec pr d bm hm p1 (@Crashed T d' bm' hm') tr' ->
                exec pr d bm hm (Bind p1 p2) (@Crashed T' d' bm' hm') tr'
                     
| FailRead    : forall pr d bm hm a,
                  d a = None ->
                  exec pr d bm hm (Read a) (Failed d bm hm) nil

| FailWrite    : forall pr d bm hm a i,
                  bm i = None \/ d a = None ->
                  exec pr d bm hm (Write a i) (Failed d bm hm) nil
                    
| FailUnseal : forall pr d bm hm i,
                 bm i = None ->
                 exec pr d bm hm (Unseal i) (Failed d bm hm) nil

| FailBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' hm hm' tr',
                exec pr d bm hm p1 (@Failed T d' bm' hm') tr' ->
                exec pr d bm hm (Bind p1 p2) (@Failed T' d' bm' hm') tr'.




Inductive recover_outcome (TF TR: Type) :=
  | RFinished (m: tagged_disk) (bm: block_mem) (hm: hashmap) (v: TF)
  | RRecovered (m: tagged_disk) (bm: block_mem) (hm: hashmap) (v: TR)
  | RFailed (m: tagged_disk) (bm: block_mem) (hm: hashmap).

Inductive exec_recover (TF TR: Type)
    : perm ->  tagged_disk -> block_mem -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> trace -> Prop :=
| XRFinished : forall pr tr' m bm hm p1 p2 m' bm' hm' (v: TF),
       exec pr m bm hm p1 (Finished m' bm' hm' v) tr'
       -> exec_recover pr m bm hm p1 p2 (RFinished TR m' bm' hm' v) tr'
| XRFailed : forall pr tr' m bm hm p1 p2 m' bm' hm',
       exec pr m bm hm p1 (Failed m' bm' hm') tr'
    -> exec_recover pr m bm hm p1 p2 (RFailed TF TR m' bm' hm') tr'
| XRCrashedFinished : forall pr tr' tr'' m bm hm p1 p2 m' bm' hm' m'r m'' bm'' hm'' (v: TR),
       exec pr m bm hm p1 (Crashed m' bm' hm') tr'
    -> possible_crash m' m'r
    -> @exec_recover TR TR pr m'r bm' hm' p2 p2 (RFinished TR m'' bm'' hm'' v) tr''
    -> exec_recover pr m bm hm p1 p2 (RRecovered TF m'' bm'' hm'' v) (tr''++tr')
| XRCrashedRecovered : forall pr tr' tr'' m bm hm p1 p2 m' bm' hm' m'r m'' bm'' hm'' (v: TR),
       exec pr m bm hm p1 (Crashed m' bm' hm') tr'
    -> possible_crash m' m'r
    -> @exec_recover TR TR pr m'r bm' hm' p2 p2 (RRecovered TR m'' bm'' hm'' v) tr''
    -> exec_recover pr m bm hm p1 p2 (RRecovered TF m'' bm'' hm'' v) (tr''++tr').


Notation "p1 :; p2" := (Bind p1 (fun _: unit => p2))
                              (at level 60, right associativity).
Notation "x <- p1 ;; p2" := (Bind p1 (fun x => p2))
                             (at level 60, right associativity).


Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).
Notation "^( a )" := (pair a tt).
Notation "^( a , .. , b )" := (pair a .. (pair b tt) .. ).


Notation "'let^' ( a ) <- p1 ;; p2" :=
  (Bind p1
    (pair_args_helper (fun a (_:unit) => p2))
  )
  (at level 60, right associativity, a ident,
   format "'[v' let^ ( a )  <-  p1 ;; '/' p2 ']'").

Notation "'let^' ( a , .. , b ) <- p1 ;; p2" :=
  (Bind p1
    (pair_args_helper (fun a => ..
      (pair_args_helper (fun b (_:unit) => p2))
    ..))
  )
    (at level 60, right associativity, a closed binder, b closed binder,
     format "'[v' let^ ( a , .. , b )  <-  p1 ;; '/' p2 ']'").
