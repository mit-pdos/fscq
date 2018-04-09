Require Import Mem.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.
Require Import Word.
Require Import PermPredCrash.
Require Export PermAsyncDisk.
Import ListNotations.
Set Implicit Arguments.

Definition perm := option nat. (* None can only read public blocks *)
Parameter handle : Type.
Parameter dummy_handle : handle.


Definition perm_dec : forall (p p': perm), {p = p'}+{p <> p'}.
  intros; destruct p, p'; try (solve [left; auto] || solve [right; congruence]).
  destruct (Nat.eq_dec n n0); subst; auto; right; congruence.
Defined.

Inductive op :=
| Sea : tag -> op
| Uns : tag -> op.

Definition op_dec : forall (o o': op), {o = o'}+{o <> o'}.
  intros.
  destruct o, o'; auto; try (solve [right; congruence] ||
  solve [destruct (tag_dec t t0); subst; auto; right; congruence]).
Defined.

Definition trace := list op.
Parameter handle_eq_dec : forall (x y : handle), {x=y}+{x<>y}.
Definition tagged_disk:= rawdisk.
Definition block_mem:= @Mem.mem handle handle_eq_dec tagged_block.

(* Axiom finite_map : forall A AEQ V (m : @mem A AEQ V), exists a, m a = None. *)
Axiom can_access: perm -> tag -> Prop.
Axiom can_access_public: forall pr, can_access pr Public.
Hint Resolve can_access_public.

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
| Hash (sz: nat) (buf: word sz) : prog (word hashlen)
| Hash2 (sz1 sz2: nat) (buf1 : word sz1) (buf2 : word sz2) : prog (word hashlen)
| Auth : tag -> prog bool
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.


Inductive exec:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> hashmap -> prog T ->  @result T -> trace -> Prop :=
| ExecRead    : forall pr d bm hm a i tb tbs tr,
                  bm i = None ->
                  d a = Some (tb, tbs) ->
                  exec pr tr d bm hm (Read a) (Finished d (upd bm i tb) hm i) tr                 
| ExecWrite   : forall pr d bm hm a i tb tbs tr,
                  bm i = Some tb ->
                  d a = Some tbs ->
                  exec pr tr d bm hm (Write a i) (Finished (upd d a (tb, vsmerge tbs)) bm hm tt) tr
                       
| ExecSeal : forall pr d bm hm i t b tr,
               bm i = None ->
               exec pr tr d bm hm (Seal t b) (Finished d (upd bm i (t, b)) hm i) (Sea t::tr)
                    
| ExecUnseal : forall pr d bm hm i tb tr,
                 bm i = Some tb ->
                 exec pr tr d bm hm (Unseal i) (Finished d bm hm (snd tb)) (Uns (fst tb)::tr)
                      
| ExecSync : forall pr d bm hm tr,
               exec pr tr d bm hm (Sync) (Finished (sync_mem d) bm hm tt) tr

| ExecAuthSucc : forall pr d bm hm tr t,
               can_access pr t ->
               exec pr tr d bm hm (Auth t) (Finished d bm hm true) tr

| ExecAuthFail : forall pr d bm hm tr t,
               ~can_access pr t ->
               exec pr tr d bm hm (Auth t) (Finished d bm hm false) tr

| StepHash : forall pr d bm hm tr sz (buf : word sz) h,
               hash_safe hm h buf ->
               hash_fwd buf = h ->
               exec pr tr d bm hm (Hash buf) (Finished d bm (upd_hashmap' hm h buf) h) tr
         
| StepHash2 : forall pr d bm hm tr sz1 sz2 (buf1 : word sz1)
                (buf2 : word sz2) (buf : word (sz1 + sz2)) h,
                buf = Word.combine buf1 buf2 ->
                hash_safe hm h buf ->
                hash_fwd buf = h ->
                exec pr tr d bm hm (Hash2 buf1 buf2) (Finished d bm (upd_hashmap' hm h buf) h) tr
                    
| ExecRet : forall T pr d bm hm (r: T) tr,
              exec pr tr d bm hm (Ret r) (Finished d bm hm r) tr
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm hm d' bm' hm' v r tr tr' tr'',
               exec pr tr d bm hm p1 (Finished d' bm' hm' v) tr' ->
               exec pr tr' d' bm' hm' (p2 v) r tr'' ->
               exec pr tr d bm hm (Bind p1 p2) r tr''
                      
| CrashRead : forall pr d bm hm a tr,
                exec pr tr d bm hm (Read a) (Crashed d bm hm) tr
                        
| CrashWrite : forall pr d bm hm a i tr,
                 exec pr tr d bm hm (Write a i) (Crashed d bm hm) tr
                       
| CrashSync : forall pr d bm hm tr,
                exec pr tr d bm hm (Sync) (Crashed d bm hm) tr

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' hm hm' tr tr',
                exec pr tr d bm hm p1 (@Crashed T d' bm' hm') tr' ->
                exec pr tr d bm hm (Bind p1 p2) (@Crashed T' d' bm' hm') tr'
                     
| FailRead    : forall pr d bm hm a tr,
                  d a = None ->
                  exec pr tr d bm hm (Read a) (Failed d bm hm) tr

| FailWrite    : forall pr d bm hm a i tr,
                  bm i = None \/ d a = None ->
                  exec pr tr d bm hm (Write a i) (Failed d bm hm) tr
                    
| FailUnseal : forall pr d bm hm i tr,
                 bm i = None ->
                 exec pr tr d bm hm (Unseal i) (Failed d bm hm) tr

| FailBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' hm hm' tr tr',
                exec pr tr d bm hm p1 (@Failed T d' bm' hm') tr' ->
                exec pr tr d bm hm (Bind p1 p2) (@Failed T' d' bm' hm') tr'.




Inductive recover_outcome (TF TR: Type) :=
  | RFinished (m: tagged_disk) (bm: block_mem) (hm: hashmap) (v: TF)
  | RRecovered (m: tagged_disk) (bm: block_mem) (hm: hashmap) (v: TR).

Inductive exec_recover (TF TR: Type)
    : perm -> trace -> tagged_disk -> block_mem -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> trace -> Prop :=
| XRFinished : forall pr tr tr' m bm hm p1 p2 m' bm' hm' (v: TF),
       exec pr tr m bm hm p1 (Finished m' bm' hm' v) tr'
    -> exec_recover pr tr m bm hm p1 p2 (RFinished TR m' bm' hm' v) tr'
| XRCrashedFinished : forall pr tr tr' tr'' m bm hm p1 p2 m' bm' hm' m'r m'' bm'' hm'' (v: TR),
       exec pr tr m bm hm p1 (Crashed m' bm' hm') tr'
    -> possible_crash m' m'r
    -> @exec_recover TR TR pr tr' m'r bm' hm' p2 p2 (RFinished TR m'' bm'' hm'' v) tr''
    -> exec_recover pr tr m bm hm p1 p2 (RRecovered TF m'' bm'' hm'' v) tr''
| XRCrashedRecovered : forall pr tr tr' tr'' m bm hm p1 p2 m' bm' hm' m'r m'' bm'' hm'' (v: TR),
       exec pr tr m bm hm p1 (Crashed m' bm' hm') tr'
    -> possible_crash m' m'r
    -> @exec_recover TR TR pr tr' m'r bm' hm' p2 p2 (RRecovered TR m'' bm'' hm'' v) tr''
    -> exec_recover pr tr m bm hm p1 p2 (RRecovered TF m'' bm'' hm'' v) tr''.


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
