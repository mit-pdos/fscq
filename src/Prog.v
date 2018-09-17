Require Import Mem.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.
Require Import Word.
Require Import PredCrash Blockmem.
Require Export AsyncDisk.
Import ListNotations.
Set Implicit Arguments.

Parameter perm : Type.
Parameter perm_dec : forall (p p': perm), {p = p'}+{p <> p'}.
Parameter can_access: perm -> tag -> Prop.
Axiom can_access_public: forall pr, can_access pr Public.
Hint Resolve can_access_public.

Hint Extern 0 (EqDec handle) => unfold EqDec; apply handle_eq_dec.

Inductive op :=
| Chd : tag -> tag -> op
| Uns : tag -> op.

Definition op_dec : forall (o o': op), {o = o'}+{o <> o'}.
  intros.
  destruct o, o'; auto; try (solve [right; congruence] ||
  solve [destruct (tag_dec t t0); subst; auto; right; congruence] ||
  solve [destruct (tag_dec t t1); destruct (tag_dec t0 t2); subst; auto; right; congruence]).
Defined.

Definition trace := list op.

Definition domainmem:= @Mem.mem addr addr_eq_dec tag.
Definition taggeddisk:= rawdisk.
Definition taggedmem:= @Mem.mem handle handle_eq_dec tagged_block.

Notation "'tagged_disk'" := taggeddisk.

Inductive result {T: Type} : Type :=
| Finished : taggeddisk -> taggedmem -> domainmem -> T -> result
| Crashed : taggeddisk -> taggedmem -> domainmem -> result
| Failed : result.

Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : addr -> block -> prog handle
| Unseal : handle -> prog block
| Sync : prog unit
| Auth : tag -> prog bool
| ChDom : addr -> tag -> prog unit
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

Fixpoint domainmem0 size : domainmem :=
  match size with
  | O => empty_mem
  | S n => upd (domainmem0 n) n Public
  end.

Definition vsmerge {T} (vs: T * list T) := fst vs :: snd vs.

Definition sync_mem AT AEQ V (m : @mem AT AEQ (V * list V)) : @mem AT AEQ (V * list V) :=
  fun a => match m a with
    | None => None
    | Some (v, _) => Some (v, nil)
    end.

Definition last_upd AT AEQ V (m : @mem AT AEQ (V * list V)) (v : V) (a: AT) :=
  match m a with
  | None => m
  | Some vs => (upd m a (v, snd vs))
  end.

Inductive exec:
  forall T, perm -> taggeddisk -> taggedmem -> domainmem -> prog T -> @result T -> trace -> Prop :=
| ExecRead    : forall pr d bm dm a i bs,
                  bm i = None ->
                  d a = Some bs ->
                  exec pr d bm dm (Read a) (Finished d (upd bm i (fst bs)) dm i) nil
                       
| ExecWrite   : forall pr d bm dm a i b bs,
                  bm i = Some b ->
                  d a = Some bs ->
                  exec pr d bm dm (Write a i) (Finished (upd d a (b, vsmerge bs)) bm dm tt) nil
                       
| ExecSeal : forall pr d bm dm i t b,
               bm i = None ->
               dm t <> None ->
               exec pr d bm dm (Seal t b) (Finished d (upd bm i (t,b)) dm i) nil
                    
| ExecUnseal : forall pr d bm dm i b t,
                 bm i = Some b ->
                 dm (fst b) = Some t ->
                 exec pr d bm dm (Unseal i) (Finished d bm dm (snd b)) [Uns t]
                      
| ExecSync : forall pr d bm dm,
               exec pr d bm dm (Sync) (Finished (sync_mem d) bm dm tt) nil

| ExecAuthSucc : forall pr d bm dm t,
               can_access pr t ->
               exec pr d bm dm (Auth t) (Finished d bm dm true) nil

| ExecAuthFail : forall pr d bm dm t,
               ~can_access pr t ->
               exec pr d bm dm (Auth t) (Finished d bm dm false) nil

| ExecChDom : forall pr d bm dm t t' a,
               dm a = Some t' ->
               exec pr d bm dm (ChDom a t) (Finished d bm (upd dm a t) tt) [Chd t' t]
                    
| ExecRet : forall T pr d bm dm (r: T),
              exec pr d bm dm (Ret r) (Finished d bm dm r) nil
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm dm d' bm' dm' v r t1 t2,
               exec pr d bm dm p1 (Finished d' bm' dm' v) t1 ->
               exec pr d' bm' dm' (p2 v) r t2 ->
               exec pr d bm dm (Bind p1 p2) r (t2++t1)
                      
| CrashRead : forall pr d bm dm a,
                exec pr d bm dm (Read a) (Crashed d bm dm) nil
                        
| CrashWrite : forall pr d bm dm a i,
                 exec pr d bm dm (Write a i) (Crashed d bm dm) nil
                       
| CrashSync : forall pr d bm dm,
                exec pr d bm dm (Sync) (Crashed d bm dm) nil

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' dm dm' tr,
                exec pr d bm dm p1 (@Crashed T d' bm' dm') tr ->
                exec pr d bm dm (Bind p1 p2) (@Crashed T' d' bm' dm') tr

| FailRead    : forall pr d bm dm a,
                  d a = None ->
                  exec pr d bm dm (Read a) Failed nil

| FailWrite    : forall pr d bm dm a i,
                  bm i = None \/ d a = None ->
                  exec pr d bm dm (Write a i) Failed nil
                    
| FailUnseal : forall pr d bm dm i,
                 bm i = None \/ (exists b, bm i = Some b /\ dm (fst b) = None) ->
                 exec pr d bm dm (Unseal i) Failed nil

| FailChDom : forall pr d bm dm t a,
               dm a = None ->
               exec pr d bm dm (ChDom a t) Failed nil

| FailBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm dm tr',
                exec pr d bm dm p1 (@Failed T) tr' ->
                exec pr d bm dm (Bind p1 p2) (@Failed T') tr'.

Inductive recover_outcome (TF TR: Type) :=
 | RFinished : taggeddisk -> taggedmem -> domainmem -> TF -> recover_outcome TF TR
 | RRecovered : taggeddisk -> taggedmem -> domainmem -> TR -> recover_outcome TF TR
 | RFailed : recover_outcome TF TR.

Inductive exec_recover (TF TR: Type):
  perm -> taggeddisk -> taggedmem -> domainmem -> prog TF -> prog TR -> recover_outcome TF TR -> trace -> Prop :=
| XRFinished : forall pr tr' d dm bm p1 p2 d' dm' bm' (v: TF),
       exec pr d bm dm p1 (Finished d' bm' dm' v) tr'
       -> exec_recover pr d bm dm p1 p2 (RFinished TR d' bm' dm' v) tr'
| XRFailed : forall pr tr' d dm bm p1 p2,
       exec pr d bm dm p1 (@Failed TF) tr'
    -> exec_recover pr d bm dm p1 p2 (RFailed TF TR) tr'
| XRCrashedFinished : forall pr tr' tr'' d dm bm bm' dm' p1 p2 d' d'r d'' dm'' bm'' (v: TR),
    exec pr d bm dm p1 (@Crashed TF d' bm' dm') tr'
    -> possible_crash d' d'r
    -> @exec_recover TR TR pr d'r empty_mem dm' p2 p2 (RFinished TR d'' bm'' dm'' v) tr''
    -> exec_recover pr d bm dm p1 p2 (RRecovered TF d'' bm'' dm'' v) (tr''++tr')
| XRCrashedRecovered :  forall pr tr' tr'' d dm bm bm' dm' p1 p2 d' d'r d'' dm'' bm'' (v: TR),
    exec pr d bm dm p1 (@Crashed TF d' bm' dm') tr'
    -> possible_crash d' d'r
    -> @exec_recover TR TR pr d'r empty_mem dm' p2 p2 (RRecovered TR d'' bm'' dm'' v) tr''
    -> exec_recover pr d bm dm p1 p2 (RRecovered TF d'' bm'' dm'' v) (tr''++tr').


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
