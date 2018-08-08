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
Definition blockset:= (block * list block)%type.
Definition blockdisk:= @Mem.mem addr addr_eq_dec blockset.
Definition blockmem:= @Mem.mem handle handle_eq_dec block.

Definition tagset:= (tag * list tag)%type.
Definition tagdisk:= @Mem.mem addr addr_eq_dec tagset.
Definition tagmem:= @Mem.mem handle handle_eq_dec tag.

Definition taggeddisk:= rawdisk.
Definition taggedmem:= @Mem.mem handle handle_eq_dec tagged_block.

Definition diskmatch {AT AEQ V1 V2} (td : @Mem.mem AT AEQ (V1 * list V1))
                                    (bd: @Mem.mem AT AEQ (V2 * list V2)):=
  forall a, (td a = None /\ bd a = None)
     \/ (exists ts bs, td a = Some ts /\ bd a = Some bs /\ length (snd ts) = length (snd bs)).

Definition memmatch {AT AEQ V1 V2} (tm : @Mem.mem AT AEQ V1)
                                    (bm: @Mem.mem AT AEQ V2):=
  forall h, tm h = None <-> bm h = None.

Definition disk_merges_to {AT AEQ V1 V2} (td : @Mem.mem AT AEQ (V1 * list V1))
                                    (bd: @Mem.mem AT AEQ (V2 * list V2)) tgd :=
  diskmatch td bd
  /\ (forall a ts bs,
        td a = Some ts /\ bd a = Some bs <->
    (tgd a = Some ((fst ts, fst bs), List.combine (snd ts) (snd bs)) /\ length (snd ts) = length (snd bs))).

Definition mem_merges_to {AT AEQ V1 V2} (tm : @Mem.mem AT AEQ V1)
                                    (bm: @Mem.mem AT AEQ V2) tgm :=
  memmatch tm bm
  /\ (forall h t b,
        tm h = Some t /\ bm h = Some b <->
        tgm h = Some (t, b)).


Inductive result {T: Type} : Type :=
| Finished : blockdisk -> tagdisk -> blockmem -> tagmem -> T -> result
| Crashed : blockdisk -> tagdisk -> blockmem -> tagmem -> result
| Failed : blockdisk -> result.

Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : tag -> block -> prog handle
| Unseal : handle -> prog block
| Sync : prog unit
| Auth : tag -> prog bool
| Chtag : tag -> addr -> prog unit
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

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
  forall T, perm -> blockdisk -> tagdisk ->
       blockmem -> tagmem -> prog T ->  @result T -> trace -> Prop :=
| ExecRead    : forall pr d dt bm bt a i bs ts,
                  bm i = None ->
                  bt i = None ->
                  d a = Some bs ->
                  dt a = Some ts ->
                  exec pr d dt bm bt (Read a) (Finished d dt (upd bm i (fst bs)) (upd bt i (fst ts)) i) nil
                       
| ExecWrite   : forall pr d dt bm bt a i b bs t ts,
                  bm i = Some b ->
                  bt i = Some t ->
                  d a = Some bs ->
                  dt a = Some ts ->
                  exec pr d dt bm bt (Write a i) (Finished (upd d a (b, vsmerge bs)) (upd dt a (t, vsmerge ts)) bm bt tt) nil
                       
| ExecSeal : forall pr d dt bm bt i t b,
               bm i = None ->
               bt i = None ->
               exec pr d dt bm bt (Seal t b) (Finished d dt (upd bm i b) (upd bt i t) i) nil
                    
| ExecUnseal : forall pr d dt bm bt i b t,
                 bm i = Some b ->
                 bt i = Some t ->
                 exec pr d dt bm bt (Unseal i) (Finished d dt bm bt b) [Uns t]
                      
| ExecSync : forall pr d dt bm bt,
               exec pr d dt bm bt (Sync) (Finished (sync_mem d) (sync_mem dt) bm bt tt) nil

| ExecAuthSucc : forall pr d dt bm bt t,
               can_access pr t ->
               exec pr d dt bm bt (Auth t) (Finished d dt bm bt true) nil

| ExecAuthFail : forall pr d dt bm bt t,
               ~can_access pr t ->
               exec pr d dt bm bt (Auth t) (Finished d dt bm bt false) nil

| ExecChtag : forall pr d dt bm bt t a,
               exec pr d dt bm bt (Chtag t a) (Finished d (last_upd dt t a) bm bt tt) nil
                    
| ExecRet : forall T pr d dt bm bt (r: T),
              exec pr d dt bm bt (Ret r) (Finished d dt bm bt r) nil
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d dt bm bt d' dt' bm' bt' v r t1 t2,
               exec pr d dt bm bt p1 (Finished d' dt' bm' bt' v) t1 ->
               exec pr d' dt' bm' bt' (p2 v) r t2 ->
               exec pr d dt bm bt (Bind p1 p2) r (t2++t1)
                      
| CrashRead : forall pr d dt bm bt a,
                exec pr d dt bm bt (Read a) (Crashed d dt bm bt) nil
                        
| CrashWrite : forall pr d dt bm bt a i,
                 exec pr d dt bm bt (Write a i) (Crashed d dt bm bt) nil
                       
| CrashSync : forall pr d dt bm bt,
                exec pr d dt bm bt (Sync) (Crashed d dt bm bt) nil

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d dt d' dt' bm bm' bt bt' tr,
                exec pr d dt bm bt p1 (@Crashed T d' dt' bm' bt') tr ->
                exec pr d dt bm bt (Bind p1 p2) (@Crashed T' d' dt' bm' bt') tr

| FailRead    : forall pr d bm dt bt a,
                  d a = None ->
                  exec pr d dt bm bt (Read a) (Failed d) nil

| FailWrite    : forall pr d bm dt bt a i,
                  bm i = None \/ d a = None ->
                  exec pr d dt bm bt (Write a i) (Failed d) nil
                    
| FailUnseal : forall pr d bm dt bt i,
                 bm i = None ->
                 exec pr d dt bm bt (Unseal i) (Failed d) nil

| FailBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm dt bt tr',
                exec pr d dt bm bt p1 (@Failed T d') tr' ->
                exec pr d dt bm bt (Bind p1 p2) (@Failed T' d') tr'.


Inductive recover_outcome (TF TR: Type) :=
 | RFinished : blockdisk -> tagdisk -> blockmem -> tagmem -> TF -> recover_outcome TF TR
 | RRecovered : blockdisk -> tagdisk -> blockmem -> tagmem -> TR -> recover_outcome TF TR
 | RFailed : blockdisk -> recover_outcome TF TR.

Inductive exec_recover (TF TR: Type):
  perm -> blockdisk -> tagdisk -> blockmem -> tagmem -> prog TF -> prog TR -> recover_outcome TF TR -> trace -> Prop :=
| XRFinished : forall pr tr' d dt bm bt p1 p2 d' dt' bm' bt' (v: TF),
       exec pr d dt bm bt p1 (Finished d' dt' bm' bt' v) tr'
       -> exec_recover pr d dt bm bt p1 p2 (RFinished TR d' dt' bm' bt' v) tr'
| XRFailed : forall pr tr' d dt bm bt p1 p2 d',
       exec pr d dt bm bt p1 (@Failed TF d') tr'
    -> exec_recover pr d dt bm bt p1 p2 (RFailed TF TR d') tr'
| XRCrashedFinished : forall pr tr' tr'' d dt bm bt p1 p2 d' dt' bm' bt' d'r dt'r d'' dt'' bm'' bt'' (v: TR),
    exec pr d dt bm bt p1 (@Crashed TF d' dt' bm' bt') tr'
    -> possible_crash d' d'r
    -> @exec_recover TR TR pr d'r dt'r empty_mem empty_mem  p2 p2 (RFinished TR d'' dt'' bm'' bt'' v) tr''
    -> exec_recover pr d dt bm bt p1 p2 (RRecovered TF d'' dt'' bm'' bt'' v) (tr''++tr')
| XRCrashedRecovered : forall pr tr' tr'' d dt bm bt p1 p2 d' dt' bm' bt' d'r dt'r d'' dt'' bm'' bt'' (v: TR),
    exec pr d dt bm bt p1 (@Crashed TF d' dt' bm' bt') tr'
    -> possible_crash d' d'r
    -> @exec_recover TR TR pr d'r dt'r empty_mem empty_mem  p2 p2 (RRecovered TR d'' dt'' bm'' bt'' v) tr''
    -> exec_recover pr d dt bm bt p1 p2  (RRecovered TF d'' dt'' bm'' bt'' v) (tr''++tr').


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
