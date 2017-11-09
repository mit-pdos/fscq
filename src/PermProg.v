Require Import Mem.
Require Import AsyncDisk.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.

Set Implicit Arguments.

Definition perm := option nat. (* None can only read public blocks *)
Definition owner := nat.
Definition handle := nat.
Definition block := valu.

Definition perm_dec : forall (p p': perm), {p = p'}+{p <> p'}.
  intros; destruct p, p'; try (solve [left; auto] || solve [right; congruence]).
  destruct (Nat.eq_dec n n0); subst; auto; right; congruence.
Defined.

Inductive tag :=
(* | Nothing : tag *)
| Public : tag
| Private : owner -> tag.

Definition tag_dec : forall (t t': tag), {t = t'}+{t <> t'}.
  intros; destruct t, t'; auto; try solve [right; congruence].
  destruct (Nat.eq_dec o o0); subst; auto; right; congruence.
Defined.

Hypothesis permitted: perm -> perm -> Prop.

Definition tagged_block := (tag * block)%type.

Inductive op :=
| Sea : tag -> op
| Uns : tag -> op
| Rn : perm -> perm -> op.

Definition op_dec : forall (o o': op), {o = o'}+{o <> o'}.
  intros.
  destruct o, o'; auto; try (solve [right; congruence] ||
  solve [destruct (tag_dec t t0); subst; auto; right; congruence]).
  destruct (perm_dec p p1); subst; try solve [right; congruence].
  destruct (perm_dec p0 p2); subst; auto; right; congruence.
Defined.

Definition trace := list op.
Definition tagged_disk:= @Mem.mem addr Nat.eq_dec tagged_block.
Definition block_mem:= @Mem.mem handle Nat.eq_dec tagged_block.

Inductive result : Type :=
| Finished : forall T, tagged_disk -> block_mem -> T -> result.


Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : tag -> block -> prog handle
| Unseal : handle -> prog block
(* 
| GetTag : handle -> prog tag
| Clear : handle -> prog unit (* Clears the blocks memory. May simplify security specs *)
| Purge : addr -> prog unit (* Clears a block and sets its tag to 'Nothing' *) 
*)
| Ret : forall T, T -> prog T
| Run : forall T, perm -> prog T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

Notation "x <- p1 ;; p2" := (Bind p1 (fun x => p2))
                              (at level 60, right associativity).

Inductive  exec:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> prog T ->  result -> trace -> Prop :=
| ExecRead    : forall pr d bm a i tb tr,
                  bm i = None ->
                  d a = Some tb ->
                  exec pr tr d bm (Read a) (Finished d (upd bm i tb) i) tr                 
| ExecWrite   : forall pr d bm a i tb tr,
                  bm i = Some tb ->
                  d a <> None ->
                  exec pr tr d bm (Write a i) (Finished (upd d a tb) bm tt) tr
                       
| ExecSeal : forall pr d bm i t b tr,
               bm i = None ->
               exec pr tr d bm (Seal t b) (Finished d (upd bm i (t, b)) i) (Sea t::tr)
                    
| ExecUnseal : forall pr d bm i tb tr,
                 bm i = Some tb ->
                 exec pr tr d bm (Unseal i) (Finished d bm (snd tb)) (Uns (fst tb)::tr)
(* 
| ExecGetTag : forall o s i t b tr,
                 blocks s i = Some (t, b) ->
                 t <> Nothing ->
                 exec o s tr (GetTag i) s (Finished t) tr
                      
| ExecClear : forall o h s tr,
                exec o s tr (Clear h)  (mkstate (disk s)
                                                (mem_except Nat.eq_dec (blocks s) h)) (Finished tt) tr
| ExecPurge :  forall o a s tr,
                 exec o s tr (Purge a)  (disk_upd s a (Nothing, 0)) (Finished tt) tr
*)                      
| ExecRet : forall T pr d bm (r: T) tr,
              exec pr tr d bm (Ret r) (Finished d bm r) tr
                   
| ExecRun : forall T pr pr' d bm r (p: prog T) tr tr',
              exec pr' tr d bm p r tr' ->
              exec pr tr d bm (Run pr' p) r (Rn pr pr'::tr')
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm d' bm' v r tr tr' tr'',
               exec pr tr d bm p1 (Finished d' bm' v) tr' ->
               exec pr tr' d' bm' (p2 v) r tr'' ->
               exec pr tr d bm (Bind p1 p2) r tr''.

