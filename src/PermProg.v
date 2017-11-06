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
| Nothing : tag
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

Record state := mkstate {
                    disk : @mem addr Nat.eq_dec tagged_block;
                    blocks: @mem handle Nat.eq_dec tagged_block}.

Definition disk_upd s a b : state :=
  mkstate (upd (disk s) a b) (blocks s).

Definition blocks_upd s a b : state :=
  mkstate (disk s) (upd (blocks s) a b).



Inductive result : Type :=
| Finished : forall T, T -> result.


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
Notation "p1 ;; p2" := (Bind p1 (fun _:unit => p2))
                            (at level 60, right associativity).

Inductive  exec: forall T, perm -> state -> trace -> prog T -> state -> result -> trace -> Prop :=
| ExecRead    : forall p s a i t b tr,
                  blocks s i = None ->
                  disk s a = Some (t, b) ->
                  t <> Nothing ->
                  exec p s tr (Read a)  (blocks_upd s i (t, b)) (Finished i) tr
                 
| ExecWrite   : forall o s a i t b t' b' tr,
                  blocks s i = Some (t, b) ->
                  disk s a  = Some (t', b') ->
                  t <> Nothing ->
                  exec o s tr (Write a i) (disk_upd s a (t, b)) (Finished tt) tr
                       
| ExecSeal : forall s i o t' b tr,
               blocks s i = None ->
               t' <> Nothing ->
               exec o s tr (Seal t' b) (blocks_upd s i (t', b)) (Finished i) (Sea t'::tr)
                    
| ExecUnseal : forall s i o t' b tr,
                 blocks s i = Some (t', b) ->
                 t' <> Nothing ->
                 exec o s tr (Unseal i) s (Finished b) (Uns t'::tr)
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
| ExecRet : forall T s (r: T) o tr,
              exec o s tr (Ret r) s (Finished r) tr
                   
| ExecRun : forall T s s' r (p: prog T) o o' tr tr',
              exec o' s tr p s' r tr' ->
              exec o s tr (Run o' p) s' r (Rn o o'::tr')
                   
| ExecBind : forall T T' (p1 : prog T) (p2: T -> prog T') s s' s'' v r o tr tr' tr'',
               exec o s tr p1 s' (Finished v) tr' ->
               exec o s' tr' (p2 v) s'' r tr'' ->
               exec o s tr (Bind p1 p2) s'' r tr''.

