Require Import Mem.
Require Export PermAsyncDisk.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.

Set Implicit Arguments.

Definition perm := option nat. (* None can only read public blocks *)
Definition handle := nat.


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
Definition handle_eq_dec:= Nat.eq_dec.
Definition tagged_disk:= rawdisk.
Definition block_mem:= @Mem.mem handle handle_eq_dec tagged_block.

Inductive result : Type :=
| Finished : forall T, tagged_disk -> block_mem -> T -> result
| Crashed : tagged_disk -> result.

Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : tag -> block -> prog handle
| Unseal : handle -> prog block
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

Notation "x <- p1 ;; p2" := (Bind p1 (fun x => p2))
                              (at level 60, right associativity).

Inductive exec:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> prog T ->  result -> trace -> Prop :=
| ExecRead    : forall pr d bm a i tb tbs tr,
                  bm i = None ->
                  d a = Some (tb, tbs) ->
                  exec pr tr d bm (Read a) (Finished d (upd bm i tb) i) tr                 
| ExecWrite   : forall pr d bm a i tb tbs tr,
                  bm i = Some tb ->
                  d a = Some tbs ->
                  exec pr tr d bm (Write a i) (Finished (upd d a (tb, vsmerge tbs)) bm tt) tr
                       
| ExecSeal : forall pr d bm i t b tr,
               bm i = None ->
               exec pr tr d bm (Seal t b) (Finished d (upd bm i (t, b)) i) (Sea t::tr)
                    
| ExecUnseal : forall pr d bm i tb tr,
                 bm i = Some tb ->
                 exec pr tr d bm (Unseal i) (Finished d bm (snd tb)) (Uns (fst tb)::tr)

| ExecRet : forall T pr d bm (r: T) tr,
              exec pr tr d bm (Ret r) (Finished d bm r) tr
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm d' bm' v r tr tr' tr'',
               exec pr tr d bm p1 (Finished d' bm' v) tr' ->
               exec pr tr' d' bm' (p2 v) r tr'' ->
               exec pr tr d bm (Bind p1 p2) r tr''
                      
| CrashRead : forall pr d bm a tr,
                exec pr tr d bm (Read a) (Crashed d) tr
                        
| CrashWrite : forall pr d bm a i tr,
                 exec pr tr d bm (Write a i) (Crashed d) tr
                         
| CrashSeal : forall pr d bm t b tr,
                exec pr tr d bm (Seal t b) (Crashed d) tr
                        
| CrashUnseal : forall pr d bm i tr,
                exec pr tr d bm (Unseal i) (Crashed d) tr
                    
| CrashRet : forall T pr d bm (r: T) tr,
              exec pr tr d bm (Ret r) (Crashed d) tr

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm tr tr' r,
                exec pr tr d bm p1 r tr' ->
                r = (Crashed d') ->
                exec pr tr d bm (Bind p1 p2) r tr'.
