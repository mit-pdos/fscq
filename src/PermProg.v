Require Import Mem.
Require Export PermAsyncDisk.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.
Require Import Word.

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
| Finished : forall T, tagged_disk -> block_mem -> hashmap -> T -> result
| Crashed : tagged_disk -> block_mem -> hashmap -> result.

Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : tag -> block -> prog handle
| Unseal : handle -> prog block
| Sync : prog unit
| Hash (sz: nat) (buf: word sz) : prog (word hashlen)
| Hash2 (sz1 sz2: nat) (buf1 : word sz1) (buf2 : word sz2) : prog (word hashlen)
| HashHandle : handle -> prog (word hashlen)
| HashHandle2 (h:handle) (sz: nat) (buf: word sz) : prog (word hashlen)
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.


Inductive exec:
  forall T, perm -> trace -> tagged_disk ->
       block_mem -> hashmap -> prog T ->  result -> trace -> Prop :=
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
                     
| StepHashHandle : forall pr d bm hm tr tb i h,
               bm i = Some tb ->
               hash_safe hm h (encode tb) ->
               hash_fwd (encode tb) = h ->
               exec pr tr d bm hm (HashHandle i) (Finished d bm (upd_hashmap' hm h (encode tb)) h) tr

| StepHashHandle2 : forall pr d bm hm tr sz i tb
                      (buf2 : word sz) (buf : word (encoding_length + sz)) h,
                bm i = Some tb ->
                buf = Word.combine (encode tb) buf2 ->
                hash_safe hm h buf ->
                hash_fwd buf = h ->
                exec pr tr d bm hm (HashHandle2 i buf2) (Finished d bm (upd_hashmap' hm h buf) h) tr
                    
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

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' hm hm' tr tr' r,
                exec pr tr d bm hm p1 r tr' ->
                r = (Crashed d' bm' hm') ->
                exec pr tr d bm hm (Bind p1 p2) r tr'.

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
