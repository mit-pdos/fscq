Require Import Prog ProgMonad.
Require Import Cache.
Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.
Require Import PermSecInstr.

Import AddrMap.
Import Map.
Import ListNotations.

Set Implicit Arguments.


Import BUFCACHE.

Lemma find_elements_hd:
  forall T a (v:T) l m,
    elements m = (a, v)::l ->
    find a m = Some v.
Proof.
  intros.
  apply find_1.
  assert (A: InA (fun a b =>  fst a = fst b /\ snd a = snd b)
                 (a,v) (elements m)).
  rewrite H; apply InA_cons_hd; auto.
  apply elements_2 in A; auto.
Qed.

Lemma remove_add_eq:
  forall T a (v:T) m,
    remove a (add a v m) = remove a m.
Proof. (*Can't prove it*) Admitted.


Definition handle_cachemap := Map.t (handle * bool).

Record handle_cachestate :=
  mk_cs {
      HCSMap : handle_cachemap;
      HCSMaxCount : nat;
      HCSCount : nat;
      HCSEvict : eviction_state
    }.


Definition cache_ok cs :=
  fun s => forall a h d,
          find a (HCSMap cs) = Some (h, d) ->
          exists tb, blocks s h = Some tb. 

Definition handle_writeback a (cs : handle_cachestate) :=
  match (find a (HCSMap cs)) with
  | Some (h, true) =>
      Bind (Write a h)
           (fun _ => Ret (mk_cs (Map.add a (h, false) (HCSMap cs))
                             (HCSMaxCount cs) (HCSCount cs)
                             (HCSEvict cs)))
  | _ =>
    Ret cs
  end.

Definition handle_evict' a cs:=
  match Map.find a (HCSMap cs) with
  | Some _ =>
    Ret (mk_cs (Map.remove a (HCSMap cs))
               (HCSMaxCount cs) (HCSCount cs - 1) (HCSEvict cs))
  | None =>
    Ret (mk_cs (Map.remove a (HCSMap cs))
               (HCSMaxCount cs) (HCSCount cs) (HCSEvict cs))
  end.

Definition handle_evict a cs:=
  Bind (handle_writeback a cs)
       (fun cs => handle_evict' a cs).

Definition handle_maybe_evict (cs : handle_cachestate) : prog handle_cachestate :=
  if (lt_dec (HCSCount cs) (HCSMaxCount cs)) then
    Ret cs
  else 
    let (victim, evictor) := eviction_choose (HCSEvict cs) in
    match (Map.find victim (HCSMap cs)) with
    | Some _ =>
      handle_evict victim (mk_cs (HCSMap cs)
          (HCSMaxCount cs) (HCSCount cs) evictor)
    | None => (* evictor failed, evict first block *)
      match (Map.elements (HCSMap cs)) with
      | nil => Ret cs
      | (a, v) :: tl => handle_evict a cs
      end
    end.



Theorem handle_writeback_secure_dirty :
  forall a s cs h t b,
    (find a (HCSMap cs)) = Some (h, true) ->
    permission_secure None s (handle_writeback a cs)
          (fun s => blocks s h = Some (t, b))
          (fun s s' r =>
             s' = disk_upd s a (t, b) /\
             r = (mk_cs (Map.add a (h, false) (HCSMap cs))
                        (HCSMaxCount cs) (HCSCount cs)
                        (HCSEvict cs))).
Proof.
  unfold handle_writeback; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.  

Theorem handle_writeback_secure_clean :
  forall a s h cs,
    (find a (HCSMap cs)) = Some (h, false) ->
    permission_secure None s (handle_writeback a cs) (fun _ => True)
                      (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_writeback; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.

Theorem handle_writeback_secure_none :
  forall a s cs,
    (find a (HCSMap cs)) = None ->
    permission_secure None s (handle_writeback a cs) (fun _ => True)
                      (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_writeback; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.  

Theorem handle_writeback_secure :
  forall a s cs t b,
    permission_secure None s (handle_writeback a cs)
         (fun s => forall h, find a (HCSMap cs) = Some (h, true) ->
                     blocks s h = Some (t, b))
         (fun s s' r =>
            match find a (HCSMap cs) with
            |Some (h, true) =>
             s' = disk_upd s a (t, b) /\
             r = (mk_cs (Map.add a (h, false) (HCSMap cs))
                        (HCSMaxCount cs) (HCSCount cs) (HCSEvict cs))
            | _ =>  s' = s /\ r = cs
            end).
Proof.
  intros.
  destruct (find a (HCSMap cs)) eqn:D.
  destruct p.
  destruct b0.
  eapply pre_impl_secure.
  apply handle_writeback_secure_dirty; auto.
  intros; simpl; auto.
  eapply pre_impl_secure.
  eapply handle_writeback_secure_clean; eauto.
  intros; simpl; auto.
  eapply pre_impl_secure.
  apply handle_writeback_secure_none; auto.
  intros; simpl; auto.
Qed.  




Theorem handle_evict'_secure_some:
  forall a s cs cb,
    (find a (HCSMap cs)) = Some cb ->
    permission_secure None s (handle_evict' a cs)  (fun s => True)
         (fun s s' r =>
            s' = s /\
            r = (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs - 1) (HCSEvict cs))).
Proof.
  unfold handle_evict'; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.

Theorem handle_evict'_secure_none:
  forall s a cs,
    (find a (HCSMap cs)) = None ->
    permission_secure None s (handle_evict' a cs)  (fun s => True)
         (fun s s' r =>
            s' = s /\
            r = (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs) (HCSEvict cs))).
Proof.
  unfold handle_evict'; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.

Theorem handle_evict'_secure:
  forall s a cs,
    permission_secure None s (handle_evict' a cs)  (fun s => True)
         (fun s s' r =>
            s' = s /\
            match find a (HCSMap cs) with
            | None =>
              r = (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                         (HCSCount cs) (HCSEvict cs))
            | Some _ =>
              r = (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                         (HCSCount cs - 1) (HCSEvict cs))
            end).
Proof.
  intros; destruct (find a (HCSMap cs)) eqn:d.
  eapply handle_evict'_secure_some; eauto.
  eapply handle_evict'_secure_none; eauto.
Qed.




Theorem handle_evict_secure_dirty:
  forall s a cs h t b,
    find a (HCSMap cs) = Some (h, true) ->
    permission_secure None s (handle_evict a cs)
         (fun s => blocks s h = Some (t, b))
         (fun s s' r =>
            s' = disk_upd s a (t, b) /\
            r = (mk_cs (Map.remove a
                         (Map.add a (h, false) (HCSMap cs)))
                       (HCSMaxCount cs) (HCSCount cs - 1)
                       (HCSEvict cs))).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  apply handle_writeback_secure_dirty; auto.
  {
    simpl; intros; cleanup.
    Existential 1 := fun _ => True.
    simpl; auto.
  }

  {
    simpl; intros; cleanup; intuition.
    unfold disk_upd; simpl.
    rewrite upd_repeat; auto.
  }

  {
    simpl; intros; cleanup.
    eapply post_impl_secure.
    eapply handle_evict'_secure_some.
    simpl; apply MapFacts.add_eq_o; auto.
    simpl; intros; cleanup.
    unfold disk_upd; simpl.
    rewrite upd_repeat; eauto.
  }    
Qed.

Theorem handle_evict_secure_clean:
  forall s a cs h,
    find a (HCSMap cs) = Some (h, false) ->
    permission_secure None s (handle_evict a cs)  (fun s => True)
        (fun s s' r =>
           s' = s /\
           r =  (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs - 1) (HCSEvict cs))).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  eapply handle_writeback_secure_clean; eauto.
  {
    simpl; intros; cleanup.
    Existential 1 := fun _ => True.
    simpl; auto.
  }

  {
    simpl; intros; cleanup; intuition.
  }

  {
    simpl; intros; cleanup.
    eapply handle_evict'_secure_some; eauto.
  }    
Qed.

Theorem handle_evict_secure_none:
  forall s a cs,
    find a (HCSMap cs) = None ->
    permission_secure None s (handle_evict a cs)  (fun s => True)
        (fun s s' r =>
           s' = s /\
           r =  (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs) (HCSEvict cs))).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  eapply handle_writeback_secure_none; eauto.
  {
    simpl; intros; cleanup.
    Existential 1 := fun _ => True.
    simpl; auto.
  }

  {
    simpl; intros; cleanup; intuition.
  }

  {
    simpl; intros; cleanup.
    eapply handle_evict'_secure_none; eauto.
  }    
Qed.

Theorem handle_evict_secure:
  forall s a cs t b,
    permission_secure None s (handle_evict a cs)
        (fun s => forall h, find a (HCSMap cs) = Some (h, true) ->
                    blocks s h = Some (t, b))
        (fun s s' r =>
           match find a (HCSMap cs) with
           | Some (h, true) =>
             s' = disk_upd s a (t, b) /\
             r = (mk_cs (Map.remove a (HCSMap cs))
                        (HCSMaxCount cs) (HCSCount cs - 1)
                        (HCSEvict cs))
           | Some (h, false) =>
             s' = s /\
             r = (mk_cs (Map.remove a (HCSMap cs))
                        (HCSMaxCount cs) (HCSCount cs - 1)
                        (HCSEvict cs))
           | None =>
             s' = s /\
             r = (mk_cs (Map.remove a (HCSMap cs))
                        (HCSMaxCount cs) (HCSCount cs)
                        (HCSEvict cs))
           end).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  eapply handle_writeback_secure; eauto.
  {
    simpl; intros; cleanup.
    Existential 1 := fun _ => True.
    simpl; auto.
  }

  {
    simpl; intros; cleanup; intuition.
    destruct (find a (HCSMap cs)) eqn:D; cleanup; intuition.
    destruct p; destruct b0; cleanup; intuition.
    unfold disk_upd; simpl.
    rewrite upd_repeat; auto.
  }

  {
    simpl; intros; cleanup.
    eapply post_impl_secure.
    eapply handle_evict'_secure; eauto.
    simpl; intros; cleanup.
    destruct (find a (HCSMap cs)) eqn:D; cleanup.
    destruct p; destruct b0; cleanup.
    simpl in *.
    rewrite MapFacts.add_eq_o in *; auto.
    rewrite remove_add_eq in *.
    intuition.
    unfold disk_upd; simpl.
    rewrite upd_repeat; auto.
    all: intuition.
  }    
Qed.




Theorem handle_maybe_evict_secure_lt:
  forall s cs,
    (HCSCount cs) < (HCSMaxCount cs) ->
    permission_secure None s (handle_maybe_evict cs)
         (fun _ => True)
         (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_maybe_evict; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); try omega.
  apply ret_secure.
Qed.

Theorem handle_maybe_evict_secure_ge_victim:
  forall s cs h bl t b,
    (HCSCount cs) >= (HCSMaxCount cs) ->
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    (Map.find victim (HCSMap cs)) = Some (h, bl) ->
    permission_secure None s (handle_maybe_evict cs)
        (fun s => blocks s h = Some (t, b))
        (fun s s' r =>
           match bl with
           | true => s' = disk_upd s victim (t, b)
           | false =>  s' = s
           end /\
           r = (mk_cs (Map.remove victim (HCSMap cs))
                      (HCSMaxCount cs) (HCSCount cs - 1)
                      evictor)).
Proof.
  unfold handle_maybe_evict; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); try omega.
  destruct (eviction_choose (HCSEvict cs)); simpl in *; cleanup.
  eapply impl_secure.
  eapply handle_evict_secure.
  simpl; intros; cleanup.
  destruct bl; cleanup; intuition.
  simpl; intros; cleanup; eauto.
Qed.



Theorem handle_maybe_evict_secure_ge_empty:
  forall s cs,
    (HCSCount cs) >= (HCSMaxCount cs) ->
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    (Map.find victim (HCSMap cs)) = None ->
    (Map.elements (HCSMap cs)) = nil -> 
    permission_secure None s (handle_maybe_evict cs)
                      (fun s => True)
                      (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_maybe_evict; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); try omega.
  destruct (eviction_choose (HCSEvict cs)); simpl in *; cleanup.
  apply ret_secure.
Qed.

Theorem handle_maybe_evict_secure_ge_nonempty:
  forall s cs h a l t b bl,
    (HCSCount cs) >= (HCSMaxCount cs) ->
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    (Map.find victim (HCSMap cs)) = None ->
    (Map.elements (HCSMap cs)) = (a, (h, bl))::l -> 
    permission_secure None s (handle_maybe_evict cs)
       (fun s => blocks s h = Some (t, b) )
       (fun s s' r =>
          match bl with
          | true => s' = disk_upd s a (t, b)
          | false => s' = s
          end /\
          r = (mk_cs (Map.remove a (HCSMap cs))
                     (HCSMaxCount cs) (HCSCount cs - 1)
                     (HCSEvict cs))).
Proof.
  unfold handle_maybe_evict; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); try omega.
  destruct (eviction_choose (HCSEvict cs)); simpl in *; cleanup.
  eapply impl_secure.
  apply handle_evict_secure.
  {
    simpl; intros.
    apply find_elements_hd in H1; cleanup.  
    destruct bl; eauto.
  }
  {
    simpl; intros.
    apply find_elements_hd in H1; cleanup; auto.  
  }
Qed.

Theorem handle_maybe_evict_secure:
  forall s t b cs,
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    permission_secure None s (handle_maybe_evict cs)
       (fun s => forall a h bl l, (HCSCount cs) >= (HCSMaxCount cs) ->
              (find victim (HCSMap cs) = Some (h, bl) \/
               elements (HCSMap cs) = (a, (h, bl))::l) ->
              blocks s h = Some (t, b))
      (fun s s' r =>
         if (lt_dec (HCSCount cs) (HCSMaxCount cs)) then
           s' = s /\ r = cs
         else 
           match (find victim (HCSMap cs)) with
           | Some (h, bl)=>
               match bl with
               | true => s' = disk_upd s victim tb
               | false =>  s' = s
               end /\
               r = (mk_cs (Map.remove victim (HCSMap cs))
                          (HCSMaxCount cs) (HCSCount cs - 1)
                          evictor)
           | None =>
             match (Map.elements (HCSMap cs)) with
             | nil => s' = s /\ r = cs
             | (a, (h, bl)) :: tl =>
               match bl with
               | true =>
                 s' = disk_upd s a tb
               | false =>
                 s' = s
               end /\
               r = (mk_cs (Map.remove a (HCSMap cs))
                          (HCSMaxCount cs) (HCSCount cs - 1)
                          (HCSEvict cs))
             end
           end).
Proof.
  unfold cache_ok; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)).
  eapply pre_impl_secure.
  apply handle_maybe_evict_secure_lt; auto.
  simpl; intuition.
  destruct (find (fst (eviction_choose (HCSEvict cs))) (HCSMap cs)) eqn:D.
  destruct p.
  eapply impl_secure.
  apply handle_maybe_evict_secure_ge_victim; eauto; try omega. 
  simpl; intros; cleanup; intuition.
  simpl; intros; cleanup; intuition.
  specialize (H _ _ _ D); cleanup.
  destruct x.
  eauto
  eapply H; try omega; intuition.
  destruct (elements (HCSMap cs)) eqn:D0.
  eapply pre_impl_secure.
  apply handle_maybe_evict_secure_ge_empty; eauto; try omega.
  simpl; intuition.
  destruct p.
  destruct p.
  eapply pre_impl_secure.
  eapply handle_maybe_evict_secure_ge_nonempty; eauto; try omega.
  simpl; intros; cleanup.
  eapply H; eauto; try omega.
  Unshelve.
  all: econstructor.
Qed.






Definition handle_read a (cs : handle_cachestate) :=
  Bind (handle_maybe_evict cs)
       (fun cs =>
          match Map.find a (HCSMap cs) with
          | Some (v, _) => Ret (cs, v)
          | None =>
            Bind (Read a)
                 ( fun v => Ret (mk_cs (Map.add a (v, false) (HCSMap cs))
                                    (HCSMaxCount cs) (HCSCount cs + 1)
                                    (eviction_update (HCSEvict cs) a), v))
          end).

Theorem handle_read_secure_cache_dirty:
  forall s a h b cs,
    Map.find a (HCSMap cs) = Some (h, b) ->
    permission_secure None s (handle_read a cs) (fun s => forall a h bl, find a (HCSMap cs) = Some(h, bl) -> exists t b, blocks s h = Some (t, b)) (fun s s' r => r = (cs, h)).
Proof.
  unfold handle_read; intros; cleanup.
  eapply bind_secure.
  eapply pre_impl_secure.
  apply handle_maybe_evict_secure.
  simpl; intros.
  destruct 
  Existential 1:= fun _ => True. intuition.
  intuition.
  destruct (Map.find a (HCSMap r)).
  destruct p; apply ret_secure.
  apply no_trace_secure; simpl; auto.
Qed.

Definition handle_write a i (cs : handle_cachestate) :=
  Bind (handle_maybe_evict cs)
       (fun cs =>
          match Map.find a (HCSMap cs) with
          | Some _ =>
            Ret (mk_cs (Map.add a (i, true) (HCSMap cs))
                       (HCSMaxCount cs) (HCSCount cs) (eviction_update (HCSEvict cs) a))
          | None =>
            Ret (mk_cs (Map.add a (i, true) (HCSMap cs))
                       (HCSMaxCount cs) (HCSCount cs + 1) (eviction_update (HCSEvict cs) a))
          end).
Proof.
  
  Theorem handle_write_secure:
    forall a i cs,
      permission_secure None (handle_write a i cs) (fun _ => True) (fun _ _ => True).
  Proof.
    unfold handle_write; intros.
    eapply bind_secure.
    apply handle_maybe_evict_secure.
    Existential 1:= fun _ => True. intuition.
    intuition.
    destruct (Map.find a (HCSMap r));
    apply ret_secure.
  Qed.

