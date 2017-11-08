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


Definition h_cachemap := t (handle * bool).

Record h_cachestate :=
  mk_cs {
      HCSMap : h_cachemap;
      HCSMaxCount : nat;
      HCSCount : nat;
      HCSEvict : eviction_state
    }.

Definition tagged_disk:= @Mem.mem addr addr_eq_dec tagged_block.
Definition block_mem:= @Mem.mem handle addr_eq_dec tagged_block.


 (** rep invariant *)

  Definition size_valid cs :=
    cardinal (HCSMap cs) = HCSCount cs /\
    cardinal (HCSMap cs) <= HCSMaxCount cs /\
    HCSMaxCount cs <> 0.

  Definition addr_valid (d: tagged_disk) (cm : h_cachemap) :=
    forall a, In a cm -> d a <> None.

Definition handle_valid (b: block_mem) (cm: h_cachemap) :=
  forall a cb, find a cm = Some cb -> b (fst cb) <> None.   
  
  Definition cachepred (s: state) (cache : h_cachemap) (a : addr) (tb: tagged_block ) : @pred _ addr_eq_dec tagged_block :=
    (match find a cache with
    | None => a |-> tb
    | Some (h, false) => a |-> tb * [[ blocks s h = Some tb ]]
    | Some (h, true)  => exists tb0, a |-> tb0 * [[ blocks s h = Some tb ]]
    end)%pred.

  Definition rep (cs : h_cachestate) (m : tagged_disk) (s: state): Prop :=
    ([[ size_valid cs /\
        addr_valid m (HCSMap cs) /\
        handle_valid (blocks s) (HCSMap cs) ]] *
     mem_pred (cachepred s (HCSMap cs)) m)%pred (disk s).







Definition handle_writeback a (cs : handle_cachestate) :=
  match find a (HCSMap cs) with
  | Some (h, true) =>
      Bind (Write a h)
           (fun _ => Ret (mk_cs (Map.add a (h, false) (HCSMap cs))
                             (HCSMaxCount cs) (HCSCount cs)
                             (HCSEvict cs)))
  | _ =>
    Ret cs
  end.

Definition handle_evict' a cs:=
  match find a (HCSMap cs) with
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
    match find victim (HCSMap cs) with
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
    find a (HCSMap cs) = Some (h, true) ->
    blocks s h = Some (t, b) ->
    permission_secure None s (handle_writeback a cs)
          (fun s s' r =>
             s' = disk_upd s a (t, b) /\
             r = (mk_cs (add a (h, false) (HCSMap cs))
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
    find a (HCSMap cs) = Some (h, false) ->
    permission_secure None s (handle_writeback a cs)
                      (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_writeback; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.

Theorem handle_writeback_secure_none :
  forall a s cs,
    find a (HCSMap cs) = None ->
    permission_secure None s (handle_writeback a cs)
                      (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_writeback; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.  

Theorem handle_writeback_secure :
  forall a s cs t b,
    (forall h, find a (HCSMap cs) = Some (h, true) ->
          blocks s h = Some (t, b)) ->
    permission_secure None s (handle_writeback a cs)
         (fun s s' r =>
            match find a (HCSMap cs) with
            |Some (h, true) =>
             s' = disk_upd s a (t, b) /\
             r = (mk_cs (add a (h, false) (HCSMap cs))
                        (HCSMaxCount cs) (HCSCount cs) (HCSEvict cs))
            | _ =>  s' = s /\ r = cs
            end).
Proof.
  intros.
  destruct (find a (HCSMap cs)) eqn:D.
  destruct p.
  destruct b0.
  apply handle_writeback_secure_dirty; auto.
  eapply handle_writeback_secure_clean; eauto.
  apply handle_writeback_secure_none; auto.
Qed.  




Theorem handle_evict'_secure_some:
  forall a s cs cb,
    find a (HCSMap cs) = Some cb ->
    permission_secure None s (handle_evict' a cs)
         (fun s s' r =>
            s' = s /\
            r = (mk_cs (remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs - 1) (HCSEvict cs))).
Proof.
  unfold handle_evict'; intros; cleanup.
  unfold permission_secure; intros; cleanup.
  repeat inv_exec_perm; simpl; cleanup.
  simpl; intuition; apply upd_eq; auto.
Qed.

Theorem handle_evict'_secure_none:
  forall s a cs,
    find a (HCSMap cs) = None ->
    permission_secure None s (handle_evict' a cs)
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
    permission_secure None s (handle_evict' a cs)
         (fun s s' r =>
            s' = s /\
            match find a (HCSMap cs) with
            | None =>
              r = (mk_cs (remove a (HCSMap cs)) (HCSMaxCount cs)
                         (HCSCount cs) (HCSEvict cs))
            | Some _ =>
              r = (mk_cs (remove a (HCSMap cs)) (HCSMaxCount cs)
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
    blocks s h = Some (t, b) ->
    permission_secure None s (handle_evict a cs)     
         (fun s s' r =>
            s' = disk_upd s a (t, b) /\
            r = (mk_cs (remove a
                         (add a (h, false) (HCSMap cs)))
                       (HCSMaxCount cs) (HCSCount cs - 1)
                       (HCSEvict cs))).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  apply handle_writeback_secure_dirty; eauto.
  {
    simpl; intros; cleanup; intuition.
    unfold disk_upd; simpl.
    rewrite upd_repeat; auto.
  }

  {
    simpl; intros; cleanup.
    eapply impl_secure.
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
    permission_secure None s (handle_evict a cs)
        (fun s s' r =>
           s' = s /\
           r =  (mk_cs (remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs - 1) (HCSEvict cs))).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  eapply handle_writeback_secure_clean; eauto.

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
    permission_secure None s (handle_evict a cs)
        (fun s s' r =>
           s' = s /\
           r =  (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs)
                       (HCSCount cs) (HCSEvict cs))).
Proof.
  unfold handle_evict; intros; cleanup.
  eapply bind_secure.
  eapply handle_writeback_secure_none; eauto.
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
    (forall h, find a (HCSMap cs) = Some (h, true) ->
          blocks s h = Some (t, b)) ->
    permission_secure None s (handle_evict a cs)
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
    simpl; intros; cleanup; intuition.
    destruct (find a (HCSMap cs)) eqn:D; cleanup; intuition.
    destruct p; destruct b0; cleanup; intuition.
    unfold disk_upd; simpl.
    rewrite upd_repeat; auto.
  }

  {
    simpl; intros; cleanup.
    eapply impl_secure.
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
         (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_maybe_evict; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); try omega.
  apply ret_secure.
Qed.

Theorem handle_maybe_evict_secure_ge_victim:
  forall s cs h bl t b,
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    ~(HCSCount cs < HCSMaxCount cs) ->
    find victim (HCSMap cs) = Some (h, bl) ->
    blocks s h = Some (t, b) ->
    permission_secure None s (handle_maybe_evict cs)
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
  simpl; intros; cleanup; eauto.
  simpl; intros; cleanup; eauto.
  destruct bl; cleanup; intuition.
Qed.



Theorem handle_maybe_evict_secure_ge_empty:
  forall s cs,
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    (HCSCount cs) >= (HCSMaxCount cs) ->
    find victim (HCSMap cs) = None ->
    elements (HCSMap cs) = nil -> 
    permission_secure None s (handle_maybe_evict cs)
                      (fun s s' r => s' = s /\ r = cs).
Proof.
  unfold handle_maybe_evict; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); try omega.
  destruct (eviction_choose (HCSEvict cs)); simpl in *; cleanup.
  apply ret_secure.
Qed.

Theorem handle_maybe_evict_secure_ge_nonempty:
  forall s cs h a l t b bl,
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    (HCSCount cs) >= (HCSMaxCount cs) ->
    find victim (HCSMap cs) = None ->
    elements (HCSMap cs) = (a, (h, bl))::l ->
    blocks s h = Some (t, b) ->
    permission_secure None s (handle_maybe_evict cs)
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
    eauto.
  }
  {
    simpl; intros.
    apply find_elements_hd in H1; cleanup; auto.
    destruct bl; cleanup; auto.
  }
Qed.

Theorem handle_maybe_evict_secure:
  forall s t b t' b' cs,
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    ((HCSCount cs) >= (HCSMaxCount cs) ->
     (forall h bl, find victim (HCSMap cs) = Some (h, bl) -> blocks s h = Some (t, b)) /\
     (forall a h bl l, elements (HCSMap cs) = (a, (h, bl))::l -> blocks s h = Some (t', b'))) ->
    permission_secure None s (handle_maybe_evict cs)
      (fun s s' r =>
         if (lt_dec (HCSCount cs) (HCSMaxCount cs)) then
           s' = s /\ r = cs
         else 
           match (find victim (HCSMap cs)) with
           | Some (h, bl)=>
               match bl with
               | true => s' = disk_upd s victim (t, b)
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
                 s' = disk_upd s a (t', b')
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
  apply handle_maybe_evict_secure_lt; auto.
  destruct (find (fst (eviction_choose (HCSEvict cs))) (HCSMap cs)) eqn:D.
  destruct p.
  eapply impl_secure.
  eapply handle_maybe_evict_secure_ge_victim; eauto; try omega.
  edestruct H; try omega.
  eapply H0; eauto; try omega.
  simpl; intros; cleanup; intuition.
  destruct (elements (HCSMap cs)) eqn:D0.
  apply handle_maybe_evict_secure_ge_empty; eauto; try omega.
  destruct p. destruct p.
  eapply handle_maybe_evict_secure_ge_nonempty; eauto; try omega.
  edestruct H; eauto; try omega.
Qed.






Definition handle_read a (cs : handle_cachestate) :=
  Bind (handle_maybe_evict cs)
       (fun cs =>
          match Map.find a (HCSMap cs) with
          | Some (v, _) => Ret (cs, v)
          | None =>
            Bind (Read a)
                 (fun v => Ret (mk_cs (Map.add a (v, false) (HCSMap cs))
                                    (HCSMaxCount cs) (HCSCount cs + 1)
                                    (eviction_update (HCSEvict cs) a), v))
          end).

Theorem handle_read_secure:
  forall s a cs t b t' b' t'' b'',
    let victim := fst(eviction_choose (HCSEvict cs)) in
    let evictor := snd(eviction_choose (HCSEvict cs)) in
    ((HCSCount cs) >= (HCSMaxCount cs) ->
     (forall h bl, find victim (HCSMap cs) = Some (h, bl) -> blocks s h = Some (t, b)) /\
     (forall a h bl l, elements (HCSMap cs) = (a, (h, bl))::l -> blocks s h = Some (t', b'))) ->
    disk s a = Some (t'', b'') ->
    permission_secure None s (handle_read a cs) (fun s s' r => True).
Proof. Admitted.
(*
  unfold handle_read; intros; cleanup.
  eapply bind_secure.
  apply handle_maybe_evict_secure; eauto.
  eauto.
  
  simpl; intros.
  destruct (lt_dec (HCSCount cs) (HCSMaxCount cs)); cleanup.
  {
    destruct (find a (HCSMap cs)) eqn:D.
    destruct p.
    eapply impl_secure.
    apply ret_secure.
    simpl; eauto.

    eapply bind_secure.
    apply read_secure; eauto.
    simpl; intros; cleanup; eauto.
    simpl; intros; cleanup.
    eapply impl_secure.
    eapply ret_secure.
    simpl; eauto.
  }

  {
    destruct (find 0 (HCSMap cs)) eqn: D0.
    {
      destruct (Nat.eq_dec 0 a); subst.
      {
        destruct p, b0; cleanup; simpl in *;
        rewrite MapFacts.remove_eq_o; auto.
        {
          eapply bind_secure.
          apply read_secure; eauto.
          simpl; intros; cleanup; eauto.    
          apply upd_eq; auto.
          simpl; intros; cleanup; auto.
          simpl; intros; cleanup; auto.
          eapply impl_secure.
          eapply ret_secure.
          simpl; intros; cleanup; auto.
        }
        {
          eapply bind_secure.
          apply read_secure; eauto.
          simpl; intros; cleanup; eauto.    
          simpl; intros; cleanup; auto.
          eapply impl_secure.
          eapply ret_secure.
          simpl; intros; cleanup; auto.
        }
        
      }
      

      {
        destruct p, b0; cleanup; simpl in *;
        rewrite MapFacts.remove_neq_o; auto;
        destruct (find a (HCSMap cs)).
        {
          destruct p.
          eapply impl_secure.
          eapply ret_secure.
          simpl; intros; cleanup; auto.
        }
        {          
          eapply bind_secure.
          apply read_secure; eauto.
          simpl; intros; cleanup; eauto.    
          rewrite upd_ne; eauto.
          simpl; intros; cleanup; auto.
          simpl; intros; cleanup; auto.
          eapply impl_secure.
          eapply ret_secure.
          simpl; intros; cleanup; auto.
        }
         {
          destruct p.
          eapply impl_secure.
          eapply ret_secure.
          simpl; intros; cleanup; auto.
        }
        {          
          eapply bind_secure.
          apply read_secure; eauto.
          simpl; intros; cleanup; eauto.    
          simpl; intros; cleanup; auto.
          eapply impl_secure.
          eapply ret_secure.
          simpl; intros; cleanup; auto.
        }
      }
    }
Admitted.
*)

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

  
  Theorem handle_write_secure:
    forall a s i cs,
      permission_secure None s (handle_write a i cs) (fun _ _ _ => True).
  Proof. Admitted.

