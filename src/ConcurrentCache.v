Require Import CoopConcur.
Require Import CoopConcurAuto.
Import RelationClasses.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Import List.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.
Require Import WriteBufferSet.

(* TODO: split into state/protocol separately to allow creating global protocol
from module protocol definitions *)
Module Type GlobalProtocol.
  Parameter Sigma:State.
  Parameter delta:Protocol Sigma.
End GlobalProtocol.

Definition Sigma := defState
                  [Cache; WriteBuffer]
                  [Cache; WriteBuffer; DISK; Disk].

Module Type CacheProj (App:GlobalProtocol).
  Parameter stateProj:StateProj App.Sigma Sigma.
End CacheProj.

Module CacheProtocol (App:GlobalProtocol) (Proj:CacheProj App).

  Section Variables.

    Tactic Notation "var" constr(n) uconstr(f) :=
      let t := constr:(ltac:(hget n (f Proj.stateProj))) in
      exact t.

    Tactic Notation "mvar" constr(n) := var n memVars.
    Tactic Notation "absvar" constr(n) := var n abstractionVars.

    (* memory variables *)
    Definition mCache := ltac:(mvar 0).
    Definition mWriteBuffer := ltac:(mvar 1).

    (* abstraction ("virtual") variables *)
    Definition vCache := ltac:(absvar 0).
    Definition vWriteBuffer := ltac:(absvar 1).
    (* the linearized disk, which evolves at each syscall *)
    Definition vDisk0 := ltac:(absvar 2).
    (* the disk from the perspective of the current syscall *)
    Definition vdisk := ltac:(absvar 3).
  End Variables.

  (* TODO: var_index_neq_mem and var_index_neq_abstraction are generic, should
  be moved out *)

  Lemma var_index_neq_mem :
    forall (Sigma Sigma':State) (proj: StateProj Sigma Sigma')
      t (m: var (mem_types Sigma') t)
      t' (m': var (mem_types Sigma') t'),
      member_index m <> member_index m' ->
      member_index (get m (memVars proj)) <>
      member_index (get m' (memVars proj)).
  Proof.
    intros; destruct proj; unfold variables in *; cbn.
    repeat rewrite member_index_eq_var_index.
    rewrite ?get_hmap with (def:=0).
    apply NoDup_get_neq;
      autorewrite with hlist;
      eauto using member_index_bound.
  Qed.

  Lemma var_index_neq_abstraction :
    forall (Sigma Sigma':State) (proj: StateProj Sigma Sigma')
      t (m: var (abstraction_types Sigma') t)
      t' (m': var (abstraction_types Sigma') t'),
      member_index m <> member_index m' ->
      member_index (get m (abstractionVars proj)) <>
      member_index (get m' (abstractionVars proj)).
  Proof.
    intros; destruct proj; unfold variables in *; cbn.
    repeat rewrite member_index_eq_var_index.
    rewrite ?get_hmap with (def:=0).
    apply NoDup_get_neq;
      autorewrite with hlist;
      eauto using member_index_bound.
  Qed.

  Ltac vars_distinct :=
    (apply (var_index_neq_abstraction (Sigma':=Sigma)) ||
     apply (var_index_neq_mem (Sigma':=Sigma)));
    cbn;
    inversion 1.

  Hint Extern 1 (@member_index _ _ (abstraction_types App.Sigma) _ <>
                 @member_index _ _ (abstraction_types App.Sigma) _) => vars_distinct.
  Hint Extern 1 (@member_index _ _ (mem_types App.Sigma) _ <>
                 @member_index _ _ (mem_types App.Sigma) _) => vars_distinct.

  Definition no_wb_reader_conflict c wb :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Definition cacheI : Invariant App.Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      get mWriteBuffer m = get vWriteBuffer s /\
      cache_rep d (get vCache s) (get vDisk0 s) /\
      wb_rep (get vDisk0 s) (get vWriteBuffer s) (get vdisk s) /\
      no_wb_reader_conflict (get vCache s) (get vWriteBuffer s).

  (** a locking-like protocol, but true for any provable program
      due to the program semantics themselves *)
  Definition readers_locked tid (vd vd': DISK) :=
    (forall a v tid', vd a = Some (v, Some tid') ->
                 tid <> tid' ->
                 vd' a = Some (v, Some tid')).

  Instance readers_locked_preorder tid : PreOrder (readers_locked tid).
  Proof.
    constructor; hnf; intros;
      unfold readers_locked; eauto.
  Qed.

  (* not sure whether to say this about vDisk0, vDisk, or both *)
  Definition cacheR (tid:TID) : Relation App.Sigma :=
    fun s s' =>
      let vd := get vDisk0 s in
      let vd' := get vDisk0 s' in
      same_domain vd vd' /\
      readers_locked tid vd vd'.

  Hint Resolve same_domain_preorder same_domain_refl.
  Hint Resolve readers_locked_preorder.

  Instance and_preorder A (R1 R2: Relation A)
           (p1: PreOrder R1) (p2: PreOrder R2)
    : PreOrder (fun a a' =>
                  R1 a a' /\
                  R2 a a').
  Proof.
    destruct p1, p2.
    constructor; hnf; intuition eauto.
  Qed.

  Theorem cacheR_preorder : forall tid,
      PreOrder (cacheR tid).
  Proof.
    unfold cacheR; intros.
    apply and_preorder; constructor; hnf; intros.
    apply same_domain_preorder.
    eapply same_domain_preorder; eauto.
    apply readers_locked_preorder.
    eapply readers_locked_preorder; eauto.
  Qed.

  Definition delta : Protocol App.Sigma :=
    defProtocol cacheI cacheR cacheR_preorder.

End CacheProtocol.

Module Type CacheSubProtocol.
  Declare Module App:GlobalProtocol.
  Declare Module Proj:CacheProj App.

  Module CProto := CacheProtocol App Proj.

  Parameter protocolProj:SubProtocol App.delta CProto.delta.

  Parameter protocolRespectsPrivateVars :
    forall tid s s',
      guar CProto.delta tid s s' ->
      modified [( CProto.vCache; CProto.vDisk0 )] s s' ->
      guar App.delta tid s s'.

  Parameter invariantRespectsPrivateVars :
    forall d m s d' m' s',
      invariant App.delta d m s ->
      modified [( CProto.vCache; CProto.vDisk0 )] s s' ->
      modified [( CProto.mCache )] m m' ->
      invariant CProto.delta d' m' s' ->
      invariant App.delta d' m' s'.

End CacheSubProtocol.

Module ConcurrentCache (C:CacheSubProtocol).
  Import C.
  Import C.CProto.

  (* abstraction helpers *)

  Definition modify_cache (up: Cache -> Cache) :=
    c <- Get mCache;
      _ <- Assgn mCache (up c);
      _ <- var_update vCache up;
      Ret tt.

  Definition modify_wb (up: WriteBuffer -> WriteBuffer) :=
    wb <- Get mWriteBuffer;
      _ <- Assgn mWriteBuffer (up wb);
      _ <- var_update vWriteBuffer up;
      Ret tt.

  (** safe read: returns None upon cache miss  *)
  Definition cache_maybe_read a :=
    c <- Get mWriteBuffer;
      match wb_val c a with
      | Some v => Ret (Some v)
      | None =>
        c <- Get mCache;
          Ret (cache_val c a)
      end.

  (** Prepare to fill address a, locking the address and marking it
  invalid in the cache to signal the lock to concurrent threads. *)
  Definition prepare_fill a :=
    tid <- GetTID;
      _ <- StartRead_upd a;
      (* note that no updates to Disk are needed since the readers are
    hidden *)
      _ <- var_update vDisk0
        (fun vd => add_reader vd a tid);
      _ <- modify_cache (fun c => cache_add c a Invalid);
      Ret tt.

  Definition cache_fill a :=
    _ <- prepare_fill a;
      _ <- Yield a;
      v <- FinishRead_upd a;
      _ <- var_update vDisk0
        (fun vd => remove_reader vd a);
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      Ret v.

  (** buffer a new write: fails (returns false) if the write overlaps
  with the address being read filled *)
  Definition cache_try_write a v :=
    c <- Get mCache;
      match cache_get c a with
      | Invalid => Ret false
      | _ =>
        _ <- modify_wb (fun wb => wb_write wb a v:WriteBuffer);
          _ <- var_update vdisk
            (fun vd => upd vd a v);
          Ret true
      end.

  Fixpoint cache_add_all (c: Cache) (entries: list (addr * valu)) : Cache :=
    match entries with
    | nil => c
    | (a, v) :: es => cache_add_all (cache_add c a (Dirty v)) es
    end.

  (** commit all the buffered writes into the global cache

    safety is provided by the invariant no_wb_reader_conflict enforced
    by cache_write's checks *)
  Definition cache_commit :=
    c <- Get mCache;
      wb <- Get mWriteBuffer;
      _ <- modify_cache (fun c => cache_add_all c (wb_writes wb));
      _ <- var_update vDisk0 (fun d => upd_buffered_writes d (wb_writes wb));
      _ <- modify_wb (fun _ => emptyWriteBuffer);
      Ret tt.

  (** abort all buffered writes, restoring vDisk0 *)
  Definition cache_abort :=
    _ <- modify_wb (fun _ => emptyWriteBuffer);
      _ <- GhostUpdate (fun s =>
                         let vd' := hide_readers (get vDisk0 s) in
                         set vdisk vd' s);
      Ret tt.

  Definition cache_read a :=
    opt_v <- cache_maybe_read a;
      match opt_v with
      | Some v => Ret (Some v)
      | None => _ <- cache_abort;
                 v <- cache_fill a;
                 Ret None
      end.

  Definition cache_write a v :=
    ok <- cache_try_write a v;
      if ok then
        Ret true
      else
        _ <- cache_abort;
      _ <- Yield a;
      Ret false.

  (** TODO: need to write all addresses into cache from WriteBuffer,
  evict from cache (writing if necessary), and then note in place of
  the writebuffer that rollback is no longer possible *)
  (* now that this is all addresses, it might just basically be
  cache_commit *)
  Definition cache_writeback :=
    wb <- Get mWriteBuffer;
      Ret tt.

  (* start of automation *)

  Lemma unfold_invariant : forall d m s,
      invariant delta d m s ->
      ltac:(let t := eval simpl in (invariant delta d m s) in
                let t := eval unfold cacheI in t in
                    exact t).
  Proof.
    auto.
  Qed.

  Lemma unfold_protocol : forall tid s s',
      guar delta tid s s' ->
      ltac:(let t := eval simpl in (guar delta tid s s') in
                let t := eval unfold cacheR in t in
                    exact t).
  Proof.
    eauto.
  Qed.

  Lemma protocol_proj_invariant {d m s} :
      invariant App.delta d m s ->
      invariant delta d m s.
  Proof.
    apply protocolProj; auto.
  Qed.

  Lemma protocol_proj_rely {tid s s'} :
      rely App.delta tid s s' ->
      rely delta tid s s'.
  Proof.
    apply (rely_subprotocol protocolProj); auto.
  Qed.

  Ltac sub_protocol :=
    match goal with
    | [ H: invariant App.delta _ _ _ |- _ ] =>
      learn that (protocol_proj_invariant H)
    | [ H: rely App.delta _ _ _ |- _ ] =>
      learn that (protocol_proj_rely H)
    end.

  Ltac learn_protocol :=
    match goal with
    | [ H: invariant delta _ _ _ |- _ ] =>
      learn that (unfold_invariant H)
    | [ H: guar delta _ _ _ |- _ ] =>
      learn that (unfold_protocol H)
    end.

  Ltac prove_protocol :=
    match goal with
    | [ |- guar delta ?tid _ _ ] =>
      simpl; unfold cacheR
    | [ |- invariant delta _ _ _ ] =>
      simpl; unfold cacheI
    end.

  Ltac descend :=
    match goal with
    | [ |- _ /\ _ ] => split
    | [ |- exists (_:unit), _ ] => exists tt
    end.

  Ltac reduce_hlist :=
    match goal with
    | [ |- context[get _ (set _ _ _) ] ] =>
      progress repeat rewrite ?get_set, ?get_set_other by auto
    end.

  Lemma cache_val_mem {m: memory App.Sigma} {s: abstraction App.Sigma} :
      get mCache m = get vCache s ->
      cache_val (get mCache m) = cache_val (get vCache s).
  Proof.
    congruence.
  Qed.

  Lemma cache_get_mem {m: memory App.Sigma} {s: abstraction App.Sigma} :
      get mCache m = get vCache s ->
      cache_get (get mCache m) = cache_get (get vCache s).
  Proof.
    congruence.
  Qed.

  Ltac replace_mem_val :=
    match goal with
    | [ H: get mWriteBuffer ?m = get vWriteBuffer _,
           H': context[ get mWriteBuffer ?m ] |- _ ] =>
      lazymatch type of H' with
      | Learnt => fail
      | _ => rewrite H in H'
      end
    | [ H: get mWriteBuffer ?m = get vWriteBuffer _
        |- context[ get mWriteBuffer ?m ] ] =>
      rewrite H
    | [ H: get mCache ?m = get vCache _,
           H': context[ cache_val (get mCache ?m) ] |- _ ] =>
      rewrite (cache_val_mem H) in H'
    | [ H: get mCache ?m = get vCache _,
           H': context[ cache_get (get mCache ?m) ] |- _ ] =>
      rewrite (cache_get_mem H) in H'
    end.

  Ltac pick_opt_condition :=
    let break H :=
      destruct H; destruct_ands; try congruence;
      let n := numgoals in guard n <= 1 in
    match goal with
    | [ H: (@eq (option _) _ _ /\ _) \/
           (@eq (option _) _ _ /\ _) |- _ ] =>
      break H
    | [ H: (@eq (option _) _ _) \/
           (@eq (option _) _ _ /\ _) |- _ ] =>
      break H
    | [ H: (@eq (option _) _ _ /\ _) \/
           (@eq (option _) _ _) |- _ ] =>
      break H
    end.

  Hint Resolve
       modified_refl
       one_more_modified_in HHere HLater
       modified_single_var : modified.

  Ltac solve_modified :=
    match goal with
    | |- modified _ _ _ =>
      solve [ auto with modified ]
    end.

  (* lightweight intuition *)
  Ltac expand_propositional t :=
    repeat match goal with
           | [ H: ?P -> _ |- _ ] =>
             lazymatch type of P with
             | Prop => let ant := fresh in
                   assert P as ant by t;
                   specialize (H ant);
                   clear ant
             end
           | [ H: _ /\ _ |- _ ] =>
             destruct H
           end.

  Ltac simp_hook := fail.

  Ltac simplify_step :=
    match goal with
    | [ |- forall _, _ ] => intros
    | _ => sub_protocol
    | _ => learn_protocol
    | _ => time "deex" deex
    | _ => time "expand_propositional" progress expand_propositional trivial
    | _ => inv_opt
    | _ => pick_opt_condition
    | _ => progress subst
    | _ => replace_mem_val
    | _ => time "reduce_hlist" reduce_hlist
    | _ => simp_hook
    | _ => descend
    | _ => prove_protocol
    | _ => time "solve_modified" solve_modified
    end.

  Ltac finish := time "finish"
                      lazymatch goal with
                      | [ |- valid _ _ _ _ ] => idtac
                      | _ => eauto;
                            try solve [simpl (mem_types _) in *;
                                       simpl (abstraction_types _) in *;
                                       congruence]
                      end.

  Ltac simplify :=
    repeat (time "simplify_step" simplify_step).

  (* hook up new finish and simplify to existing hoare tactic; this
    isn't clean, need better extensibility *)

  Ltac step_simplifier ::= simplify.
  Ltac step_finisher ::= finish.

  (* prove hoare specs *)

  Section SpecLemmas.

    Lemma disk_no_reader : forall d c vd0 wb vd a v,
      cache_rep d c vd0 ->
      wb_rep vd0 wb vd ->
      cache_get c a = Missing ->
      wb_get wb a = WbMissing ->
      vd a = Some v ->
      d a = Some (v, None).
    Proof.
      intros.
      specialize (H a).
      specialize (H0 a).
      simpl_match.
      destruct matches in *;
        intuition auto;
        repeat deex;
        eauto || congruence.
    Qed.

    Lemma no_wb_reader_conflict_stable_invalidate : forall c wb a,
        no_wb_reader_conflict c wb ->
        wb_get wb a = WbMissing ->
        no_wb_reader_conflict (cache_add c a Invalid) wb.
    Proof.
      unfold no_wb_reader_conflict; intros.
      destruct (nat_dec a a0); subst;
        autorewrite with cache in *;
        eauto.
    Qed.

    Lemma no_wb_reader_conflict_stable_write : forall c wb a v,
        cache_get c a <> Invalid ->
        no_wb_reader_conflict c wb ->
        no_wb_reader_conflict c (wb_write wb a v).
    Proof.
      unfold no_wb_reader_conflict; intros.
      destruct (nat_dec a a0); subst;
        rewrite ?wb_get_write_eq, ?wb_get_write_neq
        in * by auto;
        eauto || congruence.
    Qed.

    Lemma same_domain_add_reader : forall d a tid,
        same_domain d (add_reader d a tid).
    Proof.
      unfold same_domain, subset, add_reader; split;
        intros;
        destruct (nat_dec a a0); subst;
          destruct matches in *;
          autorewrite with upd in *;
          eauto.
    Qed.

    Lemma same_domain_remove_reader : forall d a,
        same_domain d (remove_reader d a).
    Proof.
      unfold same_domain, subset, remove_reader; split;
        intros;
        destruct (nat_dec a a0); subst;
          destruct matches in *;
          autorewrite with upd in *;
          eauto.
    Qed.

    Lemma readers_locked_add_reader : forall tid tid' vd a v,
        vd a = Some (v, None) ->
        readers_locked tid vd (add_reader vd a tid').
    Proof.
      unfold readers_locked, add_reader; intros.
      destruct (nat_dec a a0); subst;
        simpl_match;
        autorewrite with upd;
        congruence.
    Qed.

    Lemma readers_locked_remove_reading : forall tid vd a v,
        vd a = Some (v, Some tid) ->
        readers_locked tid vd (remove_reader vd a).
    Proof.
      unfold readers_locked, remove_reader; intros.
      destruct (nat_dec a a0); subst;
        simpl_match;
        autorewrite with upd;
        eauto || congruence.
    Qed.

    Theorem wb_rep_stable_write : forall d wb vd a v0 v,
        wb_rep d wb vd ->
        (* a is in domain *)
        vd a = Some v0 ->
        wb_rep d (wb_write wb a v) (upd vd a v).
    Proof.
      unfold wb_rep; intros.
      specialize (H a0).
      destruct (nat_dec a a0); subst;
        rewrite ?wb_get_write_eq, ?wb_get_write_neq by auto;
        autorewrite with upd;
        eauto.

      destruct matches in *|- ;
        intuition eauto.
    Qed.

  End SpecLemmas.

  Theorem modify_cache_ok : forall (up : Cache -> Cache),
      SPEC App.delta, tid |-
              {{ (_:unit),
               | PRE d m s_i s: get mCache m = get vCache s
               | POST d' m' s_i' s' r:
                   s' = set vCache (up (get vCache s)) s /\
                   m' = set mCache (up (get mCache m)) m /\
                   d' = d /\
                   s_i' = s_i
              }} modify_cache up.
  Proof.
    hoare.
  Qed.

  Hint Extern 1 {{ modify_cache _; _ }} => apply modify_cache_ok : prog.

  Theorem modify_wb_ok : forall (up: WriteBuffer -> WriteBuffer),
      SPEC App.delta, tid |-
              {{ (_:unit),
               | PRE d m s_i s: get mWriteBuffer m = get vWriteBuffer s
               | POST d' m' s_i' s' r:
                   s' = set vWriteBuffer (up (get vWriteBuffer s)) s /\
                   m' = set mWriteBuffer (up (get mWriteBuffer m)) m /\
                   d' = d /\
                   s_i' = s_i
              }} modify_wb up.
  Proof.
    hoare.
  Qed.

  Hint Extern 1 {{ modify_wb _; _ }} => apply modify_wb_ok : prog.

  Definition sumboolProof P Q (p: {P} + {Q}) : if p then P else Q.
  Proof.
    destruct p; auto.
  Defined.

  Ltac prove_nat_neq :=
    match goal with
    | |- ?n <> ?m =>
      exact (sumboolProof (PeanoNat.Nat.eq_dec n m))
    end.

  Hint Extern 2 (member_index _ <> member_index _) => simpl; prove_nat_neq.

  Hint Resolve wb_val_vd cache_val_vd cache_val_no_reader wb_val_none.

  Opaque mem_types abstraction_types.

  Lemma Some_inv : forall A (v v': A),
      v = v' ->
      Some v = Some v'.
  Proof.
    congruence.
  Qed.

  Hint Resolve Some_inv.

  Theorem cache_maybe_read_ok : forall a,
      SPEC App.delta, tid |-
              {{ v0,
               | PRE d m s_i s: invariant delta d m s /\
                               get vdisk s a = Some v0
               | POST d' m' s_i' s' r:
                   invariant delta d m s /\
                   s' = s /\
                   m' = m /\
                   d' = d /\
                   s_i' = s_i /\
                   (r = Some v0 \/
                    r = None /\
                    cache_get (get vCache s') a = Missing)
              }} cache_maybe_read a.
  Proof.
    hoare.
    (* requires case analysis on cache_val at a *)
    admit.
  Admitted.

  Hint Extern 1 {{cache_maybe_read _; _}} => apply cache_maybe_read_ok : prog.

  Hint Resolve
       disk_no_reader
       no_wb_reader_conflict_stable_invalidate
       same_domain_add_reader
       readers_locked_add_reader.

  Hint Resolve wb_get_val_missing.

  Theorem wb_cache_val_none_vd0 : forall d vd0 vd c wb a v,
      cache_rep d c vd0 ->
      wb_rep vd0 wb vd ->
      vd a = Some v ->
      cache_get c a = Missing ->
      wb_get wb a = WbMissing ->
      vd0 a = Some (v, None).
  Proof.
    intros.
    pose proof (wb_val_none _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    deex.
    pose proof (cache_val_no_reader _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    congruence.
  Qed.

  Lemma add_reader_eq : forall d a tid v rdr,
      d a = Some (v, rdr) ->
      add_reader d a tid a = Some (v, Some tid).
  Proof.
    unfold add_reader; intros.
    simpl_match; autorewrite with upd; auto.
  Qed.

  Lemma wb_add_reader : forall vd0 wb vd a tid v,
      wb_rep vd0 wb vd ->
      wb_get wb a = WbMissing ->
      vd a = Some v ->
      add_reader vd0 a tid a = Some (v, Some tid).
  Proof.
    unfold wb_rep; intros.
    specialize (H a).
    simpl_match.
    destruct matches in *; intuition; try deex.
    assert (w0 = v) by congruence; subst.
    eapply add_reader_eq; eauto.
  Qed.

  Hint Resolve wb_add_reader.
  Hint Resolve readers_locked_add_reader wb_cache_val_none_vd0.

  Theorem prepare_fill_ok : forall a,
      SPEC App.delta, tid |-
              {{ v0,
               | PRE d m s_i s:
                   invariant App.delta d m s /\
                   cache_get (get vCache s) a = Missing /\
                   (* XXX: not sure exactly why this is a requirement,
                   but it comes from no_wb_reader_conflict *)
                   wb_get (get vWriteBuffer s) a = WbMissing /\
                   get vdisk s a = Some v0 /\
                   guar App.delta tid s_i s
               | POST d' m' s_i' s' _:
                   invariant App.delta d' m' s' /\
                   get vDisk0 s' a = Some (v0, Some tid) /\
                   get vDisk0 s' = add_reader (get vDisk0 s) a tid /\
                   modified [( vCache; vDisk0 )] s s' /\
                   guar App.delta tid s_i' s'
              }} prepare_fill a.
  Proof.
    hoare.
    eexists; simplify; finish.

    hoare.
    eapply invariantRespectsPrivateVars; eauto;
      try solve_modified.

    simplify; finish;
      (let n := numgoals in guard n = 2);
      match goal with
      (* cache_rep stable when adding reader *)
      | [ |- cache_rep (upd _ _ _)
                      (cache_add _ _ _)
                      (add_reader _ _ _) ] => admit
      (* wb_rep insensitive to readers *)
      | [ |- wb_rep (add_reader _ _ _) _ _ ] => admit
      end.

    eapply guar_preorder; [ eassumption | ].
    eapply protocolRespectsPrivateVars; eauto;
      try solve_modified.
    simplify; finish.
  Admitted.

  Hint Extern 1 {{ prepare_fill _; _ }} => apply prepare_fill_ok : prog.

  Lemma others_readers_locked_reading : forall tid vd vd' a v,
      others readers_locked tid vd vd' ->
      vd a = Some (v, Some tid) ->
      vd' a = Some (v, Some tid).
  Proof.
    unfold others, readers_locked; intros; deex.
    eauto.
  Qed.

  Lemma others_rely_readers_locked : forall tid s s',
      others (guar delta) tid s s' ->
      others readers_locked tid (get vDisk0 s) (get vDisk0 s').
  Proof.
    simpl; unfold cacheR, others; intros; deex; eauto.
  Qed.

  Lemma rely_read_lock : forall tid (s s': abstraction App.Sigma) a v,
      get vDisk0 s a = Some (v, Some tid) ->
      rely delta tid s s' ->
      get vDisk0 s' a = Some (v, Some tid).
  Proof.
    unfold rely; intros.
    induction H0; eauto.
    eauto using others_readers_locked_reading,
    others_rely_readers_locked.
  Qed.

  Ltac simp_hook ::=
       match goal with
       | [ Hrely: rely delta ?tid ?s _,
              H: get vDisk0 ?s _ = Some (_, Some ?tid) |- _ ] =>
         learn that (rely_read_lock H Hrely)
       end.

  Hint Resolve
       same_domain_remove_reader
       readers_locked_remove_reading.

  Lemma cache_rep_disk_val : forall d c vd v rdr a,
      cache_rep d c vd ->
      vd a = Some (v, rdr) ->
      (exists v', d a = Some (v', rdr)).
  Proof.
    intros.
    specialize (H a).
    destruct matches in *; intuition auto; repeat deex;
      try match goal with
          | [ H: ?v = Some (_, ?rdr), H': ?v = Some (_, ?rdr') |- _ ] =>
            assert (rdr = rdr') by congruence
          end; subst;
        eauto.
    congruence.
  Qed.

  Lemma or_distr_impl : forall (P Q R:Prop),
      (P -> R) ->
      (Q -> R) ->
      (P \/ Q -> R).
  Proof.
    tauto.
  Qed.

  Theorem cache_fill_ok : forall a,
      SPEC App.delta, tid |-
              {{ v0,
               | PRE d m s_i s:
                   invariant App.delta d m s /\
                   cache_get (get vCache s) a = Missing /\
                   (* XXX: not sure exactly why this is a requirement,
                   but it comes from no_wb_reader_conflict *)
                   wb_get (get vWriteBuffer s) a = WbMissing /\
                   get vdisk s a = Some v0 /\
                   guar App.delta tid s_i s
               | POST d' m' s_i' s' _:
                   invariant App.delta d' m' s' /\
                   (exists (s1 s2: abstraction App.Sigma),
                       modified [(vCache; vDisk0)] s s1 /\
                       rely App.delta tid s1 s2 /\
                       modified [(vCache; vDisk0)] s2 s') /\
                   guar delta tid s_i' s'
              }} cache_fill a.
  Proof.
    hoare.
    eexists; simplify; finish.
    hoare.
    assert (get vdisk s = get vdisk s0). {
      match goal with
      | [ H: modified _ s s0 |- _ ] =>
        apply H
      end.

      rewrite hin_index_vars; simpl.
      now repeat (apply or_distr_impl; [ vars_distinct | ]).
    }

    assert (exists v, d1 a = Some (v, Some tid)). {
      eauto using cache_rep_disk_val.
      admit.
    }

    deex.
    eexists; simplify; finish.

    hoare.
    eapply invariantRespectsPrivateVars; eauto;
      simplify; finish;
        match goal with
        (* cache_rep stable when adding reader *)
        | [ |- cache_rep (upd _ _ _)
                        (cache_add _ _ _)
                        (remove_reader _ _) ] => admit
        (* wb_rep insensitive to readers *)
        | [ |- wb_rep (remove_reader _ _) _ _ ] => admit
        (* clean addresses irrelevant *)
        | [ |- no_wb_reader_conflict (cache_add _ _ _) _ ] => admit
        | [ |- exists _, _ ] => idtac
        end.

    exists s0, s1.
    intuition eauto; solve_modified.
    match goal with
    | [ |- readers_locked _ _ (remove_reader _ _) ] => admit
    end.
  Admitted.

  Hint Extern 1 {{cache_fill _; _}} => apply cache_fill_ok.

  Hint Resolve upd_eq.
  Hint Resolve wb_rep_stable_write.

  Lemma cache_not_invalid_1 : forall c a v,
      cache_get c a = Clean v ->
      cache_get c a <> Invalid.
  Proof. congruence. Qed.

  Lemma cache_not_invalid_2 : forall c a v,
      cache_get c a = Dirty v ->
      cache_get c a <> Invalid.
  Proof. congruence. Qed.

  Lemma cache_not_invalid_3 : forall c a,
      cache_get c a = Missing ->
      cache_get c a <> Invalid.
  Proof. congruence. Qed.

  Hint Resolve no_wb_reader_conflict_stable_write.
  Hint Resolve
       cache_not_invalid_1
       cache_not_invalid_2
       cache_not_invalid_3.


  Theorem cache_try_write_ok : forall a v,
      SPEC App.delta, tid |-
              {{ v0,
               | PRE d m s_i s:
                   invariant delta d m s /\
                   get vdisk s a = Some v0
               | POST d' m' s_i' s' r:
                   invariant delta d' m' s' /\
                   (r = true ->
                    get vdisk s' = upd (get vdisk s) a v /\
                    get vDisk0 s' = get vDisk0 s /\
                    modified [(vWriteBuffer; vdisk)] s s') /\
                   (r = false -> s' = s) /\
                   s_i' = s_i
              }} cache_try_write a v.
  Proof.
    hoare.
  Qed.

  Hint Extern 1 {{cache_try_write _ _; _}} => apply cache_try_write_ok : prog.

  Hint Resolve wb_rep_empty.

  Theorem cache_commit_ok :
      SPEC App.delta, tid |-
              {{ (_:unit),
               | PRE d m s_i s:
                   invariant delta d m s
               | POST d' m' s_i' s' r:
                   invariant delta d' m' s' /\
                   hide_readers (get vDisk0 s') = get vdisk s /\
                   get vdisk s' = get vdisk s /\
                   guar delta tid s s' /\
                   s_i' = s_i
              }} cache_commit.
  Proof.
    hoare.
  Admitted.

  Lemma wb_rep_id : forall vd,
      wb_rep vd emptyWriteBuffer (hide_readers vd).
  Proof.
    unfold wb_rep, hide_readers; intros.
    rewrite wb_get_empty.
    destruct matches.
  Qed.

  Lemma no_wb_reader_conflict_empty : forall c,
      no_wb_reader_conflict c emptyWriteBuffer.
  Proof.
    unfold no_wb_reader_conflict; intros;
      rewrite wb_get_empty;
      auto.
  Qed.

  Hint Resolve wb_rep_id no_wb_reader_conflict_empty.

  Theorem cache_abort_ok :
    SPEC App.delta, tid |-
  {{ (_:unit),
   | PRE d m s_i s:
       invariant delta d m s
   | POST d' m' s_i' s' _:
       invariant delta d' m' s' /\
       get vdisk s' = hide_readers (get vDisk0 s) /\
       modified [(vWriteBuffer; vdisk)] s s' /\
       get vDisk0 s' = get vDisk0 s /\
       get vCache s' = get vCache s /\
       get vWriteBuffer s' = emptyWriteBuffer /\
       guar delta tid s s' /\
       s_i' = s_i
  }} cache_abort.
  Proof.
    hoare.
  Qed.

  Hint Extern 1 {{cache_abort; _}} => apply cache_abort_ok : prog.

  Lemma hide_readers_eq : forall (d: DISK) a v,
      d a = Some v ->
      hide_readers d a = Some (fst v).
  Proof.
    unfold hide_readers; intros; simpl_match.
    destruct v; auto.
  Qed.

  Lemma hide_readers_eq' : forall (d: DISK) a v,
      hide_readers d a = Some v ->
      (exists v0, d a = Some v0).
  Proof.
    unfold hide_readers; intros;
      destruct (d a).
    eauto.
    congruence.
  Qed.

  Lemma same_domain_hide_readers : forall d d',
      same_domain (hide_readers d) (hide_readers d') ->
      same_domain d d'.
  Proof.
    unfold same_domain, subset; intuition eauto.
    specialize (H0 _ _ (hide_readers_eq _ _ H)); deex.
    eapply hide_readers_eq'; eauto.

    specialize (H1 _ _ (hide_readers_eq _ _ H)); deex.
    eapply hide_readers_eq'; eauto.
  Qed.

  Hint Resolve wb_rep_same_domain.

  Lemma same_domain_same_vdisk : forall vd0 wb vd vd0' wb' vd',
      wb_rep vd0 wb vd ->
      wb_rep vd0' wb' vd' ->
      vd = vd' ->
      same_domain vd0 vd0'.
  Proof.
    intros.
    subst vd'.
    apply same_domain_hide_readers.
    transitivity vd; eauto.
    symmetry.
    eauto.
  Qed.

  Hint Resolve same_domain_same_vdisk.

  Theorem cache_read_ok : forall a,
      SPEC App.delta, tid |-
              {{ v,
               | PRE d m s_i s:
                   invariant App.delta d m s /\
                   get vdisk s a = Some v /\
                   guar App.delta tid s_i s
               | POST d' m' s_i' s' r:
                   invariant App.delta d' m' s' /\
                   (r = None
                    (* Need to guarantee a rely step, though actually a reader
                    was added/removed. For the actual global protocol, this
                    should still be a rely step, since the readers belong to the
                    cache and others cannot rely on them. *) \/
                    r = Some v /\
                    get vdisk s' = get vdisk s) /\
                   guar App.delta tid s_i' s'
              }} cache_read a.
  Proof.
    hoare.
    eexists; simplify; finish.
    hoare.

    (* TODO: need to produce value in disk using same_domain or
    something *)
    eexists; simplify; finish.
    admit. (* XXX: why do we only have invariant delta and no modified
    restrictions? *)
    replace (get vWriteBuffer s0) with emptyWriteBuffer by auto.
    apply wb_get_empty.
    admit. (* needed to find get vdisk s1 a first *)

    eapply guar_preorder; eauto.
    eapply protocolRespectsPrivateVars; eauto.
    admit. (* XXX: same as above, don't have modified between {m,s} and
    {m0,s0} *)

    step.
    (* XXX: why is there only guar delta here? *)
    eapply protocolRespectsPrivateVars; eauto.
    admit.
  Admitted.

  Theorem cache_write_ok : forall a v,
      SPEC App.delta, tid |-
              {{ v0,
               | PRE d m s_i s:
                   invariant App.delta d m s /\
                   get vdisk s a = Some v0 /\
                   guar App.delta tid s_i s
               | POST d' m' s_i' s' r:
                   invariant delta d' m' s' /\
                   (* same as read - what to guarantee for false? *)
                   (r = true ->
                    get vdisk s' = upd (get vdisk s) a v) /\
                   modified [(vWriteBuffer; vdisk)] s s' /\
                   s_i' = s_i
              }} cache_write a v.
  Proof.
    hoare.
    eexists; simplify; finish.
    hoare.
    admit. (* TODO: actually, this needs to come from an assumption that the
    invariant is satisfied if we abort *)

    admit. (* TODO: not strong enough to have guar App.delta s_i s at all times
    - want to know what get vDisk0 s corresponds in some way to get vdisk s_i
    (both under current disk?) *)
  Admitted.

  Section ExampleProgram.

    Definition copy a a' :=
      opt_v <- cache_read a;
        match opt_v with
        | None => Ret false
        | Some v => ok <- cache_write a' v;
                     Ret ok
        end.

    Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.
    Hint Extern 1 {{cache_write _ _; _}} => apply cache_write_ok : prog.

    Theorem copy_ok : forall a a',
        SPEC App.delta, tid |-
                {{ v v0,
                 | PRE d m s_i s:
                     invariant App.delta d m s /\
                     get vdisk s a = Some v /\
                     get vdisk s a' = Some v0 /\
                     guar App.delta tid s_i s
                 | POST d' m' s_i' s' r:
                     invariant App.delta d' m' s' /\
                      (r = true ->
                      get vdisk s' = upd (get vdisk s) a' v) /\
                     guar App.delta tid s_i' s'
                }} copy a a'.
    Proof.
      hoare.
      eexists; simplify; finish.

      hoare.
      eexists; simplify; finish.
      (* need an econgruence *)
      replace (get vdisk s0); eauto.

      hoare.
      admit. (* insufficient guarantees when cache fails *)
      admit. (* insufficient guarantees when cache fails *)
    Admitted.

  End ExampleProgram.

(* note that this is, in theory, the entire public cache API *)
Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.
Hint Extern 1 {{cache_write _ _; _}} => apply cache_write_ok : prog.

End ConcurrentCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ) ("delta'" . (?δ (Br . Bl) ?')) ("Sigma'" . (?Σ (Br . Bl) ?'))) *)
(* End: *)