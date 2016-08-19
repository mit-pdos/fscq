Require Import CoopConcur.
Require Import CoopConcurAuto.
Import RelationClasses.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Require Import FunctionalExtensionality.
Import List.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.
Require Import WriteBufferSet.

Module Type GlobalState.
  Parameter Sigma:State.
End GlobalState.

Definition Sigma := defState
                  [Cache; WriteBuffer]
                  [Cache; WriteBuffer; DISK; Disk].

Module Type CacheProj (St:GlobalState).
  Parameter stateProj:StateProj St.Sigma Sigma.
End CacheProj.

Module MakeCacheProtocol (St:GlobalState) (Proj:CacheProj St).

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

  Hint Extern 1 (@member_index _ _ (abstraction_types St.Sigma) _ <>
                 @member_index _ _ (abstraction_types St.Sigma) _) => vars_distinct.
  Hint Extern 1 (@member_index _ _ (mem_types St.Sigma) _ <>
                 @member_index _ _ (mem_types St.Sigma) _) => vars_distinct.

  Definition no_wb_reader_conflict c wb :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Definition cacheI : Invariant St.Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      get mWriteBuffer m = get vWriteBuffer s /\
      cache_rep d (get vCache s) (get vDisk0 s) /\
      wb_rep (get vDisk0 s) (get vWriteBuffer s) (get vdisk s) /\
      no_wb_reader_conflict (get vCache s) (get vWriteBuffer s).

  (* not sure whether to say this about vDisk0, vDisk, or both *)
  Definition cacheR (tid:TID) : Relation St.Sigma :=
    fun s s' =>
      let vd := get vDisk0 s in
      let vd' := get vDisk0 s' in
      same_domain vd vd'.

  Hint Resolve same_domain_preorder same_domain_refl.

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
    constructor; hnf; intros.
    apply same_domain_preorder.
    eapply same_domain_preorder; eauto.
  Qed.

  Definition delta : Protocol St.Sigma :=
    defProtocol cacheI cacheR cacheR_preorder.

End MakeCacheProtocol.

Module Type GlobalProtocol.
  Declare Module St : GlobalState.
  Definition Sigma := St.Sigma.
  Parameter delta:Protocol Sigma.
End GlobalProtocol.

Module Type CacheSubProtocol.
  Declare Module App:GlobalProtocol.
  Declare Module Proj:CacheProj App.

  Module CacheProtocol := MakeCacheProtocol App Proj.

  Parameter protocolProj:SubProtocol App.delta CacheProtocol.delta.

  Parameter protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.

  Parameter invariantRespectsPrivateVars :
    forall d m s d' m' s',
      invariant App.delta d m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' m' s' ->
      invariant App.delta d' m' s'.

End CacheSubProtocol.

Module MakeConcurrentCache (C:CacheSubProtocol).
  Import C.
  Import C.CacheProtocol.

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

  Definition finish_fill a :=
    v <- FinishRead_upd a;
      _ <- var_update vDisk0
        (fun vd => remove_reader vd a);
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      Ret v.

  (** buffer a new write: fails (returns false) if the write overlaps
  with the address being read filled *)
  Definition cache_write a v :=
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
    wb <- Get mWriteBuffer;
      match wb_get wb a  with
      | Written v => Ret (Some v)
      | WbMissing =>
        c <- Get mCache;
         match cache_get c a with
         | Clean v => Ret (Some v)
         | Dirty v => Ret (Some v)
         | Invalid => v <- finish_fill a;
                       Ret (Some v)
         | Missing => _ <- prepare_fill a;
                       Ret None
         end
      end.

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

  Lemma guar_two_step : forall Sigma (delta: Protocol Sigma) tid s s' s'',
      guar delta tid s s' ->
      guar delta tid s' s'' ->
      guar delta tid s s''.
  Proof.
    intros.
    eapply guar_preorder; eauto.
  Qed.

  Hint Extern 5 (guar _ _ _ _) => eapply guar_two_step; [ eassumption | ].

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

    Theorem wb_rep_stable_write : forall d wb vd a v0 v,
        wb_rep d wb vd ->
        d a = Some (v0, None) ->
        wb_rep d (wb_write wb a v) (upd vd a v).
    Proof.
      unfold wb_rep; intros.
      specialize (H a0).
      destruct (nat_dec a a0); subst;
        rewrite ?wb_get_write_eq, ?wb_get_write_neq by auto;
        autorewrite with upd;
        eauto.
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

  Hint Resolve
       disk_no_reader
       no_wb_reader_conflict_stable_invalidate
       same_domain_add_reader.

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
  Hint Resolve wb_cache_val_none_vd0.

  Lemma add_reader_neq : forall d a tid a',
      a <> a' ->
      add_reader d a tid a' = d a'.
  Proof.
    unfold add_reader; intros.
    destruct matches;
      autorewrite with upd;
      auto.
  Qed.

  Lemma cache_rep_add_reader : forall d c vd a v0 rdr0 rdr,
      vd a = Some (v0, rdr0) ->
      cache_rep d c vd ->
      cache_rep (upd d a (v0, Some rdr))
                (cache_add c a Invalid)
                (add_reader vd a rdr).
  Proof.
    unfold cache_rep; intros.
    specialize (H0 a0).
    destruct (nat_dec a a0); subst;
      autorewrite with upd cache.
    erewrite add_reader_eq by eauto; eauto.

    destruct matches; simpl_match;
      rewrite add_reader_neq by auto;
      eauto.
  Qed.

  Hint Resolve cache_rep_add_reader.

  Lemma wb_rep_add_reader : forall d wb vd a v tid,
      vd a = Some v ->
      wb_get wb a = WbMissing ->
      wb_rep d wb vd ->
      wb_rep (add_reader d a tid) wb vd.
  Proof.
    unfold wb_rep; intros.
    specialize (H1 a0).
    destruct (nat_dec a a0); subst;
      destruct matches in *|-; simplify;
      erewrite ?add_reader_eq by eauto;
      rewrite ?add_reader_neq by auto;
      try simpl_match;
      eauto.
  Qed.

  Hint Resolve wb_rep_add_reader.

  Hint Resolve cache_add_get_eq.

  Theorem prepare_fill_ok : forall a,
      SPEC App.delta, tid |-
              {{ v0,
               | PRE d m s_i s:
                   invariant delta d m s /\
                   cache_get (get vCache s) a = Missing /\
                   (* XXX: not sure exactly why this is a requirement,
                   but it comes from no_wb_reader_conflict *)
                   wb_get (get vWriteBuffer s) a = WbMissing /\
                   get vdisk s a = Some v0
               | POST d' m' s_i' s' _:
                   invariant delta d' m' s' /\
                   get vDisk0 s' a = Some (v0, Some tid) /\
                   get vDisk0 s' = add_reader (get vDisk0 s) a tid /\
                   modified [( vCache; vDisk0 )] s s' /\
                   guar delta tid s s' /\
                   s_i' = s_i
              }} prepare_fill a.
  Proof.
    hoare.
    eexists; simplify; finish.
    hoare.
  Qed.

  Hint Extern 1 {{ prepare_fill _; _ }} => apply prepare_fill_ok : prog.

  Lemma cache_disk_val_invalid : forall d c vd a v,
      cache_rep d c vd ->
      cache_get c a = Invalid ->
      vd a = Some v ->
      d a = Some v.
  Proof.
    unfold cache_rep; intros.
    specialize (H a).
    simpl_match; repeat deex;
      congruence.
  Qed.

  Hint Resolve cache_disk_val_invalid.

  Lemma remove_reader_eq : forall d a v0 rdr0,
      d a = Some (v0, rdr0) ->
      remove_reader d a a = Some (v0, None).
  Proof.
    unfold remove_reader; intros;
      destruct matches;
      simpl_match;
      autorewrite with upd;
      auto.
  Qed.

  Lemma remove_reader_neq : forall d a a',
      a <> a' ->
      remove_reader d a a' = d a'.
  Proof.
    unfold remove_reader; intros;
      destruct matches;
      autorewrite with upd;
      auto.
  Qed.

  Lemma cache_rep_remove_reader : forall d c vd a v rdr0,
      vd a = Some (v, rdr0) ->
      cache_rep d c vd ->
      cache_rep (upd d a (v, None))
                (cache_add c a (Clean v))
                (remove_reader vd a).
  Proof.
    unfold cache_rep; intros.
    specialize (H0 a0).
    destruct (nat_dec a a0); subst;
      autorewrite with upd cache.
    - erewrite remove_reader_eq by eauto; eauto.
    - destruct matches; simpl_match;
        rewrite remove_reader_neq by auto;
        eauto.
  Qed.

  Hint Resolve cache_rep_remove_reader.

  Lemma wb_rep_remove_reader : forall d wb vd a v,
      vd a = Some v ->
      wb_rep d wb vd ->
      wb_rep (remove_reader d a) wb vd.
  Proof.
    unfold wb_rep; intros.
    specialize (H0 a0).
    destruct (nat_dec a a0); subst;
      destruct matches in *|-; simplify;
      erewrite ?remove_reader_eq by eauto;
      rewrite ?remove_reader_neq by auto;
      try simpl_match;
      eauto.
  Qed.

  Hint Resolve wb_rep_remove_reader.

  Lemma wb_rep_missing_vdisk_val : forall d wb vd a v rdr,
      wb_rep d wb vd ->
      wb_get wb a = WbMissing ->
      d a = Some (v, rdr) ->
      vd a = Some v.
  Proof.
    unfold wb_rep; intros.
    specialize (H a); repeat simpl_match; auto.
  Qed.

  Hint Resolve wb_rep_missing_vdisk_val.

  Lemma no_wb_reader_conflict_stable_fill : forall c wb a v,
      no_wb_reader_conflict c wb ->
      no_wb_reader_conflict (cache_add c a (Clean v)) wb.
  Proof.
    unfold no_wb_reader_conflict; intros.
    specialize (H a0).
    destruct (nat_dec a a0); subst;
      autorewrite with cache in *;
      (auto || congruence).
  Qed.

  Hint Resolve no_wb_reader_conflict_stable_fill.
  Hint Resolve same_domain_remove_reader.

  Theorem finish_fill_ok : forall a,
      SPEC App.delta, tid |-
                  {{ v0 tid',
                   | PRE d m s_i s:
                       invariant delta d m s /\
                       cache_get (get vCache s) a = Invalid /\
                       wb_get (get vWriteBuffer s) a = WbMissing /\
                       get vDisk0 s a = Some (v0, Some tid')
                   | POST d' m' s_i' s' r:
                       invariant delta d' m' s' /\
                       get vdisk s a = Some v0 /\
                       get vDisk0 s' = remove_reader (get vDisk0 s) a /\
                       modified [( vCache; vDisk0 )] s s' /\
                       guar delta tid s s' /\
                       r = v0 /\
                       s_i' = s_i
                  }} finish_fill a.
  Proof.
    hoare.
    do 2 eexists; simplify; finish.
    hoare.
  Qed.

  Hint Extern 1 {{finish_fill _; _}} => apply finish_fill_ok : prog.

  Hint Resolve same_domain_remove_reader.

  Lemma reading_disk_same : forall d c vd a v tid,
      cache_rep d c vd ->
      d a = Some (v, Some tid) ->
      vd a = Some (v, Some tid).
  Proof.
    unfold cache_rep; intros.
    specialize (H a); destruct matches in *;
      intuition auto;
      repeat deex;
      congruence.
  Qed.

  Lemma reading_virt_disk_same : forall d c vd a v tid,
      cache_rep d c vd ->
      vd a = Some (v, Some tid) ->
      d a = Some (v, Some tid).
  Proof.
    unfold cache_rep; intros.
    specialize (H a); destruct matches in *;
      intuition auto;
      repeat deex;
      congruence.
  Qed.

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

  Lemma cache_clean_vd0 : forall d c vd a v,
      cache_rep d c vd ->
      cache_get c a = Clean v ->
      vd a = Some (v, None).
  Proof.
    unfold cache_rep; intros.
    specialize (H a); simpl_match;
      intuition auto.
  Qed.

  Lemma cache_dirty_vd0 : forall d c vd a v,
      cache_rep d c vd ->
      cache_get c a = Dirty v ->
      vd a = Some (v, None).
  Proof.
    unfold cache_rep; intros.
    specialize (H a); simpl_match;
      intuition auto; repeat deex.
  Qed.

  Hint Resolve cache_clean_vd0.
  Hint Resolve cache_dirty_vd0.

  Lemma wb_cache_rep_missing : forall d c vd0 wb vd a v,
      cache_rep d c vd0 ->
      wb_rep vd0 wb vd ->
      vd a = Some v ->
      cache_get c a = Missing ->
      exists v0, vd0 a = Some (v0, None).
  Proof.
    intros.
    specialize (H a).
    specialize (H0 a).
    destruct matches in *;
      intuition auto; repeat deex;
        eauto;
        try congruence.
    assert (o = None) by congruence; subst; eauto.
  Qed.

  Theorem cache_write_ok : forall a v,
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
                   guar delta tid s s' /\
                   s_i' = s_i
              }} cache_write a v.
  Proof.
    hoare.

    match goal with
      | [ H: cache_get _ _ = Missing |- _ ] =>
        eapply wb_cache_rep_missing in H; eauto; deex
    end.

    eauto.
  Qed.

  Hint Extern 1 {{cache_write _ _; _}} => apply cache_write_ok : prog.

  Hint Resolve wb_rep_empty.

  Lemma cache_rep_add_upd : forall d c vd a v,
      (exists v0, d a = Some (v0, None)) ->
      cache_rep d c vd ->
      cache_rep d (cache_add c a (Dirty v)) (upd vd a (v, None)).
  Proof.
    unfold cache_rep; intros; deex.
    specialize (H0 a0).
    destruct (nat_dec a a0); subst; simpl;
      autorewrite with cache upd;
      eauto.
  Qed.

  Hint Resolve cache_rep_add_upd.

  Lemma wb_cache_states : forall d c vd0 wb vd a v,
      cache_rep d c vd0 ->
      wb_rep vd0 wb vd ->
      wb_get wb a = Written v ->
      exists v0, d a = Some (v0, None).
  Proof.
    intros.
    specialize (H a).
    specialize (H0 a).
    simpl_match; intuition auto;
      destruct matches in *;
      repeat deex;
      eauto;
      try congruence.
  Qed.

  Lemma fst_compose_add_empty_rdr :
    (fun (e: addr * valu) => fst (add_empty_rdr e)) = fst.
  Proof.
    extensionality e; simpl.
    destruct e; auto.
  Qed.

  Lemma NoDup_cons_iff_1 : forall A (l: list A) a,
      NoDup (a :: l) ->
      NoDup l.
  Proof.
    intros.
    eapply NoDup_cons_iff; eauto.
  Qed.

  Hint Resolve NoDup_cons_iff_1.

  Lemma cache_rep_add_all_upd : forall ws d c vd,
      NoDup (map fst ws) ->
      (forall a, In a (map fst ws) ->
            exists v0, d a = Some (v0, None)) ->
      cache_rep d c vd ->
      cache_rep d (cache_add_all c ws) (upd_buffered_writes vd ws).
  Proof.
    induction ws; simpl; intuition auto.
    rename a0 into a.
    rename b into v.

    unfold upd_buffered_writes.
    rewrite upd_all_eq_upd_all'.
    simpl.
    rewrite <- upd_all_eq_upd_all'.
    fold (upd_buffered_writes (upd vd a (v, None)) ws).
    eapply IHws; eauto.

    rewrite map_map.
    rewrite fst_compose_add_empty_rdr.
    eauto.

    rewrite map_map.
    rewrite fst_compose_add_empty_rdr.
    eauto.
  Qed.

  Hint Resolve cache_rep_add_all_upd.
  Hint Resolve NoDup_writes.

  Lemma in_addr_to_in_entry : forall A V a (entries: list (A*V)),
      In a (map fst entries) ->
      exists v, In (a, v) entries.
  Proof.
    induction entries; simpl; intros.
    - destruct H.
    - destruct a0 as [a' v]; simpl in *.
      intuition auto; subst; eauto.
      deex; eauto.
  Qed.

  Lemma wb_writes_valid_addresses : forall d c vd0 wb vd,
      wb_rep vd0 wb vd ->
      cache_rep d c vd0 ->
      forall a, In a (map fst (wb_writes wb)) ->
           exists v0, d a = Some (v0, None).
  Proof.
    intros.
    edestruct in_addr_to_in_entry; eauto.
    eapply wb_cache_states; eauto.
    apply wb_writes_complete'; eauto.
  Qed.

  Hint Resolve wb_writes_valid_addresses.

  Lemma no_wb_reader_conflict_empty : forall c,
      no_wb_reader_conflict c emptyWriteBuffer.
  Proof.
    unfold no_wb_reader_conflict, emptyWriteBuffer;
      intros; auto.
  Qed.

  Hint Resolve no_wb_reader_conflict_empty.

  Lemma hide_readers_upd_buffered_writes : forall entries d,
      hide_readers (upd_buffered_writes d entries) =
      upd_all (hide_readers d) entries.
  Proof.
    unfold upd_buffered_writes.
    induction entries; intros.
    reflexivity.
    destruct a as [a v]; simpl.
    extensionality a'.
    destruct (nat_dec a a'); subst.
    unfold hide_readers; autorewrite with upd; auto.
    rewrite <- IHentries.
    unfold hide_readers; autorewrite with upd; auto.
  Qed.

  Lemma wb_rep_upd_all : forall d wb vd,
      wb_rep d wb vd ->
      upd_all (hide_readers d) (wb_writes wb) = vd.
  Proof.
    unfold wb_rep; intros.
    extensionality a.
    specialize (H a).
    destruct (wb_get wb a) eqn:Ha;
      destruct_ands; repeat deex.
    pose proof (wb_writes_complete _ _ Ha).
    erewrite upd_all_in by eauto; auto.
    pose proof (wb_get_missing _ _ Ha).
    rewrite upd_all_not_in by auto.
    unfold hide_readers.
    destruct matches in *; auto.
  Qed.

  Hint Resolve wb_rep_upd_all.

  Lemma upd_buffered_writes_cons : forall vd entries a v,
      upd_buffered_writes vd ((a, v) :: entries) =
      upd (upd_buffered_writes vd entries) a (v, None).
  Proof.
    reflexivity.
  Qed.

  Lemma same_domain_upd_buffered_writes : forall entries vd,
      (forall a v, In (a, v) entries -> exists v0, vd a = Some v0) ->
      NoDup (map fst entries) ->
      same_domain vd (upd_buffered_writes vd entries).
  Proof.
    induction entries; simpl; intros; auto.
    destruct a as [a v].
    pose proof (H a v); intuition auto; deex.
    clear H3.
    eapply same_domain_preorder.
    eapply IHentries; eauto.
    rewrite upd_buffered_writes_cons.

    unfold upd_buffered_writes.
    destruct (in_dec nat_dec a (map fst entries)).
    - apply in_addr_to_in_entry in i; deex.
      eapply same_domain_upd; eauto.
      apply (List.in_map add_empty_rdr) in H2; simpl in *.
      erewrite upd_all_in; eauto.
      rewrite map_map, fst_compose_add_empty_rdr; eauto.
    - eapply same_domain_upd; eauto.
      rewrite upd_all_not_in; eauto.
      rewrite map_map, fst_compose_add_empty_rdr.
      auto.
  Qed.

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
    rewrite hide_readers_upd_buffered_writes; auto.
    apply same_domain_upd_buffered_writes; eauto.
    intros.
    apply wb_writes_complete' in H7.
    specialize (H5 a); simpl_match; destruct_ands; deex.
    eauto.
  Qed.

  Hint Extern 1 {{cache_commit; _}} => apply cache_commit_ok : prog.

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

  (* TODO: these lemmas are very repetitive, figure out how to simplify this *)

  Lemma wb_written_value_vdisk : forall d wb vd a v,
      wb_rep d wb vd ->
      wb_get wb a = Written v ->
      vd a = Some v.
  Proof.
    unfold wb_rep; intros.
    specialize (H a); repeat simpl_match; intuition auto.
  Qed.

  Arguments wb_written_value_vdisk {d wb vd a v} _ _.

  Ltac wb_written_fwd :=
    match goal with
    | [ Hrep: wb_rep _ ?wb _,
              Hval: wb_get ?wb _ = Written _  |- _ ] =>
      learn that (wb_written_value_vdisk Hrep Hval)
    end.

  Lemma cache_clean_value_vdisk : forall d c vd a v,
      cache_rep d c vd ->
      cache_get c a = Clean v ->
      vd a = Some (v, None).
  Proof.
    unfold cache_rep; intros.
    specialize (H a); repeat simpl_match;
      intuition auto.
  Qed.

  Arguments cache_clean_value_vdisk {d c vd a v} _ _.

  Ltac cache_clean_fwd :=
    match goal with
    | [ Hrep: cache_rep _ ?c _,
              Hval: cache_get ?c _ = Clean _ |- _ ] =>
      learn that (cache_clean_value_vdisk Hrep Hval)
    end.

  Lemma wb_missing_value_vdisk : forall d wb vd a v rdr,
      wb_rep d wb vd ->
      wb_get wb a = WbMissing ->
      d a = Some (v, rdr) ->
      vd a = Some v.
  Proof.
    unfold wb_rep; intros.
    specialize (H a); repeat simpl_match; auto.
  Qed.

  Ltac wb_rep_fwd :=
    match goal with
    | [ Hrep: wb_rep _ ?wb _,
              Hval: wb_get ?wb ?a = _ |- _ ] =>
      learn that (Hrep a)
    end.

  Ltac cache_rep_fwd :=
    match goal with
    | [ Hrep: cache_rep _ ?c _,
              Hval: cache_get ?c ?a = _ |- _ ] =>
      learn that (Hrep a)
    end.

  Ltac simp_hook ::= wb_rep_fwd || cache_rep_fwd || simpl_match.

  Theorem cache_read_ok : forall a,
      SPEC App.delta, tid |-
              {{ v,
               | PRE d m s_i s:
                   invariant delta d m s /\
                   get vdisk s a = Some v
               | POST d' m' s_i' s' r:
                   invariant delta d' m' s' /\
                   guar delta tid s s' /\
                   hide_readers (get vDisk0 s') = hide_readers (get vDisk0 s) /\
                   modified [( vCache; vDisk0 )] s s' /\
                   (forall v', r = Some v' -> v' = v) /\
                   s_i' = s_i
              }} cache_read a.
  Proof.
    hoare.
    (* TODO: eauto on v = v' goals is slow but info_eauto shows nothing *)

    eexists; simplify; finish.
    hoare.

    eexists; simplify; finish.
    hoare.

    replace (get vDisk0 s0).
    rewrite hide_readers_unchanged_remove; auto.

    eexists; simplify; finish.
    hoare.

    replace (get vDisk0 s0).
    rewrite hide_readers_unchanged_add; auto.
  Qed.

  Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.

  Module CopyExample.

    Definition copy a a' :=
      opt_v <- cache_read a;
        match opt_v with
        | None => Ret false
        | Some v => ok <- cache_write a' v;
                     Ret ok
        end.

    Hint Extern 1 {{cache_read _; _}} => apply cache_read_ok : prog.
    Hint Extern 1 {{cache_write _ _; _}} => apply cache_write_ok : prog.

    Lemma same_domain_fwd : forall AT AEQ V (d d': @mem AT AEQ V) a,
        same_domain d d' ->
        forall v, d a = Some v -> exists v', d' a = Some v'.
    Proof.
      unfold same_domain; intuition eauto.
    Qed.

    Lemma impl_trans : forall (P Q R:Prop),
        (P -> Q) ->
        (Q -> R) ->
        (P -> R).
    Proof.
      tauto.
    Qed.

    Lemma or_impl : forall (P Q R:Prop),
        (P -> R) ->
        (Q -> R) ->
        P \/ Q -> R.
    Proof.
      tauto.
    Qed.

    Theorem copy_ok : forall a a',
        SPEC App.delta, tid |-
                {{ v v0,
                 | PRE d m s_i s:
                     invariant delta d m s /\
                     get vdisk s a = Some v /\
                     get vdisk s a' = Some v0 /\
                     guar delta tid s_i s
                 | POST d' m' s_i' s' r:
                     invariant delta d' m' s' /\
                      (r = true ->
                      get vdisk s' = upd (get vdisk s) a' v) /\
                      s_i' = s_i
                }} copy a a'.
    Proof.
      hoare.
      eexists; simplify; finish.

      hoare.

      match goal with
      | [ H: same_domain (get vDisk0 s) (get vDisk0 s0) |- _ ] =>
        pose proof (same_domain_fwd a' H)
      end.

      (* TODO: need same_domain across vdisks from invariant + guar; the value
for get vdisk s0 a' does not matter, since it is overwritten *)
      eexists; simplify; finish.
      admit.

      hoare.
      match goal with
      | [ H: forall _, Some ?v = Some _ -> _ |- _ ] =>
        specialize (H v)
      end; simplify; finish.

      replace (get vdisk s) with (get vdisk s0); auto.

      symmetry.
      match goal with
      | [ H: modified _ s s0 |- _ ] =>
        eapply H
      end.
      eapply impl_trans; [ apply hin_iff_index_in | ]; simpl.
      repeat (apply or_impl; [ vars_distinct | ]); auto.
    Admitted.

  End CopyExample.

End MakeConcurrentCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ) ("delta'" . (?δ (Br . Bl) ?')) ("Sigma'" . (?Σ (Br . Bl) ?'))) *)
(* End: *)