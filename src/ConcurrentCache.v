Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Import List.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.
Require Import WriteBuffer.

Section ConcurrentCache.

  Definition Sigma := defState [Cache; WriteBuffer] [Cache; WriteBuffer; DISK; Disk].

  Section Variables.

    Tactic Notation "var" constr(n) constr(f) :=
      let t := constr:(ltac:(hmember n (f Sigma))) in
      let t' := eval cbn in t in
          exact (t': var (f Sigma) _).

    Tactic Notation "mvar" constr(n) := var n mem_types.
    Tactic Notation "absvar" constr(n) := var n abstraction_types.

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

  Definition no_wb_reader_conflict c wb :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Definition cacheI : Invariant Sigma :=
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

  Lemma readers_locked_refl : forall tid vd,
      readers_locked tid vd vd.
  Proof.
    unfold readers_locked; eauto.
  Qed.

  Lemma readers_locked_trans : forall tid vd vd' vd'',
      readers_locked tid vd vd' ->
      readers_locked tid vd' vd'' ->
      readers_locked tid vd vd''.
  Proof.
    unfold readers_locked; eauto.
  Qed.

  (* not sure whether to say this about vDisk0, vDisk, or both *)
  Definition cacheR (tid:TID) : Relation Sigma :=
    fun s s' =>
      let vd := get vDisk0 s in
      let vd' := get vDisk0 s' in
      same_domain vd vd' /\
      readers_locked tid vd vd'.

  Hint Immediate same_domain_refl same_domain_trans.
  Hint Immediate readers_locked_refl readers_locked_trans.

  Theorem cacheR_trans_closed : forall tid s s',
      star (cacheR tid) s s' ->
      cacheR tid s s'.
  Proof.
    intro tid.
    apply trans_closed; unfold cacheR; intuition eauto.
  Qed.

  Definition delta : Protocol Sigma :=
    defProtocol cacheI cacheR cacheR_trans_closed.

  (* abstraction helpers *)

  Definition modify_cache (up: Cache -> Cache) rx : prog Sigma :=
    c <- Get mCache;
      _ <- Assgn mCache (up c);
      _ <- var_update vCache up;
      rx tt.

  Definition modify_wb (up: WriteBuffer -> WriteBuffer) rx : prog Sigma :=
    wb <- Get mWriteBuffer;
      _ <- Assgn mWriteBuffer (up wb);
      _ <- var_update vWriteBuffer up;
      rx tt.

  (** safe read: returns None upon cache miss  *)
  Definition cache_maybe_read a rx : prog Sigma :=
    c <- Get mWriteBuffer;
      match wb_val c a with
      | Some v => rx (Some v)
      | None =>
        c <- Get mCache;
          rx (cache_val c a)
      end.

  (** Prepare to fill address a, locking the address and marking it
  invalid in the cache to signal the lock to concurrent threads. *)
  Definition prepare_fill a rx : prog Sigma :=
    tid <- GetTID;
      _ <- StartRead_upd a;
      (* note that no updates to Disk are needed since the readers are
    hidden *)
      _ <- var_update vDisk0
        (fun vd => add_reader vd a tid);
      _ <- modify_cache (fun c => cache_add c a Invalid);
      rx tt.

  Definition cache_fill a rx : prog Sigma :=
    _ <- prepare_fill a;
      _ <- Yield a;
      v <- FinishRead_upd a;
      _ <- var_update vDisk0
        (fun vd => remove_reader vd a);
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      rx v.

  (** buffer a new write: fails (returns false) if the write overlaps
  with the address being read filled *)
  Definition cache_write a v rx : prog Sigma :=
    c <- Get mCache;
      match cache_get c a with
      | Invalid => rx false
      | _ =>
        _ <- modify_wb (fun wb => wb_write wb a v);
          _ <- var_update vdisk
            (fun vd => upd vd a v);
          rx true
      end.

  Definition wb_writes wb : list (addr * valu) :=
    fold_right (fun e acc =>
                 match e with
                 | (a, Written v) => (a, v) :: acc
                 | (_, WbMissing) => acc
                 end) nil (wb_entries wb).

  Fixpoint cache_add_all (c: Cache) (entries: list (addr * valu)) : Cache :=
    match entries with
    | nil => c
    | (a, v) :: es => cache_add_all (cache_add c a (Dirty v)) es
    end.

  Definition upd_all A AEQ V (m: @mem A AEQ (const V)) (entries: list (A * V)) :=
    fold_right (fun (e:A * V) acc =>
                  let (a, v) := e in
                  upd acc a v) m entries.

  Definition add_empty_rdr (ae: addr * valu) : addr * wr_set :=
    let (a, v) := ae in
    (a, (v, None)).

  (* TODO; replace with a more efficient direct recursive
  implementation and prove equivalent to this *)
  Definition upd_buffered_writes (d: DISK) (entries: list (addr * valu)) :=
    upd_all d (map add_empty_rdr entries).

  (** commit all the buffered writes into the global cache

    safety is provided by the invariant no_wb_reader_conflict enforced
    by cache_write's checks *)
  Definition cache_commit rx : prog Sigma :=
    c <- Get mCache;
      wb <- Get mWriteBuffer;
      _ <- modify_cache (fun c => cache_add_all c (wb_writes wb));
      _ <- var_update vDisk0 (fun d => upd_buffered_writes d (wb_writes wb));
      _ <- modify_wb (fun _ => emptyWriteBuffer);
      rx tt.

  (** abort all buffered writes, restoring vDisk0 *)
  Definition cache_abort rx : prog Sigma :=
    _ <- Assgn mWriteBuffer emptyWriteBuffer;
      _ <- GhostUpdate (fun s =>
                         let vd' := hide_readers (get vDisk0 s) in
                         set vdisk vd' s);
      rx tt.

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

  Lemma cache_val_mem {m: memory Sigma} {s: abstraction Sigma} :
      get mCache m = get vCache s ->
      cache_val (get mCache m) = cache_val (get vCache s).
  Proof.
    congruence.
  Qed.

  Lemma cache_get_mem {m: memory Sigma} {s: abstraction Sigma} :
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

  Ltac simp_hook := fail.

  Ltac simplify_step :=
    match goal with
    | [ |- forall _, _ ] => intros
    | _ => learn_protocol
    | _ => deex
    | _ => progress destruct_ands
    | _ => inv_opt
    | _ => progress subst
    | _ => replace_mem_val
    | _ => reduce_hlist
    | _ => simp_hook
    | _ => descend
    | _ => prove_protocol
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
      unfold const; intros.
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
      destruct (weq a a0); subst;
        autorewrite with cache in *;
        eauto.
    Qed.

    Lemma no_wb_reader_conflict_stable_write : forall c wb a v,
        cache_get c a <> Invalid ->
        no_wb_reader_conflict c wb ->
        no_wb_reader_conflict c (wb_write wb a v).
    Proof.
      unfold no_wb_reader_conflict; intros.
      destruct (weq a a0); subst;
        rewrite ?wb_get_write_eq, ?wb_get_write_neq
        in * by auto;
        eauto || congruence.
    Qed.

    Lemma same_domain_add_reader : forall d a tid,
        same_domain d (add_reader d a tid).
    Proof.
      unfold same_domain, subset, add_reader; split;
        intros;
        destruct (weq a a0); subst;
          destruct matches in *;
          autorewrite with upd in *;
          eauto.
    Qed.

    Lemma same_domain_remove_reader : forall d a,
        same_domain d (remove_reader d a).
    Proof.
      unfold same_domain, subset, remove_reader; split;
        intros;
        destruct (weq a a0); subst;
          destruct matches in *;
          autorewrite with upd in *;
          eauto.
    Qed.

    Lemma readers_locked_add_reader : forall tid tid' vd a v,
        vd a = Some (v, None) ->
        readers_locked tid vd (add_reader vd a tid').
    Proof.
      unfold readers_locked, add_reader; intros.
      destruct (weq a a0); subst;
        simpl_match;
        autorewrite with upd;
        congruence.
    Qed.

    Lemma readers_locked_remove_reading : forall tid vd a v,
        vd a = Some (v, Some tid) ->
        readers_locked tid vd (remove_reader vd a).
    Proof.
      unfold readers_locked, remove_reader; intros.
      destruct (weq a a0); subst;
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
      destruct (weq a a0); subst;
        rewrite ?wb_get_write_eq, ?wb_get_write_neq by auto;
        autorewrite with upd;
        eauto.

      destruct matches in *|- ;
        intuition eauto.
    Qed.

  End SpecLemmas.

  Theorem modify_cache_ok : forall up,
      SPEC delta, tid |-
              {{ (_:unit),
               | PRE d m s0 s: get mCache m = get vCache s
               | POST d' m' s0' s' r:
                   s' = set vCache (up (get vCache s)) s /\
                   m' = set mCache (up (get mCache m)) m /\
                   d' = d /\
                   s0' = s0
              }} modify_cache up.
  Proof.
    hoare.
  Qed.

  Hint Extern 1 {{ modify_cache _; _ }} => apply modify_cache_ok : prog.

  Theorem modify_wb_ok : forall up,
      SPEC delta, tid |-
              {{ (_:unit),
               | PRE d m s0 s: get mWriteBuffer m = get vWriteBuffer s
               | POST d' m' s0' s' r:
                   s' = set vWriteBuffer (up (get vWriteBuffer s)) s /\
                   m' = set mWriteBuffer (up (get mWriteBuffer m)) m /\
                   d' = d /\
                   s0' = s0
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

  Theorem cache_maybe_read_ok : forall a,
      SPEC delta, tid |-
              {{ v0,
               | PRE d m s0 s: invariant delta d m s /\
                               get vdisk s a = Some v0
               | POST d' m' s0' s' r:
                   invariant delta d m s /\
                   s0' = s0 /\
                   (forall v, r = Some v ->
                         v = v0) /\
                   (r = None ->
                    cache_val (get vCache s') a = None)
              }} cache_maybe_read a.
  Proof.
    hoare.
    eauto using wb_val_none.
  Qed.

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
    pose proof (wb_val_none ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    deex.
    pose proof (cache_val_no_reader ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    congruence.
  Qed.

  Theorem prepare_fill_ok : forall a,
      SPEC delta, tid |-
              {{ v0,
               | PRE d m s0 s:
                   invariant delta d m s /\
                   cache_get (get vCache s) a = Missing /\
                   (* XXX: not sure exactly why this is a requirement,
                   but it comes from no_wb_reader_conflict *)
                   wb_get (get vWriteBuffer s) a = WbMissing /\
                   get vdisk s a = Some v0 /\
                   guar delta tid s0 s
               | POST d' m' s0' s' _:
                   invariant delta d' m' s' /\
                   get vDisk0 s' a = Some (v0, Some tid) /\
                   guar delta tid s0' s'
              }} prepare_fill a.
  Proof.
    hoare.
    eexists; simplify; finish.
    eauto using disk_no_reader.

    hoare;
      (* make sure that all these goals are still around until we
      specifically solve them *)
      let n := numgoals in guard n = 4;
      match goal with
      (* cache_rep stable when adding reader *)
      | [ |- cache_rep (upd _ _ _)
                      (cache_add _ _ _)
                      (add_reader _ _ _) ] => admit
      (* wb_rep insensitive to readers *)
      | [ |- wb_rep (add_reader _ _ _) _ _ ] => admit
      (* add_reader -> upd *)
      | [ |- add_reader _ ?a _ ?a = _ ] => admit
      | [ |- readers_locked _ _ _ ] =>
        (* TODO: debug eauto not being able to follow this chain of
        reasoning *)
        eapply readers_locked_trans; eauto;
          eapply readers_locked_add_reader;
          eapply wb_cache_val_none_vd0; eauto
      end.
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

  Lemma rely_read_lock : forall tid (s s': abstraction Sigma) a v,
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

  Theorem cache_fill_ok : forall a,
      SPEC delta, tid |-
              {{ v0,
               | PRE d m s0 s:
                   invariant delta d m s /\
                   cache_get (get vCache s) a = Missing /\
                   (* XXX: not sure exactly why this is a requirement,
                   but it comes from no_wb_reader_conflict *)
                   wb_get (get vWriteBuffer s) a = WbMissing /\
                   get vdisk s a = Some v0 /\
                   guar delta tid s0 s
               | POST d' m' s0' s' _:
                   invariant delta d' m' s' /\
                   (* no promise about actually filling the cache -
                   shouldn't affect anybody *)
                   rely delta tid s s' /\
                   guar delta tid s0' s'
              }} cache_fill a.
  Proof.
    hoare.
    eexists; simplify; finish.
    hoare.
    exists v0; simplify; finish.
    (* to guarantee this, need to know that a is still not cached -
    protocol should say if cache has invalid, then someone must be
    reading it (this is in the invariant via cache_rep already) AND
    reader is only thread that can add a value (or write - WriteBuffer
    must also remain empty)

    XXX: make changes to protocol to make this admit provable
    *)
    admit.

    hoare;
      let n := numgoals in guard n = 4;
      match goal with
      (* cache_rep stable when adding reader *)
      | [ |- cache_rep (upd _ _ _)
                      (cache_add _ _ _)
                      (remove_reader _ _) ] => admit
      (* wb_rep insensitive to readers *)
      | [ |- wb_rep (remove_reader _ _) _ _ ] => admit
      (* clean addresses irrelevant *)
      | [ |- no_wb_reader_conflict (cache_add _ _ _) _ ] => admit
      (* XXX: not provable. Problematic step introduced by
            prepare_fill, which should precisely specify everything it
            did to s so we can prove together with FinishRead the
            effect is the same as a rely *)
      | [ |- rely delta _ _ _ ] => admit
      end.
  Admitted.

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


  Theorem cache_write_ok : forall a v,
      SPEC delta, tid |-
              {{ v0,
               | PRE d m s0 s:
                   invariant delta d m s /\
                   get vdisk s a = Some v0 /\
                   guar delta tid s0 s
               | POST d' m' s0' s' r:
                   invariant delta d' m' s' /\
                   (r = true -> get vdisk s' a = Some v) /\
                   get vDisk0 s' = get vDisk0 s /\
                   guar delta tid s s' /\
                   guar delta tid s0' s'
              }} cache_write a v.
  Proof.
    hoare.
  Qed.

  Hint Resolve in_eq in_cons.
  Hint Resolve SetoidList.InA_cons_hd SetoidList.InA_cons_tl.

  Lemma eq_key_elt_eq : forall elt a a',
      a = a' ->
      @Map.eq_key_elt elt a a'.
  Proof.
    intros.
    subst.
    reflexivity.
  Qed.

  Hint Resolve eq_key_elt_eq.

  Theorem wb_writes_complete : forall wb a v,
      wb_get wb a = Written v ->
      In (a, v) (wb_writes wb).
  Proof.
    intros.
    unfold wb_writes, wb_get, wb_entries in *.
    pose proof (MapFacts.elements_mapsto_iff wb a (Written v)).
    let H := fresh in
    destruct (Map.find a wb) eqn:H; subst; try congruence.
    assert (Map.MapsTo a (Written v) wb).
    apply MapFacts.find_mapsto_iff; congruence.
    intuition.

    induction (Map.elements wb); intros.

    inversion H0.

    inversion H0; subst.
    inversion H4; destruct a0.
    simpl in *; subst.
    simpl; auto.

    intuition.
    destruct a0 as [ ? [] ]; simpl; auto.
  Qed.

  Lemma setoid_ina : forall a l,
      SetoidList.InA (Map.eq_key_elt (elt:=wb_entry)) a l <->
      In a l.
  Proof.
    induction l.
    split; inversion 1.

    split; intuition.
    inversion H; subst; eauto.
    destruct a, a0.
    inversion H3; simpl in *; subst; eauto.

    inversion H; subst; eauto.
  Qed.

  Lemma in_wb_writes_elements : forall wb a v,
      In (a, v) (wb_writes wb) ->
      In (a, Written v) (Map.elements wb).
  Proof.
    unfold wb_writes, wb_entries; intros.
    induction (Map.elements wb); simpl in *; auto.
    destruct a0 as [ ? [] ]; simpl in *.
    intuition.
    inversion H0; subst; auto.
    intuition.
  Qed.

  Theorem wb_writes_complete' : forall wb a v,
      In (a, v) (wb_writes wb) ->
      wb_get wb a = Written v.
  Proof.
    intros.

    apply in_wb_writes_elements in H.
    assert (Map.MapsTo a (Written v) wb).
    apply MapFacts.elements_mapsto_iff.
    apply setoid_ina.
    auto.
    unfold wb_get.
    erewrite Map.find_1; eauto.
  Qed.

  Lemma wb_get_empty : forall a,
      wb_get emptyWriteBuffer a = WbMissing.
  Proof.
    auto.
  Qed.

  Hint Constructors NoDup.

  Lemma NoDup_entries : forall wb,
      NoDup (map fst (wb_entries wb)).
  Proof.
    intros.
    pose proof (Map.elements_3w wb).
    unfold wb_entries.
    generalize dependent (Map.elements wb); intros.
    induction H; cbn; auto.
    constructor; auto.
    intro.
    apply H.

    destruct x; simpl in *.
    clear H H0.
    induction l; simpl in *; intuition.
    destruct a; simpl in *; subst.
    constructor.
    reflexivity.

    inversion IHNoDupA; subst; auto.
  Qed.

  Lemma wb_entries_writes_subset : forall wb,
      incl (map fst (wb_writes wb))
           (map fst (wb_entries wb)).
  Proof.
    unfold incl, wb_writes; intros.
    generalize dependent (wb_entries wb); intros.
    induction l; simpl in *; eauto.
    destruct a0.
    destruct w0; simpl in *; intuition.
  Qed.


  Lemma incl_nil : forall A (l: list A),
      incl l nil ->
      l = nil.
  Proof.
    unfold incl; destruct l; intros; auto.
    assert (In a []) by eauto.
    inversion H0.
  Qed.

  Lemma incl_not_in : forall A (l l': list A) a,
      incl l l' ->
      ~In a l' ->
      ~In a l.
  Proof.
    unfold incl; intros.
    intuition.
  Qed.

  Ltac assume P := assert P by admit.

  Theorem incl_trans : forall A (l l' l'' : list A),
      incl l l' ->
      incl l' l'' ->
      incl l l''.
  Proof.
    firstorder.
  Qed.

  Lemma incl_cons : forall A l l' (a:A),
      incl (a::l) l' ->
      incl l l'.
  Proof.
    unfold incl; simpl; intuition eauto.
  Qed.

  Hint Resolve incl_cons.

  Lemma incl_converse : forall A (l l': list A),
      incl l l' ->
      (forall a, ~In a l' -> ~In a l).
  Proof.
    firstorder.
  Qed.

  Lemma incl_remove : forall A l l' (a:A),
      incl (a::l) (a::l') ->
      incl l l'.
  Proof.
    induction l; intros; eauto.
    unfold incl; simpl; intuition.
  Abort.

  Fixpoint remove_first A (decA: DecEq A) (a:A) l :=
    match l with
    | nil => nil
    | a'::l' => if decA a a' then l' else a' :: remove_first decA a l'
    end.

  Lemma in_split_first : forall A (decA: DecEq A) l (a:A),
      In a l ->
      exists l1 l2, l = l1 ++ a :: l2 /\
               ~In a l1.
  Proof.
    induction l.
    inversion 1.
    inversion 1; subst.
    exists nil, l.
    intuition eauto.

    pose proof (IHl _ H0).
    repeat deex.
    destruct (decA a a0); subst.
    exists nil, (l1 ++ a0 :: l2).
    intuition.
    exists (a :: l1), l2.
    rewrite <- app_comm_cons; intuition.
    inversion H1; subst; intuition eauto.
  Qed.

  Lemma remove_first_app : forall A (decA: DecEq A) l l' (a: A),
      ~In a l ->
      remove_first decA a (l ++ l') = l ++ remove_first decA a l'.
  Proof.
    induction l; intros; eauto.
    rewrite <- app_comm_cons.
    simpl.
    destruct (decA a0 a); subst.
    exfalso; eauto.
    rewrite IHl; eauto.
  Qed.

  Lemma remove_first_eq : forall A (decA: DecEq A) l (a:A),
      remove_first decA a (a::l) = l.
  Proof.
    intros; simpl.
    destruct (decA a a); congruence.
  Qed.

  Lemma incl_in_cons : forall A l l' (a:A),
      incl l l' ->
      In a l' ->
      incl (a::l) l'.
  Proof.
    unfold incl; intros.
    destruct H1; subst; eauto.
  Qed.

  Hint Resolve incl_in_cons.

  Lemma incl_app_comm_r : forall A (l l' l'': list A),
      incl l (l' ++ l'') ->
      incl l (l'' ++ l').
  Proof.
    unfold incl; intros.
    apply H in H0.
    apply in_app_or in H0.
    intuition auto using in_or_app.
  Qed.

  Lemma incl_app_single : forall A (l l' l'': list A) a,
      incl l (l' ++ a :: l'') ->
      incl l (a :: l' ++ l'').
  Proof.
    unfold incl; intros.
    apply H in H0.
    apply in_app_or in H0.
    intuition.
    rewrite app_comm_cons.
    destruct H1; subst;
      intuition auto using in_or_app.
  Qed.

  Lemma incl_remove' : forall A (decA: DecEq A) l l' (a:A),
      ~In a l ->
      incl (a::l) l' ->
      incl l (remove_first decA a l').
  Proof.
    induction l; intros; eauto.
    unfold incl; inversion 1.
    assert (In a0 l') as Ina0 by eauto.
    pose proof (in_split_first decA _ _ Ina0); repeat deex.
    rewrite remove_first_app by eauto.
    rewrite remove_first_eq.
    clear Ina0.
    apply incl_app_single in H0.
    assert (incl (a0 :: l) (a0 :: l1 ++ l2)) as Hincl by eauto.
    apply IHl in Hincl.
    rewrite remove_first_eq in Hincl.
    apply incl_in_cons; eauto.
    destruct (decA a a0); subst.
    exfalso; eauto.

    assert (In a (a0 :: l1 ++ l2)) as Hin by eauto.
    destruct Hin; congruence.
    intuition eauto.
  Qed.

  Lemma count_occ_app : forall A (decA: DecEq A) l l' (a:A),
      count_occ decA (l ++ l') a =
      count_occ decA l a + count_occ decA l' a.
  Proof.
    induction l; cbn; intros; eauto.
    destruct (decA a a0); subst; eauto.
    rewrite IHl; auto.
  Qed.

  Require Import Arith.

  Lemma count_occ_remove_first : forall A (decA: DecEq A) (l: list A) a,
      In a l ->
      count_occ decA (remove_first decA a l) a < count_occ decA l a.
  Proof.
    intros.
    apply in_split_first in H; auto.
    repeat deex.
    rewrite remove_first_app; auto.
    rewrite remove_first_eq.
    rewrite ?count_occ_app, ?count_occ_cons_eq by auto.
    apply plus_lt_compat_l.
    auto.
  Qed.

  Require Import Omega.

  Lemma count_occ_in : forall A (decA : DecEq A) l (a:A),
      In a l ->
      1 <= count_occ decA l a.
  Proof.
    intros.
    apply in_split_first in H; auto.
    repeat deex.
    rewrite count_occ_app.
    rewrite count_occ_cons_eq by auto.
    omega.
  Qed.

  Lemma count_occ_not_in : forall A (decA : DecEq A) l (a:A),
      ~In a l ->
       count_occ decA l a = 0.
  Proof.
    intros.
    induction l; eauto.
    simpl; destruct (decA a0 a); subst; eauto.
    exfalso; eauto.
  Qed.

  Lemma incl_nodup_count_occ : forall A (decA: DecEq A) (l l': list A),
      NoDup l ->
      incl l l' ->
      (forall a, count_occ decA l a <= count_occ decA l' a).
  Proof.
    induction l; intros; simpl.
    apply le_0_n.
    destruct (decA a a0); subst; eauto.
    assert (In a0 l') by eauto.
    inversion H; subst; eauto.
    pose proof (incl_remove' decA ltac:(eassumption) ltac:(eassumption)).
    apply IHl with (a := a0) in H2; auto.
    rewrite count_occ_not_in in * by eauto.
    pose proof (count_occ_in decA _ _ H1).
    omega.

    inversion H; subst; eauto.
  Qed.

  (** Oops, this isn't true: incl l l' only gives a subset relation
  for l and l' treated as sets, so (incl [a; a] [a; b]) holds for
  example, but l has duplicates. Instead of incl we need a injective
  mapping from the indices of l to indices in l' where corresponding
  elements match, a much more complicated permutation-like notion *)
  Lemma NoDup_filter : forall A (l l': list A),
      incl l l' ->
      NoDup l' ->
      NoDup l.
  Proof.
    (* direct induction on l *)
    induction l; intros; eauto.
    assert (incl l l').
    unfold incl in *; intuition eauto.
    assert (~In a l).
    intro.
    assert (In a (a :: l)) by auto.
    apply H in H3.

    Restart.
    (* induction in NoDup l' (should be same as induction l') *)
    induction 2.
    apply incl_nil in H; subst; auto.
    (* exists a, In a l /\ ~In a l0 *)
    assert ({incl l l0} + {~incl l l0}).
    admit.
    destruct H2; eauto.

    Restart.
    (* direct induction on l' *)
    intros.
    generalize dependent l.
    induction l'; intros; eauto.
    apply incl_nil in H; subst; auto.
    inversion H0; subst; intuition.

    Restart.

    (* brute force attempt to do induction on l and l' *)
    induction l; intros; eauto.
    induction l'; intros; eauto.
    assert (In a []).
    apply H; auto.
    inversion H1.
    inversion H0; subst; eauto.
    apply IHl'; eauto.
    assert ({a = a0} + {a <> a0}).
    admit.
    destruct H1; subst; eauto.
    intros a' ?.
    apply H in H1.
    destruct H1; subst; eauto.
    admit.

    intros a' ?.
    inversion H1; subst; eauto.
    admit.
    apply H in H1.
    destruct H1; subst; eauto.

    Restart.

    (* more careful induction on l, l' *)
    induction l, l'; intros; eauto.
    assert (In a []) by eauto.
    inversion H1.
    rename a0 into a'.
    inversion H0; subst.
    assume ({a' = a} + {a <> a'}).
    destruct H1; subst.
    constructor; eauto.
    intuition.
  Admitted.

  Lemma NoDup_writes : forall wb,
      NoDup (map fst (wb_writes wb)).
  Proof.
    intros.
    eapply NoDup_filter.
    apply wb_entries_writes_subset.
    apply NoDup_entries.
  Qed.

  Theorem in_nodup_split : forall A l (a:A),
      NoDup l ->
      In a l ->
      exists l1 l2,
        l = l1 ++ a :: l2 /\
        ~In a l1 /\
        ~In a l2.
  Proof.
    intros.
    induction l.
    inversion H0.
    destruct H0; subst.
    - exists nil, l; intuition.
      inversion H; intuition.
    - inversion H; subst; intuition.
      repeat deex.
      exists (a0 :: l1), l2; intuition.
      inversion H2; subst; eauto.
  Qed.

  Theorem in_nodup_map_split : forall A B (f: A -> B) l (a:A),
      NoDup (map f l) ->
      In a l ->
      exists l1 l2,
        l = l1 ++ a :: l2 /\
        ~In (f a) (map f l1) /\
        ~In (f a) (map f l2).
  Proof.
    intros.
    induction l.
    inversion H0.
    destruct H0; subst.
    - exists nil, l; intuition.
      inversion H; subst; intuition.
    - inversion H; subst; intuition.
      repeat deex.
      exists (a0 :: l1), l2; intuition.
      destruct H2; subst; eauto.
      rewrite ?map_cons, ?map_app, ?map_cons in *.
      rewrite H2 in *.
      apply H3.
      apply in_app_iff; eauto.
  Qed.

  Theorem upd_all_app_ignore : forall A AEQ V l1 l2
                                 (d: @mem A AEQ (const V)) (a:A),
      ~In a (map fst l2) ->
      upd_all d (l1 ++ l2) a = upd_all d l1 a.
  Proof.
    unfold upd_all.
    induction l1; cbn; intros.
    induction l2; cbn; auto.
    destruct a0.
    apply not_in_cons in H; intuition.
    autorewrite with upd; auto.
    destruct a.
    destruct (AEQ a a0); subst;
      autorewrite with upd;
      auto.
  Qed.

  Corollary upd_all_not_in : forall A AEQ V l
                               (d: @mem A AEQ (const V)) (a:A),
      ~In a (map fst l) ->
      upd_all d l a = d a.
  Proof.
    intros.
    replace l with (nil ++ l) by reflexivity.
    rewrite upd_all_app_ignore; auto.
  Qed.

  Theorem upd_all_app_last : forall A AEQ V l
                               (d: @mem A AEQ (const V))
                               a v,
      ~In a (map fst l) ->
      upd_all d (l ++ [ (a, v) ]) a = Some v.
  Proof.
    unfold upd_all.
    induction l; cbn; intros.
    autorewrite with upd; auto.

    destruct a.
    destruct (AEQ a a0); subst.

    autorewrite with upd; auto.
    apply not_in_cons in H; intuition.
    autorewrite with upd; auto.
  Qed.

  Lemma app_cons_to_app : forall A (l l': list A) a,
      l ++ a :: l' = l ++ [a] ++ l'.
  Proof.
    auto.
  Qed.

  Hint Resolve in_map.

  Lemma not_in_map : forall A B (f: A -> B)
                       (finj: forall a a', f a = f a' -> a = a')
                       l a,
      ~In a l ->
      ~In (f a) (map f l).
  Proof.
    intros.
    contradict H.
    induction l.
    inversion H.
    inversion H.
    apply finj in H0; subst; auto.
    eauto.
  Qed.

  Lemma nodup_map : forall A B (f: A -> B) l,
      (forall a a', f a = f a' -> a = a') ->
      NoDup l ->
      NoDup (map f l).
  Proof.
    intros.
    induction l; intros; cbn; auto.
    inversion H0; subst.
    constructor; auto.
    apply not_in_map; auto.
  Qed.

  Theorem upd_all_in : forall A AEQ V (d: @mem A AEQ (const V)) l a v,
      NoDup (map fst l) ->
      In (a, v) l ->
      upd_all d l a = Some v.
  Proof.
    intros.

    pose proof (in_nodup_map_split _ _ _ H H0); repeat deex.
    rewrite app_cons_to_app in *.
    rewrite app_assoc.
    rewrite upd_all_app_ignore; auto.
    rewrite upd_all_app_last; auto.
  Qed.

  Lemma In_add_empty_rdr : forall a v wb,
      In (a, v) (wb_writes wb) ->
      In (a, (v, None)) (map add_empty_rdr (wb_writes wb)).
  Proof.
    intros.
    replace (a, (v, None)) with (add_empty_rdr (a, v)) by reflexivity.
    apply in_map; auto.
  Qed.

  Lemma addrs_add_empty_rdr : forall wb,
      map fst (map add_empty_rdr (wb_writes wb)) =
      map fst (wb_writes wb).
  Proof.
    intros.
    rewrite map_map.
    unfold add_empty_rdr.
    induction (wb_writes wb); simpl; eauto.
    destruct a; simpl; congruence.
  Qed.

  Hint Resolve In_add_empty_rdr.

  Lemma wb_get_missing' : forall wb a,
      wb_get wb a = WbMissing ->
      (forall v, ~In (a, v) (wb_writes wb)).
  Proof.
    intros.
    intro.
    apply wb_writes_complete' in H0.
    congruence.
  Qed.

  Lemma in_map : forall A (l: list A) B (f: A -> B) b,
      In b (map f l) ->
      exists a, b = f a /\
           In a l.
  Proof.
    induction l; simpl; intros.
    inversion H.
    intuition eauto.
    edestruct IHl; eauto.
    intuition eauto.
  Qed.

  Lemma wb_get_missing : forall wb a,
      wb_get wb a = WbMissing ->
      ~In a (map fst (wb_writes wb)).
  Proof.
    intros; intro.
    apply in_map in H0; deex.
    destruct a0; simpl in *.
    pose proof (wb_get_missing' _ _ H).
    intuition eauto.
  Qed.

  Theorem wb_rep_empty : forall d wb vd,
      wb_rep d wb vd ->
      wb_rep (upd_buffered_writes d (wb_writes wb)) emptyWriteBuffer vd.
  Proof.
    unfold wb_rep; intros.
    specialize (H a).
    rewrite wb_get_empty.
    unfold upd_buffered_writes.
    let H := fresh in
    destruct (wb_get wb a) eqn:H; intuition.
    apply wb_writes_complete in H0.
    pose proof (NoDup_writes wb).
    erewrite upd_all_in; eauto.
    2: rewrite addrs_add_empty_rdr; auto.
    2: apply In_add_empty_rdr; eauto.
    auto.

    apply wb_get_missing in H0.
    rewrite upd_all_not_in; auto.
    rewrite addrs_add_empty_rdr; auto.
  Qed.

  Hint Resolve wb_rep_empty.

  Theorem cache_commit_ok :
      SPEC delta, tid |-
              {{ (_:unit),
               | PRE d m s0 s:
                   invariant delta d m s
               | POST d' m' s0' s' r:
                   invariant delta d' m' s' /\
                   hide_readers (get vDisk0 s') = get vdisk s /\
                   get vdisk s' = get vdisk s /\
                   guar delta tid s s' /\
                   s0' = s0
              }} cache_commit.
  Proof.
    hoare.
  Admitted.

End ConcurrentCache.