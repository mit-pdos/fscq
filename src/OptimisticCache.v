Require Import CCL.

Require Import Mem Pred AsyncDisk.
Require Import MemCache.
Require Import FunctionalExtensionality.
Require Import UpdList.

(* re-export WriteBuffer since it's part of external type signatures *)
Require Export WriteBuffer.

Definition Disk := @mem addr addr_eq_dec valu.

(* TODO: move CacheMem and CacheAbstraction into section; fix implicit types if
necessary *)

(** a complete memory, consisting of the cache plus the memory in *)
Inductive CacheMem St :=
  cacheMem { cache: Cache;
             cache_other_mem : Mem St; }.

Arguments cacheMem {St} cache cache_other_mem.

(** a complete abstract state, consisting of the cache state plus the
abstraction in St *)
Inductive CacheAbstraction St :=
  cacheS { vdisk_committed: Disk;
           vdisk: Disk;
           cache_other_s: Abstraction St; }.

Arguments cacheS {St} vdisk_committed vdisk cache_other_s.

Section OptimisticCache.

  (** OtherSt is arbitrary and provides the non-cache part of the state *)
  Context {OtherSt:StateTypes}.
  (* TODO: might be unideal for the cache to take this identifier, unless it can
  be nicely shadowed in all callers *)
  Definition St : StateTypes :=
    {| Mem := CacheMem OtherSt;
       Abstraction := CacheAbstraction OtherSt; |}.

  (** the protocol is arbitrary for the cache, other than being over a cache set
  of state types *)
  Variable G:TID -> Sigma St -> Sigma St -> Prop.

  Implicit Types (m:Mem St) (s: Abstraction St).

  Definition set_cache m c : Mem St :=
    cacheMem c (cache_other_mem m).

  Definition set_vdisk s vd : Abstraction St :=
    cacheS (vdisk_committed s) vd (cache_other_s s).
  Definition set_vdisk0 s vd0 : Abstraction St :=
    cacheS vd0 (vdisk s) (cache_other_s s).

  Definition locally_modified (sigma sigma': Sigma St) :=
    cache_other_mem (Sigma.mem sigma') = cache_other_mem (Sigma.mem sigma) /\
    cache_other_s (Sigma.s sigma') = cache_other_s (Sigma.s sigma) /\
    Sigma.l sigma' = Sigma.l sigma.

  Theorem locally_modified_refl : forall sigma, locally_modified sigma sigma.
  Proof.
    unfold locally_modified.
    auto.
  Qed.

  Theorem locally_modified_hashmap : forall sigma sz buf,
      locally_modified sigma (Sigma.upd_hm (sz:=sz) sigma buf).
  Proof.
    unfold locally_modified.
    destruct sigma; simpl in *; auto.
  Qed.

  Theorem locally_modified_trans : forall sigma sigma' sigma'',
      locally_modified sigma sigma' ->
      locally_modified sigma' sigma'' ->
      locally_modified sigma sigma''.
  Proof.
    unfold locally_modified.
    destruct sigma, sigma', sigma''; simpl in *;
      intuition;
      congruence.
  Qed.

  Ltac simplify :=
    subst;
    simpl;
    autorewrite with cache upd in *;
    repeat simpl_match;
    auto.

  Implicit Types (c:Cache) (wb:WriteBuffer).

  Definition BufferRead wb a : @cprog St _ :=
    match wb_get wb a with
    | Written v => Ret (Some v)
    | WbMissing => Ret (None)
    end.

  Definition ClearPending m wb a :=
    v <- WaitForRead a;
      let c := cache m in
      let c' := add_entry Clean c a v in
      _ <- Assgn (set_cache m c');
        (* note that v could also be added to the local write buffer (not
           returned since it isn't modified), which should improve
           performance *)
        Ret v.

  Definition CacheRead wb a l : @cprog St _ :=
    r <- BufferRead wb a;
      match r with
      | Some v => Ret (Some v, wb)
      | None => m <- Get (St:=St);
                 let c := cache m in
                 match cache_get c a with
                 | Present v _ => Ret (Some v, wb)
                 | Missing => if CanWrite l then
                               _ <- BeginRead a;
                               let c' := mark_pending c a in
                               _ <- Assgn (set_cache m c');
                                 Ret (None, wb)
                             else Ret (None, wb)
                 | Invalid => if CanWrite l then
                               v <- ClearPending m wb a;
                                 Ret (Some v, wb)
                             else Ret (None, wb)
                 end
      end.

  Definition cache_rep (d: DISK) (c: Cache) (vd0: Disk) :=
    forall a, match cache_get c a with
         | Present v dirty => vd0 a = Some v /\
                             if dirty then exists v0, d a = Some (v0, NoReader)
                             else d a = Some (v, NoReader)
         | Invalid => exists v0, d a = Some (v0, Pending) /\
                           vd0 a = Some v0
         | Missing => match vd0 a with
                     | Some v => d a = Some (v, NoReader)
                     | None => d a = None
                     end
         end.

  Definition wb_rep (vd0: Disk) (wb: WriteBuffer) (vd: Disk) :=
    forall a, match wb_get wb a with
         | Written v => vd a = Some v /\
                       exists v0, vd0 a = Some v0
         | WbMissing => vd a = vd0 a
         end.

  Definition no_pending_dirty (c: Cache) (wb: WriteBuffer) :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Definition CacheRep wb (sigma:Sigma St) :=
    cache_rep (Sigma.disk sigma) (cache (Sigma.mem sigma))
              (vdisk_committed (Sigma.s sigma)) /\
    wb_rep (vdisk_committed (Sigma.s sigma)) wb
           (vdisk (Sigma.s sigma)) /\
    no_pending_dirty (cache (Sigma.mem sigma)) wb.

  Ltac solve_cache :=
    unfold CacheRep; intuition;
    repeat match goal with
           | [ a: addr, H: cache_rep _ _ _ |- _ ] =>
             specialize (H a)
           | [ a: addr, H: wb_rep _ _ _ |- _ ] =>
             specialize (H a)
           end;
    repeat simpl_match;
    repeat deex;
    intuition eauto; try congruence.

  Lemma Buffer_hit:
    forall (wb : WriteBuffer) (a : addr) (v : valu),
      wb_get wb a = Written v ->
      forall (sigma : Sigma St) (a0 : valu),
        CacheRep wb sigma -> vdisk (Sigma.s sigma) a = Some a0 -> v = a0.
  Proof.
    solve_cache.
  Qed.

  Lemma Buffer_miss:
    forall (wb : WriteBuffer) (a : addr),
      wb_get wb a = WbMissing ->
      forall (sigma : Sigma St) (a0 : valu),
        CacheRep wb sigma ->
        vdisk (Sigma.s sigma) a = Some a0 ->
        vdisk_committed (Sigma.s sigma) a = Some a0.
  Proof.
    solve_cache.
  Qed.

  Hint Resolve Buffer_hit Buffer_miss.

  Definition BufferRead_ok : forall tid wb a,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
                         vdisk (Sigma.s sigma) a = Some v0;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma' = sigma /\
                           match r with
                           | Some v => v = v0
                           | None => vdisk_committed (Sigma.s sigma) a = Some v0 /\
                                    wb_get wb a = WbMissing
                           end /\
                           sigma_i' = sigma_i|})
                 (BufferRead wb a).
  Proof.
    unfold BufferRead; intros.

    case_eq (wb_get wb a); intros.
    step.

    step.
    intuition eauto.

    step.

    step.
    intuition eauto.
  Qed.

  Hint Extern 0 {{ BufferRead _ _; _ }} => apply BufferRead_ok : prog.

  Lemma CacheRep_clear_pending:
    forall (wb : WriteBuffer) (a : addr) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap) l (a0 : valu),
      CacheRep wb (state d m s hm l) ->
      cache_get (cache m) a = Invalid ->
      vdisk s a = Some a0 ->
      CacheRep wb
               (state (upd d a (a0, NoReader))
                      (set_cache m (add_entry Clean (cache m) a a0)) s hm l).
  Proof.
    unfold CacheRep; intuition; simpl in *; simplify.
    - intro a'.
      destruct (addr_eq_dec a a'); simplify.
      specialize (H4 a'); intuition.
      specialize (H a'); simpl_match.
      congruence.
      solve_cache.
    - intro a'.
      destruct (addr_eq_dec a a'); simplify.
  Qed.

  Hint Resolve CacheRep_clear_pending.

  Lemma CacheRep_present:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (a0 : valu),
      CacheRep wb sigma ->
      vdisk_committed (Sigma.s sigma) a = Some a0 ->
      forall (v : valu) (b : DirtyBit),
        cache_get (cache (Sigma.mem sigma)) a = Present v b -> v = a0.
  Proof.
    solve_cache.
  Qed.

  Lemma CacheRep_invalid:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (a0 : valu),
      CacheRep wb sigma ->
      vdisk (Sigma.s sigma) a = Some a0 ->
      cache_get (cache (Sigma.mem sigma)) a = Invalid ->
      Sigma.disk sigma a = Some (a0, Pending).
  Proof.
    solve_cache.
    specialize (H4 a); intuition eauto.
    simpl_match; congruence.
  Qed.

  Lemma CacheRep_missing:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (a0 : valu),
      CacheRep wb sigma ->
      vdisk_committed (Sigma.s sigma) a = Some a0 ->
      cache_get (cache (Sigma.mem sigma)) a = Missing ->
      Sigma.disk sigma a = Some (a0, NoReader).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve CacheRep_present CacheRep_invalid CacheRep_missing.

  Lemma CacheRep_finish_read:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (v0 : valu),
      vdisk (Sigma.s sigma) a = Some v0 ->
      CacheRep wb sigma ->
      wb_get wb a = WbMissing ->
      cache_get (cache (Sigma.mem sigma)) a = Invalid ->
      CacheRep wb
               (Sigma.set_mem
                  (Sigma.upd_disk sigma (fun d : DISK => upd d a (v0, NoReader)))
                  (set_cache (Sigma.mem sigma)
                             (add_entry Clean (cache (Sigma.mem sigma)) a v0))).
  Proof.
    unfold CacheRep; intuition; simplify.

    - intro a'.
      destruct (addr_eq_dec a a'); subst; simplify.
      destruct sigma; simpl in *; simplify; intuition eauto.
      solve_cache.

      destruct sigma; simpl in *; simplify.
      solve_cache.
    - intro a'.
      destruct (addr_eq_dec a a'); simplify.
      destruct sigma; simpl in *.
      solve_cache.

      specialize (H0 a').
      destruct sigma; simpl in *; eauto.
    - destruct sigma; simpl in *; simplify.
      intros a'.
      destruct (addr_eq_dec a a'); simplify.
  Qed.

  Lemma CacheRep_mark_pending:
    forall (wb : WriteBuffer) (a : addr) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap) l (a0 : valu),
      CacheRep wb (state d m s hm l) ->
      vdisk_committed s a = Some a0 ->
      wb_get wb a = WbMissing ->
      cache_get (cache m) a = Missing ->
      CacheRep wb
               (state (upd d a (a0, Pending)) (set_cache m (mark_pending (cache m) a))
                      s hm l).
  Proof.
    unfold CacheRep; intuition; simpl in *; simplify.
    - intro a'.
      destruct (addr_eq_dec a a'); simplify.
      solve_cache.
      solve_cache.
    - intro a'.
      destruct (addr_eq_dec a a'); simplify.
  Qed.

  Hint Resolve CacheRep_finish_read CacheRep_mark_pending.

  Ltac state_upd :=
    simpl in *; subst;
    eauto.

  Tactic Notation "state" "upd" constr(sigma) := destruct sigma; state_upd.
  Tactic Notation "state" "upd" constr(sigma) "," constr(sigma') := destruct sigma, sigma'; state_upd.

  Ltac prove_local_modify :=
    match goal with
    | [ |- locally_modified ?sigma ?sigma' ] =>
      unfold locally_modified;
      (try (is_var sigma; destruct sigma));
      (try (is_var sigma'; destruct sigma'));
      intuition idtac;
      simpl in *;
      subst;
      eauto; try congruence
    end.

  Hint Extern 2 (locally_modified ?sigma ?sigma') => prove_local_modify.

  Ltac state_upd_ctx :=
    match goal with
    | [ sigma: Sigma St, sigma': Sigma St |- _ ] =>
      state upd sigma, sigma'
    | [ sigma: Sigma St |- _ ] =>
      state upd sigma
    end.

  Hint Extern 2 (vdisk (Sigma.s _) = _) => state_upd_ctx.
  Hint Extern 2 (vdisk_committed (Sigma.s _) = _) => state_upd_ctx.
  Hint Extern 2 (Sigma.hm _ = Sigma.hm _) => state_upd_ctx.
  Hint Extern 2 (Sigma.l _ = _) => state_upd_ctx.
  Hint Extern 2 (CacheRep _ _) => state_upd_ctx.

  Hint Resolve locally_modified_refl.

  Theorem ClearPending_ok : forall tid m wb a,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
                         Sigma.l sigma = WriteLock /\
                         m = Sigma.mem sigma /\
                         cache_get (cache m) a = Invalid /\
                         vdisk (Sigma.s sigma) a = Some v0;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           CacheRep wb sigma' /\
                           locally_modified sigma sigma' /\
                           cache_get (cache (Sigma.mem sigma')) a = Present v0 Clean /\
                           Sigma.s sigma' = Sigma.s sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           r = v0 /\
                           sigma_i' = sigma_i|})
                 (ClearPending m wb a).
  Proof.
    unfold ClearPending.
    hoare.

    state upd sigma; intuition; simplify.
  Qed.

  Hint Extern 0 {{ ClearPending _ _ _; _ }} => apply ClearPending_ok : prog.

  Definition CacheRead_ok : forall tid wb a l,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
                         Sigma.l sigma = l /\
                         ReadPermission l /\
                         vdisk (Sigma.s sigma) a = Some v0;
                       postcondition :=
                         fun '(sigma_i', sigma') '(r, wb') =>
                           CacheRep wb' sigma' /\
                           locally_modified sigma sigma' /\
                           vdisk (Sigma.s sigma') = vdisk (Sigma.s sigma) /\
                           vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           match r with
                           | Some v => v = v0
                           | None => True
                           end /\
                           sigma_i' = sigma_i |})
                 (CacheRead wb a l).
  Proof.
    unfold CacheRead.
    hoare.

    destruct r; step; simplify.
    intuition eauto.

    intuition eauto.
    rename r into m'.
    case_eq (cache_get (cache m') a); intros;
      hoare.

    destruct (CanWrite (Sigma.l sigma));
      hoare.

    destruct (CanWrite (Sigma.l sigma));
      hoare.
  Qed.

  Definition CacheWrite wb a v : @cprog St _ :=
    m <- Get (St:=St);
      _ <- match cache_get (cache m) a with
          | Invalid => _ <- ClearPending m wb a;
                        Ret tt
          | _ => Ret tt
          end;
      _ <- GhostUpdate (fun _ s => set_vdisk s (upd (vdisk s) a v));
      Ret (tt, wb_add wb a v).

  Lemma CacheRep_write:
    forall (wb : WriteBuffer) (a : addr) (v : valu) (d : DISK)
      (m : Mem St) (s : Abstraction St) (hm : hashmap) l
      (a0 : valu),
      CacheRep wb (state d m s hm l) ->
      vdisk s a = Some a0 ->
      cache_get (cache m) a <> Invalid ->
      CacheRep (wb_add wb a v) (state d m (set_vdisk s (upd (vdisk s) a v)) hm l).
  Proof.
    unfold CacheRep; intuition; simpl in *; simplify.
    - intro a'.
      destruct (addr_eq_dec a a'); simplify.
      solve_cache.
      case_eq (wb_get wb a'); intros; simpl_match;
        intuition eauto.
      exists a0; congruence.

      solve_cache.
    - intro a'; intros.
      destruct (addr_eq_dec a a'); simplify.
  Qed.

  Hint Resolve CacheRep_write.

  Hint Extern 2 (cache_get _ _ <> _) => congruence.

  Lemma locally_modified_lock_preserved : forall sigma sigma',
      locally_modified sigma sigma' ->
      Sigma.l sigma' = Sigma.l sigma.
  Proof.
    unfold locally_modified; intuition.
  Qed.

  Theorem CacheWrite_ok : forall tid wb a v,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
                         Sigma.l sigma = WriteLock /\
                         vdisk (Sigma.s sigma) a = Some v0;
                       postcondition :=
                         fun '(sigma_i', sigma') '(_, wb') =>
                           CacheRep wb' sigma' /\
                           locally_modified sigma sigma' /\
                           vdisk (Sigma.s sigma') = upd (vdisk (Sigma.s sigma)) a v  /\
                           vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           sigma_i' = sigma_i |})
                 (CacheWrite wb a v).
  Proof.
    unfold CacheWrite.
    hoare.
    rename r into m'.
    case_eq (cache_get (cache m') a);
      hoare.
    intuition.
    erewrite locally_modified_lock_preserved; eauto.

    hoare.
    state upd sigma, sigma'; intuition eauto.
  Qed.

  Fixpoint add_writes (c:Cache) (wrs: list (addr * valu)) :=
    match wrs with
    | nil => c
    | (a,v) :: wrs' => add_entry Dirty (add_writes c wrs') a v
    end.

  Definition upd_with_buffer (c:Cache) (wb:WriteBuffer) :=
    add_writes c (wb_writes wb).

  Definition CacheCommit wb :=
    m <- Get (St:=St);
      let c := cache m in
      _ <- Assgn (set_cache m (upd_with_buffer c wb));
        _ <- GhostUpdate (fun _ s => set_vdisk0 s (vdisk s));
        Ret tt.

  Lemma no_pending_dirty_empty : forall c,
      no_pending_dirty c empty_writebuffer.
  Proof.
    unfold no_pending_dirty; eauto.
  Qed.

  Lemma wb_rep_empty : forall vd,
      wb_rep vd empty_writebuffer vd.
  Proof.
    unfold wb_rep; intros; simpl; auto.
  Qed.

  Hint Resolve no_pending_dirty_empty wb_rep_empty.

  Theorem wb_rep_upd_all_ext : forall wb vd0 (vd: Disk) (a: addr),
      wb_rep vd0 wb vd ->
      vd a = upd_all (AEQ:=addr_eq_dec) vd0 (wb_writes wb) a.
  Proof.
    intro.
    assert (forall a v, wb_get wb a = Written v <-> List.In (a, v) (wb_writes wb)).
    { intros; apply wb_get_writes. }
    intros.
    specialize (H a).
    pose proof (wb_writes_nodup_addr wb).
    move H1 at top.
    generalize dependent (wb_writes wb).
    induction l; intros; subst; simpl in *.
    - specialize (H0 a).
      case_eq (wb_get wb a); intros; simpl_match; auto.
      exfalso.
      eapply H; eauto.
    - destruct a0 as [a' v].
      destruct (addr_eq_dec a a'); subst; autorewrite with upd.
      + destruct (H v) as [H' ?]; clear H'.
        intuition.
        specialize (H0 a'); simpl_match; intuition.
      + simpl in *.
        inversion H1; subst; intuition.

        case_eq (wb_get wb a); intuition.
        specialize (H v0); intuition.
        congruence.
        erewrite upd_all_nodup_in by eauto.
        specialize (H0 a); simpl_match; intuition eauto.

        destruct (list_addr_in_dec addr_eq_dec a l);
          autorewrite with upd.
        destruct s.
        specialize (H x); intuition; congruence.
        specialize (H0 a); simpl_match; eauto.
  Qed.

  Corollary wb_rep_upd_all : forall vd0 wb vd,
      wb_rep vd0 wb vd ->
      vd = upd_all vd0 (wb_writes wb).
  Proof.
    intros.
    extensionality a.
    apply wb_rep_upd_all_ext; auto.
  Qed.

  Lemma cache_rep_add_dirty:
    forall (d : DISK) (a : addr) (v : valu) (c : Cache) (vd0 : Disk),
      cache_get c a <> Invalid ->
      (exists v0, vd0 a = Some v0) ->
      cache_rep d c vd0 ->
      cache_rep d (add_entry Dirty c a v) (upd vd0 a v).
  Proof.
    unfold cache_rep; intros; repeat deex.
    specialize (H1 a0).
    destruct (addr_eq_dec a a0); subst; simplify; intuition eauto.
    case_eq (cache_get c a0); intros; simpl_match; intuition.
    destruct b; repeat deex; intuition eauto.
    eauto.
  Qed.

  Lemma add_writes_same_invalid : forall ws c a,
      cache_get (add_writes c ws) a = Invalid ->
      cache_get c a = Invalid.
  Proof.
    induction ws; intros; simpl in *; auto.
    destruct a as [a v].
    destruct (addr_eq_dec a a0); subst;
      autorewrite with cache in H; auto.
    congruence.
  Qed.

  Hint Resolve upd_all_incr_domain.

  Lemma CacheRep_commit:
    forall (wb : WriteBuffer) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap) lock,
      CacheRep wb (state d m s hm lock) ->
      CacheRep empty_writebuffer
               (state d (set_cache m (upd_with_buffer (cache m) wb))
                      (set_vdisk0 s (vdisk s)) hm lock).
  Proof.
    unfold CacheRep; simpl; intuition; simplify.
    unfold upd_with_buffer.

    erewrite wb_rep_upd_all by eauto.
    assert (forall a v, List.In (a,v) (wb_writes wb) ->
                   wb_get wb a = Written v).
    intros; apply wb_get_writes; auto.
    generalize dependent (wb_writes wb); intros.
    induction l; simpl; eauto.
    destruct a as [a v].
    pose proof (H1 a v); simpl in *.
    match type of H3 with
    | ?P -> _ => let HP := fresh in
               assert P as HP by eauto;
                 specialize (H3 HP);
                 clear HP
    end.

    eapply cache_rep_add_dirty; eauto.
    - intro Hinvalid.
      apply add_writes_same_invalid in Hinvalid.
      specialize (H2 a); intuition auto.
      congruence.
    - specialize (H a); simpl_match; intuition eauto.
  Qed.

  Hint Resolve CacheRep_commit.

  Definition CacheCommit_ok : forall tid wb,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           CacheRep empty_writebuffer sigma' /\
                           locally_modified sigma sigma' /\
                           vdisk_committed (Sigma.s sigma') = vdisk (Sigma.s sigma) /\
                           vdisk (Sigma.s sigma') = vdisk (Sigma.s sigma) /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           sigma_i' = sigma_i |})
                 (CacheCommit wb).
  Proof.
    unfold CacheCommit.
    hoare.
  Qed.

  Definition CacheAbort : @cprog St _ :=
    _ <- GhostUpdate (fun _ s => set_vdisk s (vdisk_committed s));
      Ret tt.

  Lemma CacheRep_abort:
    forall (wb : WriteBuffer) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap) l,
      CacheRep wb (state d m s hm l) ->
      CacheRep empty_writebuffer (state d m (set_vdisk s (vdisk_committed s)) hm l).
  Proof.
    unfold CacheRep; simpl; intuition; simplify.
  Qed.

  Hint Resolve CacheRep_abort.

  Definition CacheAbort_ok : forall tid,
      cprog_spec G tid
                 (fun wb '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
                         (* this is needed for the ghost update, but actually
                         the current vdisk need not even be exposed and updated
                         via ghost state, since it's unobservable to other
                         threads (they need the writebuffer to make sense of
                         it)

                          the fix is to get rid of the vdisk ghost state, then
                          remove this function entirely, and expose the current
                          disk in CacheRep and cache specs only *)
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           CacheRep empty_writebuffer sigma' /\
                           locally_modified sigma sigma' /\
                           vdisk (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
                           vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           sigma_i' = sigma_i |})
                 (CacheAbort).
  Proof.
    unfold CacheAbort.
    hoare.
  Qed.

  Lemma wb_rep_empty' : forall vd0 vd,
      wb_rep vd0 empty_writebuffer vd ->
      vd0 = vd.
  Proof.
    unfold wb_rep; simpl; intros.
    extensionality a; eauto.
  Qed.

  Theorem CacheRep_empty : forall sigma,
      CacheRep empty_writebuffer sigma ->
      vdisk_committed (Sigma.s sigma) = vdisk (Sigma.s sigma).
  Proof.
    unfold CacheRep; intuition.
    destruct sigma, s; simpl in *.
    apply wb_rep_empty'; eauto.
  Qed.

End OptimisticCache.

Arguments St OtherSt : clear implicits.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)