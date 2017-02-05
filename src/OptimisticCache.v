Require Import CCL.

Require Import Mem Pred AsyncDisk.
Require Import MemCache WriteBuffer.
Require Import FunctionalExtensionality.

Require Import UpdList.

Definition Disk := @mem addr addr_eq_dec valu.

Record mem_var St T :=
  { get_var : Mem St -> T;
    set_var : Mem St -> T -> Mem St;
    get_set_id : forall m v, get_var (set_var m v) = v;
    set_get_id : forall m v, v = get_var m -> set_var m v = m;
    set_set : forall m v v', set_var (set_var m v) v' = set_var m v'; }.

Record g_var St T :=
  { get_gvar : Abstraction St -> T;
    set_gvar : Abstraction St -> T -> Abstraction St;
    get_set_g_id : forall s v, get_gvar (set_gvar s v) = v;
    set_get_g_id : forall s v, v = get_gvar s -> set_gvar s v = s;
    set_set_g : forall s v v', set_gvar (set_gvar s v) v' = set_gvar s v'; }.

Record CacheParams St :=
  { cache: mem_var St Cache;
    vdisk: g_var St Disk;
    vdisk_committed: g_var St Disk;
    vdisk_vdisk0_neq : forall s vd', get_gvar vdisk_committed (set_gvar vdisk s vd') =
                                get_gvar vdisk_committed s;
    vdisk0_vdisk_neq : forall s vd', get_gvar vdisk (set_gvar vdisk_committed s vd') =
                                get_gvar vdisk s; }.

Section OptimisticCache.

  Variable St:StateTypes.
  Variable G:TID -> Sigma St -> Sigma St -> Prop.

  Variable P:CacheParams St.

  Definition get_cache := get_var (cache P).
  Definition set_cache := set_var (cache P).
  Definition get_vdisk := get_gvar (vdisk P).
  Definition set_vdisk := set_gvar (vdisk P).
  Definition get_vdisk0 := get_gvar (vdisk_committed P).
  Definition set_vdisk0 := set_gvar (vdisk_committed P).

  Hint Rewrite (get_set_id (cache P)) : get_set.
  Hint Rewrite (set_get_id (cache P)) using solve [ auto ] : get_set.
  Hint Rewrite (set_set (cache P)) : get_set.
  Hint Rewrite (get_set_g_id (vdisk P)) : get_set.
  Hint Rewrite (set_get_g_id (vdisk P)) using solve [ auto ] : get_set.
  Hint Rewrite (set_set_g (vdisk P)) : get_set.
  Hint Rewrite (get_set_g_id (vdisk_committed P)) : get_set.
  Hint Rewrite (set_get_g_id (vdisk_committed P)) using solve [ auto ] : get_set.
  Hint Rewrite (set_set_g (vdisk_committed P)) : get_set.
  Hint Rewrite (vdisk_vdisk0_neq P) : get_set.
  Hint Rewrite (vdisk0_vdisk_neq P) : get_set.

  Definition locally_modified (sigma sigma': Sigma St) :=
    Sigma.mem sigma' = set_cache (Sigma.mem sigma) (get_cache (Sigma.mem sigma')) /\
    Sigma.s sigma' = set_vdisk (set_vdisk0 (Sigma.s sigma) (get_vdisk0 (Sigma.s sigma')))
                       (get_vdisk (Sigma.s sigma')).

  Theorem locally_modified_refl : forall sigma, locally_modified sigma sigma.
  Proof.
    unfold locally_modified.
    destruct sigma; simpl in *; autorewrite with get_set; auto.
  Qed.

  Theorem locally_modified_hashmap : forall sigma sz buf,
      locally_modified sigma (Sigma.upd_hm (sz:=sz) sigma buf).
  Proof.
    unfold locally_modified.
    destruct sigma; simpl in *; autorewrite with get_set; auto.
  Qed.

  Theorem locally_modified_trans : forall sigma sigma' sigma'',
      locally_modified sigma sigma' ->
      locally_modified sigma' sigma'' ->
      locally_modified sigma sigma''.
  Proof.
    unfold locally_modified.
    destruct sigma, sigma', sigma''; simpl in *; autorewrite with get_set in *;
      intuition auto.
    rewrite H1 in *.
    autorewrite with get_set in *; auto.

    admit. (* should really have only one ghost var, to avoid distinctness issues *)
  Admitted.

  Ltac simplify :=
    subst;
    simpl;
    autorewrite with get_set cache upd in *;
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
      let c := get_cache m in
      let c' := add_entry Clean c a v in
      _ <- Assgn (set_cache m c');
        (* note that v could also be added to the local write buffer (not
           returned since it isn't modified), which should improve
           performance *)
        Ret v.

  Definition CacheRead wb a : @cprog St _ :=
    r <- BufferRead wb a;
      match r with
      | Some v => Ret (Some v, wb)
      | None => m <- Get;
                 let c := get_cache m in
                 match cache_get c a with
               | Present v _ => Ret (Some v, wb)
               | Missing => _ <- BeginRead a;
                             let c' := mark_pending c a in
                             _ <- Assgn (set_cache m c');
                             Ret (None, wb)
               | Invalid => v <- ClearPending m wb a;
                             Ret (Some v, wb)
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
    cache_rep (Sigma.disk sigma) (get_cache (Sigma.mem sigma))
              (get_vdisk0 (Sigma.s sigma)) /\
    wb_rep (get_vdisk0 (Sigma.s sigma)) wb
           (get_vdisk (Sigma.s sigma)) /\
    no_pending_dirty (get_cache (Sigma.mem sigma)) wb.

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
        CacheRep wb sigma -> get_vdisk (Sigma.s sigma) a = Some a0 -> v = a0.
  Proof.
    solve_cache.
  Qed.

  Lemma Buffer_miss:
    forall (wb : WriteBuffer) (a : addr),
      wb_get wb a = WbMissing ->
      forall (sigma : Sigma St) (a0 : valu),
        CacheRep wb sigma ->
        get_vdisk (Sigma.s sigma) a = Some a0 ->
        get_vdisk0 (Sigma.s sigma) a = Some a0.
  Proof.
    solve_cache.
  Qed.

  Hint Resolve Buffer_hit Buffer_miss.

  Definition BufferRead_ok : forall tid wb a,
      cprog_triple G tid
                   (fun v0 '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma /\
                           get_vdisk (Sigma.s sigma) a = Some v0;
                         postcondition :=
                           fun '(sigma_i', sigma') r =>
                             sigma' = sigma /\
                             match r with
                             | Some v => v = v0
                             | None => get_vdisk0 (Sigma.s sigma) a = Some v0 /\
                                      wb_get wb a = WbMissing
                             end /\
                             sigma_i' = sigma_i|})
                   (BufferRead wb a).
  Proof.
    unfold cprog_triple, BufferRead; intros.

    case_eq (wb_get wb a); intros.
    step.

    intros.
    step.
    intuition eauto.

    step.

    intros; step.
    intuition eauto.
  Qed.

  Lemma CacheRep_missing_wb : forall wb sigma a,
      CacheRep wb sigma ->
      get_vdisk (Sigma.s sigma) a = None ->
      wb_get wb a = WbMissing.
  Proof.
    unfold CacheRep; intuition.
    specialize (H a).
    case_eq (wb_get wb a); intros; simpl_match; intuition eauto.
    congruence.
  Qed.

  Lemma CacheRep_missing_cache : forall wb sigma a,
      CacheRep wb sigma ->
      get_vdisk (Sigma.s sigma) a = None ->
      cache_get (get_cache (Sigma.mem sigma)) a = Missing.
  Proof.
    intros.
    assert (wb_get wb a = WbMissing).
    eapply CacheRep_missing_wb; eauto.
    unfold CacheRep in *; intuition.
    specialize (H a).
    specialize (H2 a).
    case_eq (cache_get (get_cache (Sigma.mem sigma)) a); intros;
      repeat simpl_match; intuition eauto;
        repeat deex;
        congruence.
  Qed.

  Lemma CacheRep_missing_disk : forall wb sigma a,
      CacheRep wb sigma ->
      get_vdisk (Sigma.s sigma) a = None ->
      Sigma.disk sigma a = None.
  Proof.
    intros.
    assert (wb_get wb a = WbMissing).
    eapply CacheRep_missing_wb; eauto.
    assert (cache_get (get_cache (Sigma.mem sigma)) a = Missing).
    eapply CacheRep_missing_cache; eauto.
    unfold CacheRep in *; intuition.
    specialize (H a).
    specialize (H3 a).
    repeat simpl_match.
    rewrite <- H in H3; simpl_match; auto.
  Qed.

  Definition BufferRead_oob : forall tid wb a,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma /\
                           get_vdisk (Sigma.s sigma) a = None;
                         postcondition :=
                           fun '(sigma_i', sigma') r =>
                             sigma' = sigma /\
                             r = None /\
                             sigma_i' = sigma_i|})
                   (BufferRead wb a).
  Proof.
    unfold cprog_triple, BufferRead; intros.

    case_eq (wb_get wb a); intros.
    step.
    assert (wb_get wb a = WbMissing).
    eapply CacheRep_missing_wb; eauto.
    congruence.

    step.
    step.
    intuition eauto.
  Qed.

  Hint Extern 0 {{ BufferRead _ _; _ }} => apply BufferRead_ok : prog.

  Lemma CacheRep_clear_pending:
    forall (wb : WriteBuffer) (a : addr) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap) (a0 : valu),
      CacheRep wb (state d m s hm) ->
      cache_get (get_cache m) a = Invalid ->
      get_vdisk s a = Some a0 ->
      CacheRep wb
               (state (upd d a (a0, NoReader))
                      (set_cache m (add_entry Clean (get_cache m) a a0)) s hm).
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
      get_vdisk0 (Sigma.s sigma) a = Some a0 ->
      forall (v : valu) (b : DirtyBit),
        cache_get (get_cache (Sigma.mem sigma)) a = Present v b -> v = a0.
  Proof.
    solve_cache.
  Qed.

  Lemma CacheRep_invalid:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (a0 : valu),
      CacheRep wb sigma ->
      get_vdisk (Sigma.s sigma) a = Some a0 ->
      cache_get (get_cache (Sigma.mem sigma)) a = Invalid ->
      Sigma.disk sigma a = Some (a0, Pending).
  Proof.
    solve_cache.
    specialize (H4 a); intuition eauto.
    simpl_match; congruence.
  Qed.

  Lemma CacheRep_missing:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (a0 : valu),
      CacheRep wb sigma ->
      get_vdisk0 (Sigma.s sigma) a = Some a0 ->
      cache_get (get_cache (Sigma.mem sigma)) a = Missing ->
      Sigma.disk sigma a = Some (a0, NoReader).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve CacheRep_present CacheRep_invalid CacheRep_missing.

  Lemma CacheRep_finish_read:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma St) (v0 : valu),
      get_vdisk (Sigma.s sigma) a = Some v0 ->
      CacheRep wb sigma ->
      wb_get wb a = WbMissing ->
      cache_get (get_cache (Sigma.mem sigma)) a = Invalid ->
      CacheRep wb
               (Sigma.set_mem
                  (Sigma.upd_disk sigma (fun d : DISK => upd d a (v0, NoReader)))
                  (set_cache (Sigma.mem sigma)
                             (add_entry Clean (get_cache (Sigma.mem sigma)) a v0))).
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
      (s : Abstraction St) (hm : hashmap) (a0 : valu),
      CacheRep wb (state d m s hm) ->
      get_vdisk0 s a = Some a0 ->
      wb_get wb a = WbMissing ->
      cache_get (get_cache m) a = Missing ->
      CacheRep wb
               (state (upd d a (a0, Pending)) (set_cache m (mark_pending (get_cache m) a))
                      s hm).
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

  Theorem ClearPending_ok : forall tid m wb a,
      cprog_triple G tid
                   (fun v0 '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma /\
                           m = Sigma.mem sigma /\
                           cache_get (get_cache m) a = Invalid /\
                           get_vdisk (Sigma.s sigma) a = Some v0;
                         postcondition :=
                           fun '(sigma_i', sigma') r =>
                             CacheRep wb sigma' /\
                             Sigma.mem sigma' = set_cache (Sigma.mem sigma) (get_cache (Sigma.mem sigma')) /\
                             cache_get (get_cache (Sigma.mem sigma')) a = Present v0 Clean /\
                             Sigma.s sigma' = Sigma.s sigma /\
                             Sigma.hm sigma' = Sigma.hm sigma /\
                             r = v0 /\
                             sigma_i' = sigma_i|})
                   (ClearPending m wb a).
  Proof.
    unfold cprog_triple, ClearPending; intros.
    step.

    eexists; intuition eauto.

    step.

    intros; step.
    intuition eauto.
    destruct sigma; simpl in *; eauto.

    destruct sigma; simpl in *; simplify.
    destruct sigma; simpl in *; simplify.
    destruct sigma; simpl in *; simplify.
    destruct sigma; simpl in *; simplify.
  Qed.

  Hint Extern 0 {{ ClearPending _ _ _; _ }} => apply ClearPending_ok : prog.

  (* prevent monad_simpl from unfolding for now *)
  Opaque ClearPending.

  Ltac state_upd :=
    simpl in *; subst;
    autorewrite with get_set in *;
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
      autorewrite with get_set in *;
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

  Hint Extern 2 (get_vdisk (Sigma.s _) = _) => state_upd_ctx.
  Hint Extern 2 (get_vdisk0 (Sigma.s _) = _) => state_upd_ctx.
  Hint Extern 2 (Sigma.hm _ = Sigma.hm _) => state_upd_ctx.

  Definition CacheRead_ok : forall tid wb a,
      cprog_triple G tid
                   (fun v0 '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma /\
                           get_vdisk (Sigma.s sigma) a = Some v0;
                         postcondition :=
                           fun '(sigma_i', sigma') '(r, wb') =>
                             CacheRep wb' sigma' /\
                             locally_modified sigma sigma' /\
                             get_vdisk (Sigma.s sigma') = get_vdisk (Sigma.s sigma) /\
                             get_vdisk0 (Sigma.s sigma') = get_vdisk0 (Sigma.s sigma) /\
                             Sigma.hm sigma' = Sigma.hm sigma /\
                             match r with
                             | Some v => v = v0
                             | None => True
                             end /\
                             sigma_i' = sigma_i |})
                   (CacheRead wb a).
  Proof.
    unfold cprog_triple, CacheRead; intros.

    step.
    eexists; intuition eauto.

    destruct r; step; simplify.
    intuition eauto.

    rename r into m'.
    case_eq (cache_get (get_cache m') a); intros.
    step; simplify.

    intuition eauto.

    step.
    eexists; intuition eauto.

    step.
    intuition eauto.

    step.
    eexists; intuition eauto.

    step.
    step.

    intuition eauto.

    state upd sigma.
  Qed.

  Definition CacheWrite wb a v : @cprog St _ :=
    m <- Get;
      _ <- match cache_get (get_cache m) a with
          | Invalid => _ <- ClearPending m wb a;
                        Ret tt
          | _ => Ret tt
          end;
    _ <- GhostUpdate (fun _ s => set_vdisk s (upd (get_vdisk s) a v));
    Ret (tt, wb_add wb a v).

  Lemma CacheRep_write:
    forall (wb : WriteBuffer) (a : addr) (v : valu) (d : DISK)
      (m : Mem St) (s : Abstraction St) (hm : hashmap)
      (a0 : valu),
      CacheRep wb (state d m s hm) ->
      get_vdisk s a = Some a0 ->
      cache_get (get_cache m) a <> Invalid ->
      CacheRep (wb_add wb a v) (state d m (set_vdisk s (upd (get_vdisk s) a v)) hm).
  Proof.
    unfold CacheRep; intuition; simpl in *; simplify.
    - fold (get_vdisk0 s) in *.
      intro a'.
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

  Theorem CacheWrite_ok : forall tid wb a v,
      cprog_triple G tid
                   (fun v0 '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma /\
                           get_vdisk (Sigma.s sigma) a = Some v0;
                         postcondition :=
                           fun '(sigma_i', sigma') '(_, wb') =>
                             CacheRep wb' sigma' /\
                             locally_modified sigma sigma' /\
                             get_vdisk (Sigma.s sigma') = upd (get_vdisk (Sigma.s sigma)) a v  /\
                             get_vdisk0 (Sigma.s sigma') = get_vdisk0 (Sigma.s sigma) /\
                             Sigma.hm sigma' = Sigma.hm sigma /\
                             sigma_i' = sigma_i |})
                   (CacheWrite wb a v).
  Proof.
    unfold cprog_triple, CacheWrite; intros.
    step.

    rename r into m'.
    case_eq (cache_get (get_cache m') a); intros.

    step.
    step; simplify.
    intuition eauto.
    state upd sigma.

    step.
    eexists; intuition eauto.
    step.
    step.
    intuition eauto.

    state upd sigma, sigma'.
    state upd sigma, sigma'.

    step.
    step.

    intuition eauto.
    state upd sigma.
  Qed.

  Fixpoint add_writes (c:Cache) (wrs: list (addr * valu)) :=
    match wrs with
    | nil => c
    | (a,v) :: wrs' => add_entry Dirty (add_writes c wrs') a v
    end.

  Definition upd_with_buffer (c:Cache) (wb:WriteBuffer) :=
    add_writes c (wb_writes wb).

  Definition CacheCommit wb :=
    m <- Get;
      let c := get_cache m in
      _ <- Assgn (set_cache m (upd_with_buffer c wb));
        _ <- GhostUpdate (fun _ s => set_vdisk0 s (get_vdisk s));
        Ret (tt, empty_writebuffer).

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
      (s : Abstraction St) (hm : hashmap),
      CacheRep wb (state d m s hm) ->
      CacheRep empty_writebuffer
               (state d (set_cache m (upd_with_buffer (get_cache m) wb))
                      (set_vdisk0 s (get_vdisk s)) hm).
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

  Lemma CacheRep_abort:
    forall (wb : WriteBuffer) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap),
      CacheRep wb (state d m s hm) ->
      CacheRep empty_writebuffer (state d m (set_vdisk s (get_vdisk0 s)) hm).
  Proof.
    unfold CacheRep; simpl; intuition; simplify.
  Qed.

  Hint Resolve CacheRep_commit CacheRep_abort.

  Definition CacheCommit_ok : forall tid wb,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma;
                         postcondition :=
                           fun '(sigma_i', sigma') '(_, wb') =>
                             CacheRep wb' sigma' /\
                             locally_modified sigma sigma' /\
                             get_vdisk0 (Sigma.s sigma') = get_vdisk (Sigma.s sigma) /\
                             get_vdisk (Sigma.s sigma') = get_vdisk (Sigma.s sigma) /\
                             Sigma.hm sigma' = Sigma.hm sigma /\
                             sigma_i' = sigma_i |})
                   (CacheCommit wb).
  Proof.
    unfold cprog_triple, CacheCommit; intros.

    step.
    step.
    step.
    step.

    intuition eauto.
    state upd sigma.

    prove_local_modify.
    rewrite (set_get_g_id (vdisk P)) by simplify.
    auto.
  Qed.

  Definition CacheAbort wb : @cprog St _ :=
    _ <- GhostUpdate (fun _ s => set_vdisk s (get_vdisk0 s));
    Ret (tt, empty_writebuffer).

  Definition CacheAbort_ok : forall tid wb,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma;
                         postcondition :=
                           fun '(sigma_i', sigma') '(_, wb') =>
                             CacheRep wb' sigma' /\
                             locally_modified sigma sigma' /\
                             get_vdisk (Sigma.s sigma') = get_vdisk0 (Sigma.s sigma) /\
                             get_vdisk0 (Sigma.s sigma') = get_vdisk0 (Sigma.s sigma) /\
                             Sigma.hm sigma' = Sigma.hm sigma /\
                             sigma_i' = sigma_i |})
                   (CacheAbort wb).
  Proof.
    unfold cprog_triple, CacheAbort; intros.

    step.
    step.

    intuition eauto.
    state upd sigma.
  Qed.

End OptimisticCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)