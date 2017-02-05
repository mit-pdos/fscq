Require Import CCL.

Require Import Mem Pred AsyncDisk.

Require Import MemCache WriteBuffer.

Definition Disk := @mem addr addr_eq_dec valu.

Record mem_var St T :=
  { get_var : Mem St -> T;
    set_var : Mem St -> T -> Mem St;
    get_set_id : forall m v, get_var (set_var m v) = v;
    set_get_id : forall m v, v = get_var m -> set_var m v = m}.

Record g_var St T :=
  { get_gvar : Abstraction St -> T;
    set_gvar : Abstraction St -> T -> Abstraction St;
    get_set_g_id : forall s v, get_gvar (set_gvar s v) = v;
    set_get_g_id : forall s v, v = get_gvar s -> set_gvar s v = s}.

Record CacheParams St :=
  { cache: mem_var St Cache;
    vdisk: g_var St Disk;
    vdisk_committed: g_var St Disk;
    vdisk_vdisk0_neq : forall s vd', get_gvar vdisk_committed (set_gvar vdisk s vd') =
                                get_gvar vdisk_committed s }.

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
    unfold CacheRep; intuition; simpl in *.
    - intro a'.
      rewrite (get_set_id (cache P)).
      destruct (addr_eq_dec a a'); subst.
      rewrite cache_get_add_eq; intuition eauto.
      specialize (H4 a'); intuition.
      specialize (H a'); simpl_match.
      congruence.
      autorewrite with upd; eauto.

      rewrite cache_get_add_neq; intuition eauto.
      autorewrite with upd.
      solve_cache.
    - intro a'.
      rewrite (get_set_id (cache P)).
      destruct (addr_eq_dec a a'); subst.
      rewrite cache_get_add_eq; intuition eauto.
      rewrite cache_get_add_neq; intuition eauto.
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
    unfold CacheRep; intuition.

    - intro a'.
      destruct (addr_eq_dec a a'); subst; intros.
      destruct sigma; simpl in *.
      rewrite (get_set_id (cache P)).
      rewrite cache_get_add_eq; intuition eauto.
      solve_cache.
      autorewrite with upd; eauto.

      destruct sigma; simpl in *.
      rewrite (get_set_id (cache P)).
      rewrite cache_get_add_neq; intuition eauto.
      solve_cache.
      autorewrite with upd; eauto.

    - intro a'.
      destruct (addr_eq_dec a a'); subst; intros.
      destruct sigma; simpl in *.
      solve_cache.

      specialize (H0 a').
      destruct sigma; simpl in *; eauto.

    - destruct sigma; simpl in *.
      rewrite (get_set_id (cache P)).

      intros a'.
      destruct (addr_eq_dec a a'); subst.
      rewrite cache_get_add_eq; intuition eauto.
      rewrite cache_get_add_neq; intuition eauto.
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
    unfold CacheRep; intuition; simpl in *.
    - intro a'.
      rewrite (get_set_id (cache P)).

      destruct (addr_eq_dec a a'); subst; autorewrite with upd.
      rewrite cache_get_pending_eq; solve_cache.

      rewrite cache_get_pending_neq by auto; solve_cache.
    - rewrite (get_set_id (cache P)).
      intro a'.
      destruct (addr_eq_dec a a'); subst.
      rewrite cache_get_pending_eq; intuition eauto.
      rewrite cache_get_pending_neq; intuition eauto.
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

    destruct sigma; simpl in *.
    rewrite (get_set_id (cache P)); auto.

    destruct sigma; simpl in *.
    rewrite (get_set_id (cache P)).
    rewrite cache_get_add_eq; auto.

    destruct sigma; simpl in *; auto.
  Qed.

  Hint Extern 0 {{ ClearPending _ _ _; _ }} => apply ClearPending_ok : prog.

  (* prevent monad_simpl from unfolding for now *)
  Opaque ClearPending.

  Definition CacheRead_ok : forall tid wb a,
      cprog_triple G tid
                   (fun v0 '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma /\
                           get_vdisk (Sigma.s sigma) a = Some v0;
                         postcondition :=
                           fun '(sigma_i', sigma') '(r, wb') =>
                             CacheRep wb' sigma' /\
                             Sigma.mem sigma' = set_cache (Sigma.mem sigma) (get_cache (Sigma.mem sigma')) /\
                             Sigma.s sigma' = Sigma.s sigma /\
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

    destruct r; step.
    rewrite (set_get_id (cache P)); auto.
    intuition eauto.

    intros m'.
    case_eq (cache_get (get_cache m') a); intros.
    step.

    rewrite (set_get_id (cache P)); auto.
    intuition eauto.

    step.
    eexists; intuition eauto.

    step.
    intuition eauto.

    step.
    eexists; intuition eauto.

    step.
    intros; step.

    destruct sigma; simpl in *.
    rewrite (get_set_id (cache P)).
    intuition eauto.
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
    unfold CacheRep; intuition; simpl in *.
    - unfold get_vdisk0, set_vdisk in *.
      rewrite (vdisk_vdisk0_neq P).
      eauto.

    - rewrite (vdisk_vdisk0_neq P).
      fold (get_vdisk0 s) in *.
      rewrite (get_set_g_id (vdisk P)).
      intro a'.
      destruct (addr_eq_dec a a'); subst; autorewrite with upd.
      rewrite wb_get_add_eq; intuition eauto.
      solve_cache.
      case_eq (wb_get wb a'); intros; simpl_match;
        intuition eauto.
      exists a0; congruence.

      rewrite wb_get_add_neq by auto; intuition eauto.
      solve_cache.

    - intro a'; intros.
      destruct (addr_eq_dec a a'); subst.
      congruence.

      rewrite wb_get_add_neq by auto.
      specialize (H4 a'); eauto.
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
                             let vd' := upd (get_vdisk (Sigma.s sigma)) a v in
                             Sigma.s sigma' = set_vdisk (Sigma.s sigma) vd'  /\
                             Sigma.mem sigma' = set_cache (Sigma.mem sigma) (get_cache (Sigma.mem sigma')) /\
                             get_vdisk (Sigma.s sigma') a = Some v /\
                             sigma_i' = sigma_i |})
                   (CacheWrite wb a v).
  Proof.
    unfold cprog_triple, CacheWrite; intros.
    step.

    intros m'.
    case_eq (cache_get (get_cache m') a); intros.

    step.
    intros; step.
    intuition eauto.
    destruct sigma; simpl in *; intuition eauto.

    destruct sigma; simpl in *; auto.
    destruct sigma; simpl in *; auto.
    rewrite (set_get_id (cache P)); auto.
    destruct sigma; simpl in *; auto.

    rewrite (get_set_g_id (vdisk P)).
    autorewrite with upd; auto.

    step.
    eexists; intuition eauto.
    step.
    intros; step.
    intuition eauto.

    destruct sigma'; simpl in *; subst; intuition eauto.
    destruct sigma'; simpl in *; subst; intuition eauto.
    destruct sigma'; simpl in *; subst; intuition eauto.
    destruct sigma'; simpl in *; subst; intuition eauto.
    rewrite (get_set_g_id (vdisk P));
      autorewrite with upd;
      eauto.

    step.
    intros; step.
    intuition eauto.
    destruct sigma; simpl in *; intuition eauto.
    destruct sigma; simpl in *; intuition eauto.
    destruct sigma; simpl in *; intuition eauto.
    rewrite (set_get_id (cache P)); auto.
    destruct sigma; simpl in *; intuition eauto.
    rewrite (get_set_g_id (vdisk P));
      autorewrite with upd;
      auto.
  Qed.

  (* TODO: implement *)
  Definition add_writes (c:Cache) (wb:WriteBuffer) := c.

  Definition CacheCommit wb :=
    m <- Get;
      let c := get_cache m in
      _ <- Assgn (set_cache m (add_writes c wb));
        _ <- GhostUpdate (fun _ s => set_vdisk0 s (get_vdisk s));
        Ret (tt, empty_writebuffer).

  Definition CacheCommit_ok : forall tid wb,
      cprog_triple G tid
                   (fun (_:unit) '(sigma_i, sigma) =>
                      {| precondition :=
                           CacheRep wb sigma;
                         postcondition :=
                           fun '(sigma_i', sigma') '(_, wb') =>
                             CacheRep wb' sigma' /\
                             Sigma.mem sigma' = set_cache (Sigma.mem sigma) (get_cache (Sigma.mem sigma')) /\
                             Sigma.s sigma' = set_vdisk0 (Sigma.s sigma) (get_vdisk (Sigma.s sigma)) /\
                             sigma_i' = sigma_i |})
                   (CacheCommit wb).
  Proof.
  Abort.

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
                             Sigma.mem sigma' = set_cache (Sigma.mem sigma) (get_cache (Sigma.mem sigma')) /\
                             Sigma.s sigma' = set_vdisk (Sigma.s sigma) (get_vdisk0 (Sigma.s sigma)) /\
                             sigma_i' = sigma_i |})
                   (CacheAbort wb).
  Proof.
  Abort.

End OptimisticCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)