Require Import CCL.

Require Import Mem Pred AsyncDisk.
Require Import MemCache.
Require Import FunctionalExtensionality.
Require Import UpdList.

(* re-export WriteBuffer since it's part of external type signatures *)
Require Export WriteBuffer.

Notation Disk := (@mem addr addr_eq_dec valu).

Record CacheParams :=
  { cache : ident;
    vdisk : ident;
    vdisk_committed : ident; }.

Section OptimisticCache.

  Implicit Types (c:Cache) (wb:WriteBuffer).

  Definition cache_rep (d: DISK) c (vd0: Disk) :=
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

  Definition wb_rep (vd0: Disk) wb (vd: Disk) :=
    forall a, match wb_get wb a with
         | Written v => vd a = Some v /\
                       exists v0, vd0 a = Some v0
         | WbMissing => vd a = vd0 a
         end.

  Definition no_pending_dirty c wb :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Variable (P:CacheParams).
  Variable G:Protocol.

  Definition CacheRep d wb (vd0 vd:Disk) : heappred :=
    (exists c, cache P |-> val c *
          vdisk_committed P |-> absMem vd0 *
          vdisk P |-> absMem vd *
          [[ cache_rep d c vd0 ]] *
          [[ wb_rep vd0 wb vd ]] *
          [[ no_pending_dirty c wb ]]
    )%pred.

  Definition BufferRead wb a :=
    match wb_get wb a with
    | Written v => Ret (Some v)
    | WbMissing => Ret (None)
    end.

  Definition ClearPending c wb a :=
    v <- WaitForRead a;
      let c' := add_entry Clean c a v in
      _ <- Assgn (cache P) c';
        (* note that v could also be added to the local write buffer (not
           returned since it isn't modified), which should improve
           performance *)
        Ret v.

  Definition CacheRead wb a :=
    r <- BufferRead wb a;
      match r with
      | Some v => Ret (Some v, wb)
      | None => c <- Get _ (cache P);
                 match cache_get c a with
                 | Present v _ => Ret (Some v, wb)
                 | Missing => _ <- BeginRead a;
                               let c' := mark_pending c a in
                               _ <- Assgn (cache P) c';
                                 Ret (None, wb)
                 | Invalid => v <- ClearPending c wb a;
                               Ret (Some v, wb)
                 end
      end.

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

  Ltac simplify :=
    repeat match goal with
           | [ H: context[let (n, m) := ?a in _] |- _ ] =>
             let n := fresh n in
             let m := fresh m in
             destruct a as [m n]
           | _ => progress simpl in *
           | _ => progress subst
           | _ => intuition eauto
           end.

  Definition BufferRead_ok : forall tid wb a,
      cprog_spec G tid
                 (fun '(F, vd0, vd, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         (F * CacheRep (Sigma.disk sigma) wb vd0 vd)%pred (Sigma.mem sigma) /\
                         vd a = Some v0;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma' = sigma /\
                           match r with
                           | Some v => v = v0
                           | None => wb_get wb a = WbMissing
                           end /\
                           sigma_i' = sigma_i|})
                 (BufferRead wb a).
  Proof.
    unfold BufferRead; intros.

    case_eq (wb_get wb a); intros.
    step.
    simplify.

    step.
    simplify.
    admit. (* need to extract props from CacheRep *)

    step.
    simplify.

    step.
    simplify.
  Admitted.

  Hint Extern 0 {{ BufferRead _ _; _ }} => apply BufferRead_ok : prog.

  Lemma CacheRep_clear_pending:
    forall (wb : WriteBuffer) (a : addr) (d : DISK) (m : Mem St)
      (s : Abstraction St) (hm : hashmap) (a0 : valu),
      CacheRep wb (state d m s hm) ->
      cache_get (cache m) a = Invalid ->
      vdisk s a = Some a0 ->
      CacheRep wb
               (state (upd d a (a0, NoReader))
                      (set_cache m (add_entry Clean (cache m) a a0)) s hm).
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
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma) (a0 : valu),
      CacheRep wb sigma ->
      vdisk_committed (Sigma.s sigma) a = Some a0 ->
      forall (v : valu) (b : DirtyBit),
        cache_get (cache (Sigma.mem sigma)) a = Present v b -> v = a0.
  Proof.
    solve_cache.
  Qed.

  Lemma CacheRep_invalid:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma) (a0 : valu),
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
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma) (a0 : valu),
      CacheRep wb sigma ->
      vdisk_committed (Sigma.s sigma) a = Some a0 ->
      cache_get (cache (Sigma.mem sigma)) a = Missing ->
      Sigma.disk sigma a = Some (a0, NoReader).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve CacheRep_present CacheRep_invalid CacheRep_missing.

  Lemma CacheRep_finish_read:
    forall (wb : WriteBuffer) (a : addr) (sigma : Sigma) (v0 : valu),
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
      (s : Abstraction St) (hm : hashmap) (a0 : valu),
      CacheRep wb (state d m s hm) ->
      vdisk_committed s a = Some a0 ->
      wb_get wb a = WbMissing ->
      cache_get (cache m) a = Missing ->
      CacheRep wb
               (state (upd d a (a0, Pending)) (set_cache m (mark_pending (cache m) a))
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
    | [ sigma: Sigma, sigma': Sigma |- _ ] =>
      state upd sigma, sigma'
    | [ sigma: Sigma |- _ ] =>
      state upd sigma
    end.

  Hint Extern 2 (vdisk (Sigma.s _) = _) => state_upd_ctx.
  Hint Extern 2 (vdisk_committed (Sigma.s _) = _) => state_upd_ctx.
  Hint Extern 2 (Sigma.hm _ = Sigma.hm _) => state_upd_ctx.
  Hint Extern 2 (CacheRep _ _) => state_upd_ctx.

  Hint Resolve locally_modified_refl.

  Theorem ClearPending_ok : forall tid m wb a,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
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

  Definition CacheRead_ok : forall tid wb a,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
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
                 (CacheRead wb a).
  Proof.
    unfold CacheRead.
    hoare.

    destruct r; step; simplify.
    intuition eauto.

    rename r into m'.
    case_eq (cache_get (cache m') a); intros;
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
      (m : Mem St) (s : Abstraction St) (hm : hashmap)
      (a0 : valu),
      CacheRep wb (state d m s hm) ->
      vdisk s a = Some a0 ->
      cache_get (cache m) a <> Invalid ->
      CacheRep (wb_add wb a v) (state d m (set_vdisk s (upd (vdisk s) a v)) hm).
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

  Theorem CacheWrite_ok : forall tid wb a v,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma /\
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
      (s : Abstraction St) (hm : hashmap),
      CacheRep wb (state d m s hm) ->
      CacheRep empty_writebuffer
               (state d (set_cache m (upd_with_buffer (cache m) wb))
                      (set_vdisk0 s (vdisk s)) hm).
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
                         CacheRep wb sigma;
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
      (s : Abstraction St) (hm : hashmap),
      CacheRep wb (state d m s hm) ->
      CacheRep empty_writebuffer (state d m (set_vdisk s (vdisk_committed s)) hm).
  Proof.
    unfold CacheRep; simpl; intuition; simplify.
  Qed.

  Hint Resolve CacheRep_abort.

  Definition CacheAbort_ok : forall tid,
      cprog_spec G tid
                 (fun wb '(sigma_i, sigma) =>
                    {| precondition :=
                         CacheRep wb sigma;
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

End OptimisticCache.

Arguments St OtherSt : clear implicits.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)