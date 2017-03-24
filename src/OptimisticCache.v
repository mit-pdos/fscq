Require Import CCL.

Require Import Mem AsyncDisk.
Require Import FunctionalExtensionality.
Require Import UpdList.

(* re-export MemCache since Cache appears in external type signatures *)
Require Export MemCache.

Require SepAuto.

Definition Disk := @mem addr addr_eq_dec valu.

Record CacheSt :=
  caches { old_cache: Cache;
           cache: Cache; }.

Section OptimisticCache.

  Implicit Types (c:Cache) (cs:CacheSt).

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

  (* the protocol is completely arbitrary for the cache, since it never deals
  with locking *)
  Variable G:Protocol.

  Definition caches_consistent c0 c :=
    (forall a, match cache_get c a with
         | Present _ _ => True
         | Invalid => cache_get c0 a = Invalid
         | Missing => cache_get c0 a = Missing
          end) /\
    (forall a, match cache_get c0 a with
          | Invalid => cache_get c a = Invalid
          | _ => True
          end).

  Definition CacheRep d cs (vd0 vd:Disk) :=
    cache_rep d (old_cache cs) vd0 /\
    cache_rep d (cache cs) vd /\
    caches_consistent (old_cache cs) (cache cs).

  Lemma CacheRep_fold : forall d c0 c vd0 vd,
      cache_rep d c0 vd0 ->
      cache_rep d c vd ->
      caches_consistent c0 c ->
      CacheRep d (caches c0 c) vd0 vd.
  Proof.
    unfold CacheRep; intuition.
  Qed.

  Lemma CacheRep_fold' : forall d cs vd0 vd,
      cache_rep d (old_cache cs) vd0 ->
      cache_rep d (cache cs) vd ->
      caches_consistent (old_cache cs) (cache cs) ->
      CacheRep d cs vd0 vd.
  Proof.
    unfold CacheRep; intuition.
  Qed.

  Hint Resolve CacheRep_fold CacheRep_fold'.

  Ltac simplify :=
    repeat match goal with
           | [ H: CacheRep _ _ _ _ |- _ ] =>
             unfold CacheRep in H
           | [ |- exists (_: _ * _), _ ] => apply exists_tuple
           | [ H: (_, _) = (_, _) |- _ ] =>
             inversion H; subst; clear H
           | [ H: exists _, _ |- _ ] => deex
           | _ => progress simpl in *
           | _ => progress subst
           | _ => simpl_match
           | _ => break_tuple
           | _ => progress autorewrite with upd cache in *
           | _ => intuition eauto
           end.

  Ltac finisher :=
    descend;
    repeat match goal with
           | [ |- ?F (Sigma.mem _) ] =>
             solve [ SepAuto.pred_apply; SepAuto.cancel ]
           | _ => congruence
           | _ => intuition eauto
           end.

  Ltac finish := simplify; finisher.

  Ltac step := CCLAutomation.step; simplify; finisher.

  Definition ClearPending cs a :=
    v <- WaitForRead a;
      let c0' := add_entry Clean (old_cache cs) a v in
      let c' := add_entry Clean (cache cs) a v in
        Ret (v, caches c0' c').

  Definition StartFill cs a :=
    _ <- BeginRead a;
      let c0' := mark_pending (old_cache cs) a in
      let c' := mark_pending (cache cs) a in
      Ret (caches c0' c').

  Definition CacheRead cs a l :=
    match cache_get (cache cs) a with
    | Present v _ => Ret (Some v, cs)
    | Missing => if CanWrite l then
                  cs <- StartFill cs a;
                    Ret (None, cs)
                else Ret (None, cs)
    | Invalid => if CanWrite l then
                  do '(v,cs) <- ClearPending cs a;
                    Ret (Some v, cs)
                else Ret (None, cs)
    end.

  Ltac addrs_cases :=
        match goal with
        | [ a: addr, a': addr |- _ ] =>
          destruct (addr_eq_dec a a'); subst;
          autorewrite with cache upd in *;
          try congruence
        end.

  Ltac specific_addr :=
    match goal with
    | [ a: addr, H: forall (_:addr), _ |- _ ] =>
      lazymatch goal with
      | [ a: addr, a': addr |- _ ] => fail
      | _ => specialize (H a)
      end
    end.

  Ltac solve_cache :=
    intuition;
    repeat match goal with
        | [ H: cache_rep _ _ _ |- cache_rep _ _ _ ] =>
          unfold cache_rep in *;
          let a' := fresh "a'" in
          intro a';
          specialize (H a');
          addrs_cases
        | [ a: addr, H: cache_rep _ _ _ |- _ ] =>
          specialize (H a)
        end;
    repeat simpl_match;
    repeat deex;
    intuition eauto; try congruence.

  Hint Extern 3 (_ = _) => congruence.

  Lemma cache_rep_invalid:
    forall (c : Cache) (a : addr) d (vd : Disk) (v0 : valu),
      cache_rep d c vd ->
      cache_get c a = Invalid ->
      vd a = Some v0 -> d a = Some (v0, Pending).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve cache_rep_invalid.

  Lemma cache_rep_finish_read:
    forall (c : Cache) (a : addr) d d' (vd : Disk) (v0 : valu),
      cache_rep d c vd ->
      vd a = Some v0 ->
      cache_get c a = Invalid ->
      d' = upd d a (v0, NoReader) ->
      cache_rep d' (add_entry Clean c a v0) vd.
  Proof.
    solve_cache.
  Qed.

  Hint Resolve cache_rep_finish_read.

  Lemma caches_consistent_c0_invalid : forall c0 c a,
      caches_consistent c0 c ->
      cache_get c a = Invalid ->
      cache_get c0 a = Invalid.
  Proof.
    unfold caches_consistent; intuition.
    specialize (H1 a); simpl_match; auto.
  Qed.

  Hint Resolve caches_consistent_c0_invalid.

  Lemma cache_rep_invalid_same_val:
    forall (a : addr) (vd0 vd : Disk) (v0 : valu) (st0 : Sigma)
      (d : DISK) (c0 c : Cache),
      cache_get c a = Invalid ->
      caches_consistent c0 c ->
      cache_rep d c0 vd0 ->
      cache_rep d c vd ->
      vd a = Some v0 ->
      Sigma.disk st0 = upd d a (v0, NoReader) ->
      vd0 a = Some v0.
  Proof.
    unfold caches_consistent; solve_cache.
    repeat (specific_addr || simpl_match || deex).
    congruence.
  Qed.

  Hint Resolve cache_rep_invalid_same_val.

  Lemma caches_consistent_clean_entries:
    forall (a : addr) (v0 : valu) (c0 c : Cache),
      caches_consistent c0 c ->
      caches_consistent (add_entry Clean c0 a v0) (add_entry Clean c a v0).
  Proof.
    unfold caches_consistent; intuition;
      addrs_cases; eauto.
    specialize (H0 a0).
    destruct_all_matches.
    specialize (H1 a0).
    destruct_all_matches.
  Qed.

  Hint Resolve caches_consistent_clean_entries.

  Ltac simplify ::=
    repeat match goal with
           | [ H: CacheRep _ _ _ _ |- _ ] =>
             unfold CacheRep in H
           | [ |- exists (_: _ * _), _ ] => apply exists_tuple
           | [ H: (_, _) = (_, _) |- _ ] =>
             inversion H; subst; clear H
           | [ H: exists _, _ |- _ ] => deex
           | _ => progress simpl in *
           | _ => progress subst
           | _ => simpl_match
           | _ => progress autorewrite with upd cache in *
           | _ => intuition eauto
           end.

  Theorem ClearPending_ok : forall tid cs a,
      cprog_spec G tid
                 (fun '(F, vd0, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep (Sigma.disk sigma) cs vd0 vd /\
                         cache_get (cache cs) a = Invalid /\
                         vd a = Some v0 /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' '(r, cs') =>
                           F (Sigma.mem sigma') /\
                           CacheRep (Sigma.disk sigma') cs' vd0 vd /\
                           cache_get (cache cs') a = Present v0 Clean /\
                           r = v0 /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (ClearPending cs a).
  Proof.
    unfold ClearPending.
    hoare finish.
    intuition finish.
    eauto 10.
  Qed.

  Hint Extern 0 {{ ClearPending _ _; _ }} => apply ClearPending_ok : prog.

  Lemma cache_rep_missing_val:
    forall (c : Cache) (a : addr),
      cache_get c a = Missing ->
      forall (vd : Disk) (v0 : valu),
        vd a = Some v0 ->
        forall d : DISK, cache_rep d c vd -> d a = Some (v0, NoReader).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve cache_rep_missing_val.

  Lemma cache_rep_start_fill:
    forall (c : Cache) (a : addr),
      cache_get c a = Missing ->
      forall (vd : Disk) (v0 : valu),
        vd a = Some v0 ->
        forall d : DISK,
          cache_rep d c vd ->
          forall d' : DISK, d' = upd d a (v0, Pending) ->
                       cache_rep d' (mark_pending c a) vd.
  Proof.
    solve_cache.
  Qed.

  Hint Resolve cache_rep_start_fill.

  Lemma caches_consistent_c0_missing : forall c0 c a,
      caches_consistent c0 c ->
      cache_get c a = Missing ->
      cache_get c0 a = Missing.
  Proof.
    unfold caches_consistent; intuition.
    specialize (H1 a); simpl_match; auto.
  Qed.

  Hint Resolve caches_consistent_c0_missing.

  Lemma cache_rep_missing_same_val:
    forall (a : addr) (vd0 vd : Disk) (v0 : valu) (st0 : Sigma)
      (d : DISK) (c0 c : Cache),
      cache_get c a = Missing ->
      caches_consistent c0 c ->
      cache_rep d c0 vd0 ->
      cache_rep d c vd ->
      vd a = Some v0 ->
      Sigma.disk st0 = upd d a (v0, Pending) ->
      vd0 a = Some v0.
  Proof.
    unfold caches_consistent; solve_cache.
    repeat (specific_addr || simpl_match || deex).
    destruct (vd0 a); eauto.
  Qed.

  Hint Resolve cache_rep_missing_same_val.

  Lemma cache_consistent_mark_pending:
    forall (a : addr) (c0 c : Cache),
      caches_consistent c0 c ->
      caches_consistent (mark_pending c0 a) (mark_pending c a).
  Proof.
    unfold caches_consistent; intuition;
      addrs_cases; eauto.
    specialize (H0 a0).
    destruct_all_matches.
    specialize (H1 a0).
    destruct_all_matches.
  Qed.

  Hint Resolve cache_consistent_mark_pending.

  Theorem StartFill_ok : forall tid cs a,
      cprog_spec G tid
                 (fun '(F, vd0, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep (Sigma.disk sigma) cs vd0 vd /\
                         cache_get (cache cs) a = Missing /\
                         vd a = Some v0 /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' cs' =>
                           F (Sigma.mem sigma') /\
                           CacheRep (Sigma.disk sigma') cs' vd0 vd /\
                           cache_get (cache cs') a = Invalid /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (StartFill cs a).
  Proof.
    unfold StartFill.
    hoare finish.
    intuition finish.
    eauto 10.
  Qed.

  Hint Extern 1 {{ StartFill _ _; _ }} => apply StartFill_ok : prog.

  Lemma cache_rep_present_val:
    forall (c : Cache) (a : addr) (v : valu) (b : DirtyBit),
      cache_get c a = Present v b ->
      forall (d : DISK) (vd : Disk) (v0 : valu),
        cache_rep d c vd -> vd a = Some v0 -> v = v0.
  Proof.
    solve_cache.
  Qed.

  Hint Resolve cache_rep_present_val.

  Definition CacheRead_ok : forall tid cs a l,
      cprog_spec G tid
                 (fun '(F, d, vd0, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep d cs vd0 vd /\
                         (l = WriteLock -> d = Sigma.disk sigma) /\
                         Sigma.l sigma = l /\
                         vd a = Some v0;
                       postcondition :=
                         fun sigma' '(r, cs') =>
                           F (Sigma.mem sigma') /\
                           let d' := if CanWrite l then Sigma.disk sigma' else d in
                           CacheRep d' cs' vd0 vd /\
                           (l = Free -> cs' = cs) /\
                           (l = Free -> Sigma.disk sigma' = Sigma.disk sigma) /\
                           match r with
                           | Some v => v = v0
                           | None => True
                           end /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (CacheRead cs a l).
  Proof.
    unfold CacheRead.
    intros.
    destruct (cache_get (cache cs) a) eqn:?, (CanWrite l) eqn:?;
             hoare finish.
  Qed.

  Definition CacheWrite cs a v :=
    cs <- match cache_get (cache cs) a with
        | Invalid => do '(_, cs) <- ClearPending cs a;
                      Ret cs
        | _ => Ret cs
        end;
      let c' := add_entry Dirty (cache cs) a v in
      Ret (tt, caches (old_cache cs) c').

  Lemma cache_rep_dirty_write:
    forall (c : Cache) (a : addr) (v : valu),
      cache_get c a <> Invalid ->
      forall (vd : Disk) (v1 : valu) d,
        cache_rep d c vd ->
        vd a = Some v1 ->
        cache_rep d (add_entry Dirty c a v) (upd vd a v).
  Proof.
    solve_cache.
    destruct (cache_get c a') eqn:Hcache;
      intuition eauto.
    destruct b; eauto.
  Qed.

  Hint Resolve cache_rep_dirty_write.
  Hint Extern 2 (cache_get _ _ <> _) => congruence.

  Lemma cache_consistent_add_dirty:
    forall (a : addr) (v : valu) (c0 c : Cache),
      cache_get c a <> Invalid ->
      caches_consistent c0 c ->
      caches_consistent c0 (add_entry Dirty c a v).
  Proof.
    unfold caches_consistent; intuition;
      addrs_cases; eauto.
    specialize (H1 a0).
    destruct_all_matches; eauto.
    specialize (H2 a0).
    destruct_all_matches; try congruence; eauto.
    specialize (H2 a0).
    destruct_all_matches; try congruence; eauto.
  Qed.

  Hint Resolve cache_consistent_add_dirty.

  Theorem CacheWrite_ok : forall tid cs a v,
      cprog_spec G tid
                 (fun '(F, vd0, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep (Sigma.disk sigma) cs vd0 vd /\
                         vd a = Some v0 /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' '(_, cs') =>
                           F (Sigma.mem sigma') /\
                           CacheRep (Sigma.disk sigma') cs' vd0 (upd vd a v) /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (CacheWrite cs a v).
  Proof.
    unfold CacheWrite.
    intros.
    destruct (cache_get (cache cs) a) eqn:?; hoare finish.
  Qed.

  Definition CacheCommit cs :=
    Ret (cache cs).

  Theorem CacheCommit_ok : forall tid cs,
      cprog_spec G tid
                 (fun '(F, d, vd0, vd) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep d cs vd0 vd;
                       postcondition :=
                         fun sigma' c =>
                           F (Sigma.mem sigma') /\
                           cache_rep d c vd /\
                           c = cache cs /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (CacheCommit cs).
  Proof.
    unfold CacheCommit.
    hoare finish.
  Qed.

  Definition CacheAbort cs :=
    Ret (old_cache cs).

  Theorem CacheAbort_ok : forall tid cs,
      cprog_spec G tid
                 (fun '(F, d, vd0, vd) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep d cs vd0 vd;
                       postcondition :=
                         fun sigma' c =>
                           F (Sigma.mem sigma') /\
                           cache_rep d c vd0 /\
                           c = old_cache cs /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (CacheAbort cs).
  Proof.
    unfold CacheAbort.
    hoare finish.
  Qed.

  Definition CacheInit c :=
    Ret (caches c c).

  Lemma caches_consistent_refl : forall c,
      caches_consistent c c.
  Proof.
    unfold caches_consistent; intuition;
      destruct_all_matches.
  Qed.

  Hint Resolve caches_consistent_refl.

  Theorem CacheInit_ok : forall tid c,
      cprog_spec G tid
                 (fun '(F, d, vd) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         cache_rep d c vd;
                       postcondition :=
                         fun sigma' cs =>
                           F (Sigma.mem sigma') /\
                           CacheRep d cs vd vd /\
                           cache cs = c /\
                           old_cache cs = c /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (CacheInit c).
  Proof.
    unfold CacheInit.
    hoare finish.
  Qed.

End OptimisticCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)