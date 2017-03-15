Require Import CCL.

Require Import Mem AsyncDisk.
Require Import FunctionalExtensionality.
Require Import UpdList.

(* re-export MemCache since Cache appears in external type signatures *)
Require Export MemCache.

Require SepAuto.

Definition Disk := @mem addr addr_eq_dec valu.

Section OptimisticCache.

  Implicit Types (c:Cache).

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

  Definition CacheRep d c (vd:Disk) :=
    cache_rep d c vd.

  Ltac simplify :=
    repeat match goal with
           | [ H: context[let (n, m) := ?a in _] |- _ ] =>
             let n := fresh n in
             let m := fresh m in
             destruct a as [m n]
           | [ |- exists (_: _ * _), _ ] => apply exists_tuple
           | [ H: (_, _) = (_, _) |- _ ] =>
             inversion H; subst; clear H
           | [ H: exists _, _ |- _ ] => deex
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress simpl_match
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

  Definition ClearPending c a :=
    v <- WaitForRead a;
      let c' := add_entry Clean c a v in
        Ret (v, c').

  Definition CacheRead c a l :=
    match cache_get c a with
    | Present v _ => Ret (Some v, c)
    | Missing => if CanWrite l then
                  _ <- BeginRead a;
                  let c' := mark_pending c a in
                  Ret (None, c')
                else Ret (None, c)
    | Invalid => if CanWrite l then
                  do '(v,c) <- ClearPending c a;
                    Ret (Some v, c)
                else Ret (None, c)
    end.

  Ltac solve_cache :=
    unfold CacheRep; intuition;
    repeat match goal with
           | [ a: addr, H: cache_rep _ _ _ |- _ ] =>
             specialize (H a)
           end;
    repeat simpl_match;
    repeat deex;
    intuition eauto; try congruence.

  Hint Extern 3 (_ = _) => congruence.

  Lemma CacheRep_invalid:
    forall (c : Cache) (a : addr) d (vd : Disk) (v0 : valu),
      CacheRep d c vd ->
      cache_get c a = Invalid ->
      vd a = Some v0 -> d a = Some (v0, Pending).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve CacheRep_invalid.

  Lemma CacheRep_finish_read:
    forall (c : Cache) (a : addr) d d' (vd : Disk) (v0 : valu),
      CacheRep d c vd ->
      vd a = Some v0 ->
      cache_get c a = Invalid ->
      d' = upd d a (v0, NoReader) ->
      CacheRep d' (add_entry Clean c a v0) vd.
  Proof.
    unfold CacheRep, cache_rep; intros.
    specialize (H a0).
    destruct (addr_eq_dec a a0); subst;
      autorewrite with cache upd;
      solve_cache.
  Qed.

  Hint Resolve CacheRep_finish_read.

  Theorem ClearPending_ok : forall tid c a,
      cprog_spec G tid
                 (fun '(F, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep (Sigma.disk sigma) c vd /\
                         cache_get c a = Invalid /\
                         vd a = Some v0 /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' '(r, c') =>
                           F (Sigma.mem sigma') /\
                           CacheRep (Sigma.disk sigma') c' vd /\
                           cache_get c' a = Present v0 Clean /\
                           r = v0 /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (ClearPending c a).
  Proof.
    unfold ClearPending.
    hoare finish.
  Qed.

  Hint Extern 0 {{ ClearPending _ _; _ }} => apply ClearPending_ok : prog.

  Lemma CacheRep_present_val:
    forall (c : Cache) (a : addr) (v : valu) (b : DirtyBit),
      cache_get c a = Present v b ->
      forall (d : DISK) (vd : Disk) (v0 : valu),
        CacheRep d c vd -> vd a = Some v0 -> v = v0.
  Proof.
    solve_cache.
  Qed.

  Lemma CacheRep_missing_val:
    forall (c : Cache) (a : addr),
      cache_get c a = Missing ->
      forall (vd : Disk) (v0 : valu),
        vd a = Some v0 ->
        forall d : DISK, CacheRep d c vd -> d a = Some (v0, NoReader).
  Proof.
    solve_cache.
  Qed.

  Hint Resolve CacheRep_present_val CacheRep_missing_val.

  Lemma CacheRep_start_fill:
    forall (c : Cache) (a : addr),
      cache_get c a = Missing ->
      forall (vd : Disk) (v0 : valu),
        vd a = Some v0 ->
        forall d : DISK,
          CacheRep d c vd ->
          forall d' : DISK, d' = upd d a (v0, Pending) ->
                       CacheRep d' (mark_pending c a) vd.
  Proof.
    unfold CacheRep, cache_rep; intros; subst.
    specialize (H1 a0).
    destruct (addr_eq_dec a a0); subst;
      autorewrite with cache upd;
      solve_cache.
  Qed.

  Hint Resolve CacheRep_start_fill.

  Definition CacheRead_ok : forall tid c a l,
      cprog_spec G tid
                 (fun '(F, d, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep d c vd /\
                         (l = WriteLock -> d = Sigma.disk sigma) /\
                         Sigma.l sigma = l /\
                         vd a = Some v0;
                       postcondition :=
                         fun sigma' '(r, c') =>
                           F (Sigma.mem sigma') /\
                           let d' := if CanWrite l then Sigma.disk sigma' else d in
                           CacheRep d' c' vd /\
                           (l = Free -> c' = c) /\
                           (l = Free -> Sigma.disk sigma' = Sigma.disk sigma) /\
                           match r with
                           | Some v => v = v0
                           | None => True
                           end /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma |})
                 (CacheRead c a l).
  Proof.
    unfold CacheRead.
    intros.
    destruct (cache_get c a) eqn:?, (CanWrite l) eqn:?;
             hoare finish.
  Qed.

  Definition CacheWrite c a v :=
    c <- match cache_get c a with
        | Invalid => do '(_, c) <- ClearPending c a;
                      Ret c
        | _ => Ret c
        end;
      let c' := add_entry Dirty c a v in
      Ret (tt, c').

  Lemma CacheRep_dirty_write:
    forall (c : Cache) (a : addr) (v : valu),
      cache_get c a <> Invalid ->
      forall (vd : Disk) (v1 : valu) d,
        CacheRep d c vd ->
        vd a = Some v1 ->
        CacheRep d (add_entry Dirty c a v) (upd vd a v).
  Proof.
    unfold CacheRep, cache_rep; intros.
    specialize (H0 a0).
    destruct (addr_eq_dec a a0); subst;
      autorewrite with cache upd;
      solve_cache.
    destruct (cache_get c a0) eqn:Hcache;
      intuition eauto.
    destruct b; eauto.
  Qed.

  Hint Resolve CacheRep_dirty_write.
  Hint Extern 2 (cache_get _ _ <> _) => congruence.

  Theorem CacheWrite_ok : forall tid c a v,
      cprog_spec G tid
                 (fun '(F, vd, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep (Sigma.disk sigma) c vd /\
                         vd a = Some v0 /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' '(_, c') =>
                           F (Sigma.mem sigma') /\
                           CacheRep (Sigma.disk sigma') c' (upd vd a v) /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (CacheWrite c a v).
  Proof.
    unfold CacheWrite.
    intros.
    destruct (cache_get c a) eqn:?; hoare finish; simplify.
  Qed.

End OptimisticCache.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)