Require Export SecurityCacheSet.
Require Export DiskLogHash.

Import PaddedLog.
Import Hdr.
Import AddrMap.
Import Map.

Theorem read_secure:
  forall xp cs,
  prog_secure_set (read xp cs) (Union _ (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end) (Singleton _ (LAHdr xp))).
Proof.
  unfold read, pair_args_helper; intros.
  rewrite empty_union; eauto.
Qed.

Theorem write_secure:
  forall xp n cs,
  prog_secure_set (write xp n cs) (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end).
Proof.
  unfold write, pair_args_helper; intros.
  rewrite empty_union; eauto.
Qed.

Theorem sync_secure:
  forall xp cs,
  prog_secure_set (sync xp cs) (Singleton _ (LAHdr xp)).
Proof.
  unfold sync, pair_args_helper; intros.
  rewrite empty_union; eauto.
Qed.

Theorem sync_now_secure:
  forall xp cs,
  prog_secure_set (sync_now xp cs) (Singleton _ (LAHdr xp)).
Proof.
  unfold sync_now, pair_args_helper; intros.
  rewrite union_empty; eauto.
  eapply BindSec; intros; eauto.
  rewrite empty_union; eauto.
  eapply BindSec; intros; eauto.
  rewrite union_id; eauto.
Qed.

Theorem init_secure:
  forall xp cs,
  prog_secure_set (init xp cs) (Union _ (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end) (Singleton _ (LAHdr xp))).
Proof.
  unfold init, pair_args_helper; intros.
  rewrite union_empty; eauto.
  eapply BindSec; intros; eauto.
  eapply BindSec; intros; eauto.
  rewrite union_empty; eauto.
  eapply BindSec; intros; eauto.
  rewrite empty_union; eauto.
  eapply BindSec; intros; eauto.
  rewrite union_id; eauto.
Qed.


