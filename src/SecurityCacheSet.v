Require Export SecuritySet.
Require Export Cache.
Require Export MapUtils.
Require Export ListPred.
Require Export MemPred.

Set Implicit Arguments.

Import AddrMap.
Import Map.
Import BUFCACHE.


Notation "{}" := (Empty_set _).
Notation "{ x }" := (Singleton _ x).
Notation "{ a , .. , b }" := (Union {a} .. (Union {b} {}) .. ) .
Infix "|_|" := (Union _) (at level 35).
Infix "(=" := (Included _)(at level 35).

(* Theorem writeback_ok : forall a cs,
    {< d vs (F : rawpred),
    PRE:hm
      rep cs d * [[ (F * a |+> vs)%pred d ]]
    POST:hm' RET:cs'
      rep cs' d * [[ addr_clean (CSMap cs') a ]] * 
      [[ Map.In a (CSMap cs) -> Map.In a (CSMap cs') ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} writeback a cs. *)

Lemma empty_union:
  forall A (s: Ensemble A),
  s = s |_| {}.
Proof.
  intros.
  apply Extensionality_Ensembles; intros.
  unfold Same_set, Included; intuition.
  unfold Ensembles.In in *.
  inversion H; subst; auto.
  unfold Ensembles.In in *.
  inversion H0.
Qed.

Lemma empty_incl_all:
  forall A (s: Ensemble A),
  {} (= s.
Proof.
  intros.
  unfold Included; intuition.
  unfold Ensembles.In in *.
  inversion H.
Qed.
Hint Resolve empty_incl_all.

Lemma union_empty:
  forall A (s: Ensemble A),
  s = {} |_| s.
Proof.
  intros.
  apply Extensionality_Ensembles; intros.
  unfold Same_set, Included; intuition.
  unfold Ensembles.In in *.
  inversion H; subst; auto.
  unfold Ensembles.In in *.
  inversion H0.
Qed.


Lemma union_id:
  forall A (s: Ensemble A),
  s = s |_| s.
Proof.
  intros.
  apply Extensionality_Ensembles; intros.
  unfold Same_set, Included; intuition.
  unfold Ensembles.In in *.
  inversion H; subst; auto.
Qed.



Lemma ret_secure_all:
  forall T A (s: Ensemble A) (r: T),
  prog_secure_set (Ret r) s.
Proof.
  intros.
  eapply InclSec; eauto.
Qed.
Hint Resolve ret_secure_all.

Lemma alertmodified_secure_all:
  forall A (s: Ensemble A),
  prog_secure_set AlertModified s.
Proof.
  intros.
  eapply InclSec; eauto.
Qed.
Hint Resolve alertmodified_secure_all.


Theorem writeback_secure:
  forall a cs,
  prog_secure_set (writeback a cs) (Singleton _ a).
Proof.
  unfold writeback; intuition.
  destruct (Map.find a (CSMap cs)) eqn:D; eauto.
  destruct p; eauto.
  destruct b; eauto.
  rewrite empty_union.
  eapply BindSec; eauto.
Qed.
Hint Resolve writeback_secure.


Theorem evict_secure:
  forall a cs,
  prog_secure_set (evict a cs) (Singleton _ a).
Proof.
  unfold evict; intuition.
  rewrite empty_union.
  eapply BindSec; eauto; intros.
  destruct (Map.find a (CSMap x)) eqn:D; eauto.
Qed.
Hint Resolve evict_secure.


Theorem maybe_evict_secure:
  forall cs,
  prog_secure_set (maybe_evict cs) (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (a, _) :: _ => Singleton _ a
                                                                             end
                                                           end).
Proof.
  unfold maybe_evict; intuition.
  destruct (lt_dec (CSCount cs) (CSMaxCount cs)); simpl; eauto.
  destruct (Map.find 0 (CSMap cs)); simpl; eauto.
  rewrite empty_union.
  eapply BindSec; eauto; intros.
  destruct (Map.elements (CSMap cs)) eqn:D; eauto.
  destruct p.
  rewrite empty_union.
  eapply BindSec; eauto; intros.
Qed.
Hint Resolve maybe_evict_secure.


Transparent read.
Theorem read_secure:
  forall a cs,
  prog_secure_set (read a cs) (Union _ (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end) (Singleton _ a)).
Proof.
  unfold read; intuition.
  eapply BindSec; eauto; intros.
  destruct (Map.find a (CSMap x)); simpl; eauto.
  destruct p; eauto.
  rewrite union_empty.
  eapply BindSec; eauto; intros.
  rewrite empty_union.
  eapply BindSec; eauto; intros.
Qed.
Hint Resolve read_secure.


Transparent write.
Theorem write_secure:
  forall a v cs,
  prog_secure_set (write a v cs) (match find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end).
Proof.
  unfold write; intuition.
  rewrite empty_union.
  eapply BindSec; eauto; intros.
  destruct (Map.find a (CSMap x)); simpl; eauto.
Qed.
Hint Resolve write_secure.

Transparent begin_sync.
Theorem begin_sync_secure:
  forall A cs,
  prog_secure_set (begin_sync cs) (Empty_set A).
Proof.
  unfold begin_sync; intros; auto.
Qed.
Hint Resolve begin_sync_secure.


Transparent sync.
Theorem sync_secure:
  forall a cs,
  prog_secure_set (sync a cs) (Singleton _ a).
Proof.
  unfold sync; intros.
  rewrite empty_union; eauto.
Qed.
Hint Resolve sync_secure.


Transparent end_sync.
Theorem end_sync_secure:
  forall A cs,
  prog_secure_set (end_sync cs) (Empty_set A).
Proof.
  unfold end_sync; intros.
  rewrite empty_union; eauto.
Qed.
Hint Resolve end_sync_secure.


Transparent init.
Theorem init_secure:
  forall A n,
  prog_secure_set (init n) (Empty_set A).
Proof.
  unfold init; intros.
  rewrite empty_union; eauto.
Qed.
Hint Resolve init_secure.


Transparent read_array.
Theorem read_array_secure:
  forall a i cs,
  prog_secure_set (read_array a i cs) (Union _ (match Map.find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match Map.elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end) (Singleton _ (a+i))).
Proof.
  unfold read_array; intuition.
  rewrite empty_union; eauto.
Qed.
Hint Resolve read_array_secure.


Transparent write_array.
Theorem write_array_secure:
  forall a i v cs,
  prog_secure_set (write_array a i v cs) (match Map.find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match Map.elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end).
Proof.
  unfold write_array; intuition.
  rewrite empty_union; eauto.
Qed.
Hint Resolve write_array_secure.


Transparent sync_array.
Theorem sync_array_secure:
  forall a i cs,
  prog_secure_set (sync_array a i cs) (Singleton _ (a + i)).
Proof.
  unfold sync_array; intros.
  rewrite empty_union; eauto.
Qed.
Hint Resolve sync_array_secure.

Fixpoint slice a n:=
match n with
| O => (Singleton _ a)
| S n' => (Singleton _ a) |_| slice (S a) n'
end.


Transparent read_range.
Theorem read_range_secure:
  forall nr A a (vfold: A -> valu -> A) a0 cs,
  prog_secure_set (read_range a nr vfold a0 cs) (Union _ (match Map.find (fst (eviction_choose (CSEvict cs))) (CSMap cs) with
                                                           | Some _ => Singleton _ (fst (eviction_choose (CSEvict cs)))
                                                           | None =>  match Map.elements (CSMap cs) with
                                                                             | nil => Empty_set _
                                                                             | (x, _) :: _ => Singleton _ x
                                                                             end
                                                           end) (slice a nr)).
Proof.
  unfold read_range, pair_args_helper;  induction nr; intuition.
  - rewrite empty_union; eauto.
    eapply BindSec; simpl; eauto.
  - simpl; eauto.
    rewrite empty_union.
    eapply BindSec; eauto.
    replace  (match find O (CSMap cs) with
     | Some _ => Singleton nat O
     | None =>
         match elements (CSMap cs) with
         | nil => Empty_set nat
         | cons (pair x _) _ => Singleton key x
         end
     end |_| ((Singleton _ a) |_| slice (S a) nr))
   with
    ((match find O (CSMap cs) with
     | Some _ => Singleton nat O
     | None =>
         match elements (CSMap cs) with
         | nil => Empty_set nat
         | cons (pair x _) _ => Singleton key x
         end
     end |_| (Singleton _ a)) |_|  (match find O (CSMap cs) with
     | Some _ => Singleton nat O
     | None =>
         match elements (CSMap cs) with
         | nil => Empty_set nat
         | cons (pair x _) _ => Singleton key x
         end
     end |_| slice (S a) nr)).
    eapply BindSec; intros.
    rewrite plus_n_O with (n:= a) at 2.
    rewrite empty_union; eauto.
    
    
  unfold ForN_; simpl.
Qed.
Hint Resolve read_array_secure.

  Definition read_range A a nr (vfold : A -> valu -> A) a0 cs :=
    let^ (cs, r) <- ForN i < nr
    Ghost [ F crash d vs ]
    Loopvar [ cs pf ]
    Invariant
      rep cs d * [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) a0 ]]
    OnCrash  crash
    Begin
      let^ (cs, v) <- read_array a i cs;
      Ret ^(cs, vfold pf v)
    Rof ^(cs, a0);
    Ret ^(cs, r).


  Definition write_range a l cs :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd_range vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- write_array a i (selN l i $0) cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition sync_range a nr cs :=
    let^ (cs) <- ForN i < nr
    Ghost [ F crash vs d0 ]
    Loopvar [ cs ]
    Invariant
      exists d', synrep cs d0 d' *
      [[ (F * arrayN ptsto_subset a (vssync_range vs i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition write_vecs a l cs :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      let v := selN l i (0, $0) in
      cs <- write_array a (fst v) (snd v) cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition sync_vecs a l cs :=
    let^ (cs) <- ForEach i irest l
    Ghost [ F crash vs d0 ]
    Loopvar [ cs ]
    Invariant
      exists d' iprefix, synrep cs d0 d' *
      [[ iprefix ++ irest = l ]] *
      [[ (F * arrayN ptsto_subset a (vssync_vecs vs iprefix))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.

  Definition sync_vecs_now a l cs :=
    cs <- begin_sync cs;
    cs <- sync_vecs a l cs;
    cs <- end_sync cs;
    Ret cs.

  Definition sync_all cs :=
    cs <- sync_vecs_now 0 (map fst (Map.elements (CSMap cs))) cs;
    Ret cs.







