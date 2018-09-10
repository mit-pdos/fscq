Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Mem Pred.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import WordAuto.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.

Require Export AsyncRecArray.

Import ListNotations.

Definition header_type := Rec.RecF ([("ndesc", Rec.WordF addrlen);
                                         ("ndata", Rec.WordF addrlen)]).
    Definition header := Rec.data header_type.
    Definition hdr := (nat * nat)%type.
    Definition mk_header (len : hdr) : header := ($ (fst len), ($ (snd len), tt)).

Theorem hdrsz_ok : Rec.len header_type <= valulen.
Proof.
  rewrite valulen_is. apply leb_complete. compute. trivial.
Qed.
Local Hint Resolve hdrsz_ok.

Lemma plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
Proof.
  apply le_plus_minus_r; auto.
Qed.

Definition hdr2val (h : header) : valu.
  set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
  rewrite plus_minus_header in r.
  refine r.
Defined.

Definition val2hdr (v : valu) : header.
  apply Rec.of_word.
  rewrite <- plus_minus_header in v.
  refine (split1 _ _ v).
Defined.

Arguments hdr2val: simpl never.

Lemma val2hdr2val : forall h,
                      val2hdr (hdr2val h) = h.
Proof.
  unfold val2hdr, hdr2val.
  unfold eq_rec_r, eq_rec.
  intros.
  rewrite <- plus_minus_header.
  unfold zext.
  autorewrite with core; auto.
  simpl; destruct h; simpl.
  apply Rec.of_to_id.
  simpl; tauto.
Qed.

Arguments val2hdr: simpl never.
Opaque val2hdr.  (* for some reason "simpl never" doesn't work *)


Definition xparams := log_xparams.
Definition LAHdr := LogHeader.

Inductive state : Type :=
| Synced : hdr -> state
| Unsync : hdr -> hdr -> state
.

Definition hdr_goodSize (n:hdr):=
  goodSize addrlen (fst n) /\ goodSize addrlen (snd n).

Definition state_goodSize st :=
  match st with
  | Synced n => hdr_goodSize n
  | Unsync n o => hdr_goodSize n /\ hdr_goodSize o
  end.

Definition rep xp state : @rawpred tagged_block:=
  ([[ state_goodSize state ]] *
   match state with
   | Synced n =>
     (LAHdr xp) |+> ((dummy_handle, hdr2val (mk_header n)), nil)
   | Unsync n o =>
     (LAHdr xp) |+> ((dummy_handle, hdr2val (mk_header n)), [(dummy_handle, hdr2val (mk_header o))]%list)
   end)%pred.


Definition read xp cs := Eval compute_rec in
      let^ (cs, h) <- read (LAHdr xp) cs;;   
      v <- Unseal h;;
      let header := (val2hdr v) in
      Ret ^(cs, (# ((val2hdr v) :-> "ndesc"), # ((val2hdr v) :-> "ndata"))).

Definition write xp n cs :=
    h <- Seal dummy_handle (hdr2val (mk_header n));;
    cs <- write (LAHdr xp) h cs;;
    Ret cs.

Definition sync xp cs :=
  cs <- sync (LAHdr xp) cs;;
     Ret cs.

Definition sync_now xp cs :=
  cs <- begin_sync cs;;
     cs <- CacheDef.sync (LAHdr xp) cs;;
     cs <- end_sync cs;;
     Ret cs.

Definition init xp cs :=
    hdr <- Seal dummy_handle (hdr2val (mk_header((0, 0))));;
    cs <- CacheDef.write (LAHdr xp) hdr cs;;
    cs <- begin_sync cs;;
    cs <- CacheDef.sync (LAHdr xp) cs;;
    cs <- end_sync cs;;
    Ret cs.

Local Hint Unfold rep state_goodSize : hoare_unfold.

Definition xform_rep_synced :
  forall xp n,
    crash_xform (rep xp (Synced n)) =p=> rep xp (Synced n).
Proof.
  unfold rep; intros; simpl.
  xform; auto.
  rewrite crash_xform_ptsto_subset'.
  cancel.
  rewrite H1; auto.
Qed.

Definition xform_rep_unsync :
  forall xp n o,
    crash_xform (rep xp (Unsync n o)) =p=> rep xp (Synced n) \/ rep xp (Synced o).
Proof.
  unfold rep; intros; simpl.
  xform.
  rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
  cancel.
  or_l; cancel.
  cancel.
Qed.


Theorem write_ok :
  forall xp n cs pr,
      {< F d old,
      PERM:pr   
      PRE:bm, hm,
         CacheDef.rep cs d bm *
         [[ hdr_goodSize n ]] *
         [[ (F * rep xp (Synced old))%pred d ]]
    POST:bm', hm', RET: cs
         exists d', CacheDef.rep cs d' bm' *
         [[ exists h, bm' = upd bm h (dummy_handle, (hdr2val (mk_header n))) ]] *                       
         [[ (F * rep xp (Unsync n old))%pred d' ]]
    XCRASH:bm'', hm'',
         exists cs' d', CacheDef.rep cs' d' bm'' * 
         [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} write xp n cs.
Proof.
  unfold write.
  step.
  safestep.
  rewrite rep_none_upd_pimpl; eauto.
  apply upd_eq; auto.
  eauto.
  eauto.
  step.
  step.

  erewrite <- H1; cancel; eauto.
  xcrash.

  Unshelve.
  all: unfold EqDec; apply handle_eq_dec.
Qed.

Theorem read_ok :
 forall xp cs pr,
 {< F d n,
 PERM:pr
 PRE:bm, hm,
     CacheDef.rep cs d bm *
     [[ (F * rep xp (Synced n))%pred d ]]
 POST:bm', hm', RET: ^(cs, r)
     CacheDef.rep cs d bm' *
     [[ (F * rep xp (Synced n))%pred d ]] *
     [[ r = n ]]
 CRASH:bm'', hm'',
     exists cs', CacheDef.rep cs' d bm''
 >} read xp cs.
Proof.
  unfold read.
  hoare.
  
  simpl.
  subst; rewrite val2hdr2val; simpl.
  unfold hdr_goodSize in *; intuition.
  repeat rewrite wordToNat_natToWord_idempotent'; auto.
  destruct n; auto.
  eexists; repeat(eapply hashmap_subset_trans; eauto).
Qed.

Theorem sync_ok :
  forall xp cs pr,
    {< F d0 d n old,
     PERM:pr
     PRE:bm, hm,
       CacheDef.synrep cs d0 d bm *
       [[ (F * rep xp (Unsync n old))%pred d ]] *
       [[ sync_invariant F ]]
     POST:bm', hm', RET: cs
       exists d', CacheDef.synrep cs d0 d' bm' *
       [[ (F * rep xp (Synced n))%pred d' ]]
    CRASH:bm'', hm'',  exists cs', CacheDef.rep cs' d0 bm''
    >} sync xp cs.
Proof.
  unfold sync.
  safestep.
  eassign F_; cancel.
  all: eauto.
  step.
  step.
  eexists; eapply hashmap_subset_trans; eauto.
Qed.

Theorem sync_now_ok :
  forall xp cs pr,
  {< F d n old,
  PERM:pr
  PRE:bm, hm,
      CacheDef.rep cs d bm *
      [[ (F * rep xp (Unsync n old))%pred d ]] *
      [[ sync_invariant F ]]
  POST:bm', hm', RET: cs
      exists d', CacheDef.rep cs d' bm' *
      [[ (F * rep xp (Synced n))%pred d' ]]
  CRASH:bm'', hm'',  exists cs', CacheDef.rep cs' d bm''
    >} sync_now xp cs.
Proof.
  unfold sync_now; intros.
  step.
  safestep.
  eassign F_; cancel.
  all: eauto.
  safestep.
  eassign F_; cancel.
  all: eauto.
  step.
  step.
  eexists; repeat(eapply hashmap_subset_trans; eauto).
  rewrite <- H1; cancel; eauto.
  eexists; repeat(eapply hashmap_subset_trans; eauto).
  rewrite <- H1; cancel; eauto.
  eexists; repeat(eapply hashmap_subset_trans; eauto).
Qed.


Theorem init_ok :
  forall xp cs pr,
    {< F d v0,
     PERM:pr
     PRE:bm, hm,
        CacheDef.rep cs d bm*
        [[ (F * (LAHdr xp) |+> v0)%pred d ]] *
        [[ sync_invariant F ]]
     POST:bm', hm', RET: cs
        exists d', CacheDef.rep cs d' bm'*
         [[ (F * rep xp (Synced ((0, 0))))%pred d' ]]
     CRASH:bm'', hm'',
        any
    >} init xp cs.
Proof.
  unfold init; intros.
  step.
  safestep.
  rewrite block_mem_subset_rep; eauto.
  apply upd_eq; auto.
  all: eauto.
  step.
  safestep.
  eassign F_; eassign d'; cancel.
  all: eauto.
  safestep.
  eassign F_; eassign d'; cancel.
  all: eauto.
  step.
  step.
  unfold hdr_goodSize; cbn.
  repeat split; apply zero_lt_pow2.
  eexists; repeat (eapply hashmap_subset_trans; eauto).
  all: rewrite <- H1; cancel;
  [ apply pimpl_any |
    eexists; repeat (eapply hashmap_subset_trans; eauto) |
    unfold pimpl; intros; eauto ].
  Unshelve.
  all: unfold EqDec; apply handle_eq_dec.
Qed.


Theorem sync_invariant_rep :
  forall xp st,
    sync_invariant (rep xp st).
Proof.
  unfold rep; destruct st; eauto.
Qed.

Hint Resolve sync_invariant_rep.
Hint Extern 1 ({{_ | _}} Bind (write _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_ | _}} Bind (read _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_ | _}} Bind (sync _ _) _) => apply sync_ok : prog.
Hint Extern 1 ({{_ | _}} Bind (sync_now _ _) _) => apply sync_now_ok : prog.
Hint Extern 1 ({{_ | _}} Bind (init _ _) _) => apply init_ok : prog.
