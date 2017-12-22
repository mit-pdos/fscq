Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import PermHashmap.
Require Import HashmapProg.
Require Import Pred PermPredCrash.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import WordAuto.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import PermAsyncRecArray.
Require Export PermCacheSec.

Import ListNotations.


 Module DescSig <: RASig.

    Definition xparams := log_xparams.
    Definition RAStart := LogDescriptor.
    Definition RALen := LogDescLen.
    Definition xparams_ok (xp : xparams) := goodSize addrlen ((RAStart xp) + (RALen xp)).

    Definition itemtype := Rec.WordF addrlen.
    Definition items_per_val := valulen / addrlen.

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is.
      cbv; auto.
    Qed.

  End DescSig.


  Module DataSig <: RASig.

    Definition xparams := log_xparams.
    Definition RAStart := LogData.
    Definition RALen := LogLen.
    Definition xparams_ok (xp : xparams) := goodSize addrlen ((RAStart xp) + (RALen xp)).

    Definition itemtype := Rec.WordF valulen.
    Definition items_per_val := 1.

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is.
      cbv; auto.
    Qed.

  End DataSig.

  Module Desc := AsyncRecArray DescSig.
  Module Data := AsyncRecArray DataSig.
  Module DescDefs := Desc.Defs.
  Module DataDefs := Data.Defs.


  Definition header_type := Rec.RecF ([("previous_ndesc", Rec.WordF addrlen);
                                       ("previous_ndata", Rec.WordF addrlen);
                                       ("ndesc", Rec.WordF addrlen);
                                       ("ndata", Rec.WordF addrlen);
                                       ("addr_checksum", Rec.WordF hashlen);
                                       ("valu_checksum", Rec.WordF hashlen)]).
  Definition header := Rec.data header_type.
  Definition hdr := ((nat * nat) * (nat * nat) * (word hashlen * word hashlen))%type.
  Definition previous_length (header : hdr) := fst (fst header).
  Definition current_length (header : hdr) := snd (fst header).
  Definition checksum (header : hdr) := snd header.
  Definition mk_header (len : hdr) : header :=
    ($ (fst (previous_length len)),
     ($ (snd (previous_length len)),
      ($ (fst (current_length len)),
       ($ (snd (current_length len)),
        (fst (checksum len),
         (snd (checksum len), tt)))))).
  
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
    simpl; destruct h; tauto.
  Qed.
  
  Arguments val2hdr: simpl never.
  Opaque val2hdr.  (* for some reason "simpl never" doesn't work *)
  
  
  Definition xparams := log_xparams.
  Definition LAHdr := LogHeader.
  
  Inductive state : Type :=
  | Synced : hdr -> state
  | Unsync : hdr -> hdr -> state
  .
  
  Definition hdr_goodSize header :=
    goodSize addrlen (fst (previous_length header)) /\
    goodSize addrlen (snd (previous_length header)) /\
    goodSize addrlen (fst (current_length header)) /\
    goodSize addrlen (snd (current_length header)).
  
  Definition state_goodSize st :=
    match st with
    | Synced n => hdr_goodSize n
    | Unsync n o => hdr_goodSize n /\ hdr_goodSize o
    end.
  
  Definition rep xp state : @rawpred :=
    ([[ state_goodSize state ]] *
     match state with
     | Synced n =>
       (LAHdr xp) |+> ((Public, hdr2val (mk_header n)), nil)
     | Unsync n o =>
       (LAHdr xp) |+> ((Public, hdr2val (mk_header n)), [(Public, hdr2val (mk_header o))]%list)
     end)%pred.
  
  
  
Definition read xp cs := Eval compute_rec in
      csh <- read (LAHdr xp) cs;;
      let cs := fst csh in
      let h := snd csh in    
      v <- Unseal h;;
      let header := (val2hdr v) in
      Ret (cs,
           ((# (header :-> "previous_ndesc"),
             # (header :-> "previous_ndata")),
            (# (header :-> "ndesc"),
             # (header :-> "ndata")),
            (header :-> "addr_checksum",
             header :-> "valu_checksum"))).

Definition write xp n cs :=
    h <- Seal Public (hdr2val (mk_header n));;
    cs <- write (LAHdr xp) h cs;;
    Ret cs.

Definition sync xp cs :=
  cs <- sync (LAHdr xp) cs;;
     Ret cs.

Definition sync_now xp cs :=
  cs <- begin_sync cs;;
     cs <- PermCacheDef.sync (LAHdr xp) cs;;
     cs <- end_sync cs;;
     Ret cs.

Definition init xp cs :=
  h <- Hash default_valu;;
    hdr <- Seal Public (hdr2val (mk_header((0, 0), (0, 0), (h, h))));;
    cs <- PermCacheDef.write (LAHdr xp) hdr cs;;
    cs <- begin_sync cs;;
    cs <- PermCacheDef.sync (LAHdr xp) cs;;
    cs <- end_sync cs;;
    Ret cs.

Local Hint Unfold rep state_goodSize : hoare_unfold.

Lemma can_access_public_all:
  forall pr, can_access pr Public.
Proof.
  unfold can_access; intros; destruct pr; intuition eauto.
Qed.

Hint Resolve can_access_public_all.

Theorem write_ok :
  forall xp n cs pr,
      {< F d old,
      PERM:pr   
      PRE:bm, hm,
         PermCacheDef.rep cs d bm *
         [[ hdr_goodSize n ]] *
         [[ previous_length n = current_length old \/
         previous_length old = current_length n ]] *
         [[ (F * rep xp (Synced old))%pred d ]]
    POST:bm', hm', RET: cs
         exists d', PermCacheDef.rep cs d' bm' *
         [[ exists h, bm' = upd bm h (Public, (hdr2val (mk_header n))) ]] *                       
         [[ (F * rep xp (Unsync n old))%pred d' ]]
    XCRASH:bm'', hm'',
         exists cs' d', PermCacheDef.rep cs' d' bm'' * 
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
  eexists; repeat (eapply hashmap_subset_trans; eauto).
  erewrite <- H1; cancel; eauto.
  eexists; eapply hashmap_subset_trans; eauto.
  xcrash.

  safestep.
  rewrite rep_none_upd_pimpl; eauto.
  apply upd_eq; auto.
  eauto.
  eauto.
  step.
  step.
  eexists; repeat (eapply hashmap_subset_trans; eauto).
  erewrite <- H1; cancel; eauto.
  eexists; eapply hashmap_subset_trans; eauto.
  xcrash.
  Unshelve.
  all: unfold EqDec; apply handle_eq_dec.
Qed.

Theorem read_ok :
 forall xp cs pr,
 {< F d n,
 PERM:pr
 PRE:bm, hm,
     PermCacheDef.rep cs d bm *
     [[ (F * rep xp (Synced n))%pred d ]]
 POST:bm', hm', RET: ^(cs, r)
     PermCacheDef.rep cs d bm' *
     [[ (F * rep xp (Synced n))%pred d ]] *
     [[ r = n ]]
 CRASH:bm'', hm'',
     exists cs', PermCacheDef.rep cs' d bm''
 >} read xp cs.
Proof.
  unfold read.
  hoare.
  apply upd_eq; auto.
  subst; rewrite val2hdr2val; simpl.
  unfold hdr_goodSize in *; intuition.
  repeat rewrite wordToNat_natToWord_idempotent'; auto.
  destruct n; auto.
  destruct p as (p1 , p2); destruct p1, p2, p0; auto.
  eexists; repeat(eapply hashmap_subset_trans; eauto).
Qed.

Theorem sync_ok :
  forall xp cs pr,
    {< F d0 d n old,
     PERM:pr
     PRE:bm, hm,
       PermCacheDef.synrep cs d0 d bm *
       [[ (F * rep xp (Unsync n old))%pred d ]] *
       [[ sync_invariant F ]]
     POST:bm', hm', RET: cs
       exists d', PermCacheDef.synrep cs d0 d' bm' *
       [[ (F * rep xp (Synced n))%pred d' ]]
    CRASH:bm'', hm'',  exists cs', PermCacheDef.rep cs' d0 bm''
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
                   PermCacheDef.rep cs d bm *
                   [[ (F * rep xp (Unsync n old))%pred d ]] *
                   [[ sync_invariant F ]]
    POST:bm', hm', RET: cs
                   exists d', PermCacheDef.rep cs d' bm' *
                   [[ (F * rep xp (Synced n))%pred d' ]]
    CRASH:bm'', hm'',  exists cs', PermCacheDef.rep cs' d bm''
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
        PermCacheDef.rep cs d bm*
        [[ (F * (LAHdr xp) |+> v0)%pred d ]] *
        [[ sync_invariant F ]]
     POST:bm', hm', RET: cs
        exists d', PermCacheDef.rep cs d' bm'*
         [[ (F * rep xp (Synced ((0, 0), (0, 0),
                                 (hash_fwd default_valu,
                                  hash_fwd default_valu))))%pred d' ]]
     CRASH:bm'', hm'',
        any
    >} init xp cs.
Proof.
  unfold init, rep; intros.
  step.
  step.
  safestep.
  rewrite block_mem_subset_rep; eauto.
  cancel.
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
