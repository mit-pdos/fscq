Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import AsyncDisk.
Require Import RecArrayUtils.
Require Import AsyncRecArray.

Import ListNotations.

Set Implicit Arguments.


Module PaddedLog.

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


  (************* Log header *)
  Module Hdr.
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

    Definition state_goodSize st :=
      match st with
      | Synced n => goodSize addrlen (fst n) /\ goodSize addrlen (snd n)
      | Unsync n o => goodSize addrlen (fst n) /\ goodSize addrlen (snd n) /\
                      goodSize addrlen (fst o) /\ goodSize addrlen (snd o)
      end.

    Definition rep xp state : @rawpred :=
      ([[ state_goodSize state ]] *
      match state with
      | Synced n =>
         (LAHdr xp) |-> (hdr2val (mk_header n), nil)
      | Unsync n o =>
         (LAHdr xp) |-> (hdr2val (mk_header n), [hdr2val (mk_header o)]%list)
      end)%pred.

    Definition xform_rep_synced : forall xp n,
      crash_xform (rep xp (Synced n)) =p=> rep xp (Synced n).
    Proof.
      unfold rep; intros; simpl.
      xform; auto.
    Qed.

    Definition xform_rep_unsync : forall xp n o,
      crash_xform (rep xp (Unsync n o)) =p=> rep xp (Synced n) \/ rep xp (Synced o).
    Proof.
      unfold rep; intros; simpl.
      xform; cancel.
      or_l; cancel.
      or_r; cancel.
    Qed.

    Definition read T xp cs rx : prog T := Eval compute_rec in
      let^ (cs, v) <- BUFCACHE.read (LAHdr xp) cs;
      rx ^(cs, (# ((val2hdr v) :-> "ndesc"), # ((val2hdr v) :-> "ndata"))).

    Definition write T xp n cs rx : prog T :=
      cs <- BUFCACHE.write (LAHdr xp) (hdr2val (mk_header n)) cs;
      rx cs.

    Definition sync T xp cs rx : prog T :=
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      rx cs.

    Local Hint Unfold rep state_goodSize : hoare_unfold.

    Theorem write_ok : forall xp n cs,
    {< F d old,
    PRE            BUFCACHE.rep cs d *
                   [[ goodSize addrlen (fst n) /\ goodSize addrlen (snd n) ]] *
                   [[ (F * rep xp (Synced old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    XCRASH  exists cs' d', BUFCACHE.rep cs' d' * [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} write xp n cs.
    Proof.
      unfold write.
      hoare.
      xcrash.
    Qed.

    Theorem read_ok : forall xp cs,
    {< F d n,
    PRE            BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]]
    POST RET: ^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]] *
                   [[ r = n ]]
    CRASH exists cs', BUFCACHE.rep cs' d
    >} read xp cs.
    Proof.
      unfold read.
      hoare.
      subst; rewrite val2hdr2val; simpl.
      unfold mk_header, Rec.recget'; simpl.
      repeat rewrite wordToNat_natToWord_idempotent'; auto.
      destruct n; auto.
    Qed.

    Theorem sync_ok : forall xp cs,
    {< F d n old,
    PRE            BUFCACHE.rep cs d *
                   [[ (F * rep xp (Unsync n old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Synced n))%pred d' ]]
    XCRASH  exists cs' d', BUFCACHE.rep cs' d' *
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} sync xp cs.
    Proof.
      unfold sync.
      hoare.
      xcrash.
   Qed.

    Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
    Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
    Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

  End Hdr.


  (****************** Log contents and states *)

  Definition immut_valu := immut_word valulen.

  Definition entry := (addr * immut_valu)%type.
  Definition contents := list entry.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (l: contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated (old: contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ExtendedUnsync (old: contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | Extended (old: contents) (new: contents).

  Definition ent_addr (e : entry) := addr2w (fst e).
  Definition ent_valu (e : entry) := snd e.

  Definition ndesc_log (log : contents) := (divup (length log) DescSig.items_per_val).

  Fixpoint log_nonzero (log : contents) : list entry :=
    match log with
    | (0, _) :: rest => log_nonzero rest
    | e :: rest => e :: log_nonzero rest
    | nil => nil
    end.

  Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).

  Fixpoint nonzero_addrs (al : list addr) : nat :=
    match al with
    | 0 :: rest => nonzero_addrs rest
    | e :: rest => S (nonzero_addrs rest)
    | nil => 0
    end.

  Fixpoint combine_nonzero (al : list addr) (vl : list valu) : contents :=
    match al, vl with
    | 0 :: al', v :: vl' => combine_nonzero al' vl
    | a :: al', v :: vl' => (a, v) :: (combine_nonzero al' vl')
    | _, _ => nil
    end.

  Definition ndata_log (log : contents) := nonzero_addrs (map fst log) .

  Definition addr_valid (e : entry) := goodSize addrlen (fst e).

  Definition entry_valid (ent : entry) := fst ent <> 0 /\ addr_valid ent.

  Definition rep_contents xp (log : contents) : rawpred :=
    ( [[ Forall addr_valid log ]] *
     Desc.array_rep xp 0 (Desc.Synced (map ent_addr log)) *
     Data.array_rep xp 0 (Data.Synced (vals_nonzero log)) *
     Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
     Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))
     )%pred.

  Definition padded_addr (al : list addr) :=
    setlen al (roundup (length al) DescSig.items_per_val) 0.

  Definition padded_log (log : contents) :=
    setlen log (roundup (length log) DescSig.items_per_val) (0, $0).

  Definition rep_inner xp (st : state) : rawpred :=
  (match st with
  | Synced l =>
       Hdr.rep xp (Hdr.Synced (ndesc_log l, ndata_log l)) *
       rep_contents xp l

  | Truncated old =>
       Hdr.rep xp (Hdr.Unsync (0, 0) (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | ExtendedUnsync old =>
       Hdr.rep xp (Hdr.Synced (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | Extended old new =>
       Hdr.rep xp (Hdr.Unsync (ndesc_log old + ndesc_log new, ndata_log old + ndata_log new)
                              (ndesc_log old, ndata_log old)) *
       rep_contents xp ((padded_log old) ++ new) *
       [[ Forall entry_valid new ]]
  end)%pred.

  Definition xparams_ok xp := 
    DescSig.xparams_ok xp /\ DataSig.xparams_ok xp /\
    (LogLen xp) = DescSig.items_per_val * (LogDescLen xp).

  Definition rep xp st (hm : hashmap) :=
    ([[ xparams_ok xp ]] * rep_inner xp st)%pred.

  Local Hint Unfold rep rep_inner rep_contents xparams_ok: hoare_unfold.

  Definition avail T xp cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    rx ^(cs, ((LogLen xp) - ndesc * DescSig.items_per_val)).

  Definition read T xp cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    let^ (cs, wal) <- Desc.read_all xp ndesc cs;
    let al := map (@wordToNat addrlen) wal in
    let^ (cs, vl) <- Data.read_all xp ndata cs;
    rx ^(cs, combine_nonzero al vl).

  (* this is an evil hint *)
  Remove Hints Forall_nil.

  Lemma Forall_True : forall A (l : list A),
    Forall (fun _ : A => True) l.
  Proof.
    intros; rewrite Forall_forall; auto.
  Qed.
  Hint Resolve Forall_True.

  Lemma combine_nonzero_ok : forall l,
    combine_nonzero (map fst l) (vals_nonzero l) = log_nonzero l.
  Proof.
    unfold vals_nonzero.
    induction l; intros; simpl; auto.
    destruct a, n; simpl.
    case_eq (map ent_valu (log_nonzero l)); intros; simpl.
    apply map_eq_nil in H; auto.
    rewrite <- H; auto.
    rewrite IHl; auto.
  Qed.

  Lemma combine_nonzero_nil : forall a,
    combine_nonzero a nil = nil.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.
  Local Hint Resolve combine_nonzero_nil.

  Lemma combine_nonzero_app_zero : forall a b,
    combine_nonzero (a ++ [0]) b = combine_nonzero a b.
  Proof.
    induction a; intros; simpl; auto.
    destruct b; auto.
    destruct a, b; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma combine_nonzero_app_zeros : forall n a b,
    combine_nonzero (a ++ repeat 0 n) b = combine_nonzero a b.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply combine_nonzero_app_zero.
  Qed.

  Local Hint Resolve roundup_ge DescDefs.items_per_val_gt_0.

  Lemma combine_nonzero_padded_addr : forall a b,
    combine_nonzero (padded_addr a) b = combine_nonzero a b.
  Proof.
    unfold padded_addr, vals_nonzero.
    induction a; intros; simpl; auto.
    unfold setlen, roundup; simpl.
    rewrite divup_0; simpl; auto.

    unfold setlen, roundup; simpl.
    destruct a, b; simpl; auto;
    rewrite firstn_oob; simpl; auto;
    rewrite combine_nonzero_app_zeros; auto.
  Qed.

  Lemma map_fst_repeat : forall A B n (a : A) (b : B),
    map fst (repeat (a, b) n) = repeat a n.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.

  Lemma map_entaddr_repeat_0 : forall n b,
    map ent_addr (repeat (0, b) n) = repeat $0 n.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.

  Lemma combine_nonzero_padded_log : forall l b,
    combine_nonzero (map fst (padded_log l)) b = combine_nonzero (map fst l) b.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    induction l; simpl.
    rewrite divup_0; simpl; auto.
    
    rewrite <- IHl.
    destruct a, b, n; simpl; auto;
    repeat rewrite firstn_oob; simpl; auto;
    repeat rewrite map_app;
    setoid_rewrite map_fst_repeat;
    repeat rewrite combine_nonzero_app_zeros; auto.
  Qed.

  Lemma addr_valid_padded : forall l,
    Forall addr_valid l -> Forall addr_valid (padded_log l).
  Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob; simpl; auto.
    apply Forall_append; auto.
    rewrite Forall_forall; intros.
    apply repeat_spec in H0; subst.
    unfold addr_valid; simpl.
    apply zero_lt_pow2.
  Qed.

  Lemma padded_addr_valid : forall l,
    Forall addr_valid (padded_log l) ->
    Forall addr_valid l.
  Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob in H; auto.
    eapply forall_app_r; eauto.
  Qed.

  Local Hint Resolve addr_valid_padded padded_addr_valid.

  Lemma map_wordToNat_ent_addr : forall l,
    Forall addr_valid l ->
    (map (@wordToNat _) (map ent_addr l)) = map fst l.
  Proof.
    unfold ent_addr, addr2w.
    induction l; intros; simpl; auto.
    rewrite IHl; f_equal.
    rewrite wordToNat_natToWord_idempotent'; auto.
    apply Forall_inv in H; unfold addr_valid in H; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma combine_nonzero_padded_wordToNat : forall l,
    Forall addr_valid l ->
    combine_nonzero (map (@wordToNat _) (map ent_addr (padded_log l))) (vals_nonzero l) = log_nonzero l.
  Proof.
    intros; unfold ent_addr, addr2w.
    rewrite <- combine_nonzero_ok.
    rewrite <- combine_nonzero_padded_log.
    f_equal.
    rewrite map_wordToNat_ent_addr; auto.
  Qed.

  Lemma vals_nonzero_addrs : forall l,
    length (vals_nonzero l) = nonzero_addrs (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.

  Lemma log_nonzero_addrs : forall l,
    length (log_nonzero l) = nonzero_addrs (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.

  Lemma desc_ipack_padded : forall l,
    DescDefs.ipack (map ent_addr l) = DescDefs.ipack (map ent_addr (padded_log l)).
  Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob, map_app, map_entaddr_repeat_0 by auto.
    rewrite DescDefs.ipack_app_item0; auto.
    rewrite map_length; auto.
  Qed.

  Local Hint Resolve combine_nonzero_padded_wordToNat.

  Lemma desc_padding_synced_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Synced (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.

  Lemma desc_padding_unsync_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Unsync (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H.
     rewrite firstn_oob, map_app in H by auto.
     apply Desc.items_valid_app in H; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.

  Lemma goodSize_ndesc : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndesc_log l).
  Proof.
    intros; unfold ndesc_log.
    eapply goodSize_trans; [ apply divup_le | eauto ].
    destruct (mult_O_le (length l) DescSig.items_per_val); auto.
    contradict H0; apply DescDefs.items_per_val_not_0.
  Qed.
  Local Hint Resolve goodSize_ndesc.

  Lemma padded_log_length: forall l,
    length (padded_log l) = roundup (length l) DescSig.items_per_val.
  Proof.
    unfold padded_log, roundup; intros.
    rewrite setlen_length; auto.
  Qed.

  Lemma nonzero_addrs_app_zero : forall a,
    nonzero_addrs (a ++ [0]) = nonzero_addrs a.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.

  Lemma nonzero_addrs_app_zeros : forall n a,
    nonzero_addrs (a ++ repeat 0 n) = nonzero_addrs a.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply nonzero_addrs_app_zero.
  Qed.

  Lemma nonzero_addrs_padded_log : forall l,
    nonzero_addrs (map fst (padded_log l)) = nonzero_addrs (map fst l).
  Proof.
    unfold padded_log; induction l; simpl; auto.
    rewrite setlen_nil, repeat_is_nil; simpl; auto.
    unfold roundup; rewrite divup_0; omega.
    
    destruct a, n; simpl;
    rewrite <- IHl;
    unfold setlen, roundup;
    repeat rewrite firstn_oob, map_app by auto;
    setoid_rewrite map_fst_repeat;
    repeat rewrite nonzero_addrs_app_zeros; simpl; auto.
  Qed.

  Lemma vals_nonzero_length : forall l,
    length (vals_nonzero l) <= length l.
  Proof.
    unfold vals_nonzero; induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
    autorewrite with lists in *; omega.
  Qed.

  Lemma ndata_log_goodSize : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndata_log l).
  Proof.
    unfold ndata_log; intros.
    rewrite <- vals_nonzero_addrs.
    eapply goodSize_trans.
    apply vals_nonzero_length; auto.
    auto.
  Qed.
  Local Hint Resolve ndata_log_goodSize.


  Arguments Desc.array_rep : simpl never.
  Arguments Data.array_rep : simpl never.
  Arguments Desc.avail_rep : simpl never.
  Arguments Data.avail_rep : simpl never.
  Arguments divup : simpl never.
  Hint Extern 0 (okToUnify (Hdr.rep _ _) (Hdr.rep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.array_rep _ _ _) (Desc.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.array_rep _ _ _) (Data.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.avail_rep _ _ _) (Desc.avail_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.avail_rep _ _ _) (Data.avail_rep _ _ _)) => constructor : okToUnify.


  Definition avail_ok : forall xp cs,
    {< F l d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = (LogLen xp) - roundup (length l) DescSig.items_per_val ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    >} avail xp cs.
  Proof.
    unfold avail.
    safestep.
    safestep.
    cancel.
  Qed.

  Definition read_ok : forall xp cs,
    {< F l d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = log_nonzero l ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    >} read xp cs.
  Proof.
    unfold read.
    safestep.
    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    rewrite map_length, padded_log_length.
    auto. auto.
    pred_apply.
    rewrite desc_padding_synced_piff; cancel.

    safestep.
    setoid_rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); omega.

    safestep.
    rewrite desc_padding_synced_piff; cancel.
    replace (map ent_valu (log_nonzero l)) with (vals_nonzero l); auto.

    all: cancel.
    rewrite desc_padding_synced_piff; cancel.
  Qed.


  Lemma goodSize_0 : forall sz, goodSize sz 0.
  Proof.
    unfold goodSize; intros.
    apply zero_lt_pow2.
  Qed.

  Lemma ndesc_log_nil : ndesc_log nil = 0.
  Proof.
    unfold ndesc_log; simpl.
    rewrite divup_0; auto.
  Qed.

  Lemma ndata_log_nil : ndata_log nil = 0.
  Proof.
    unfold ndata_log; simpl; auto.
  Qed.

  Local Hint Resolve goodSize_0.


  Definition trunc T xp cs rx : prog T :=
    cs <- Hdr.write xp (0, 0) cs;
    cs <- Hdr.sync xp cs;
    rx cs.

  Local Hint Resolve Forall_nil.

  Lemma helper_sep_star_reorder : forall (a b c d : rawpred),
    a * b * c * d =p=> (a * c) * (b * d).
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_add_sub_0 : forall a b,
    a <= b -> a + (b - a) + 0 = b.
  Proof.
    intros; omega.
  Qed.

  Lemma helper_trunc_ok : forall xp l,
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr l)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero l)) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    Hdr.rep xp (Hdr.Synced (0, 0))
    =p=>
    Hdr.rep xp (Hdr.Synced (ndesc_log [], ndata_log [])) *
    Desc.array_rep xp 0 (Desc.Synced []) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero [])) *
    Desc.avail_rep xp (ndesc_log []) (LogDescLen xp - ndesc_log []) *
    Data.avail_rep xp (ndata_log []) (LogLen xp - ndata_log []).
  Proof.
    intros.
    unfold ndesc_log, vals_nonzero; simpl; rewrite divup_0.
    rewrite Desc.array_rep_sync_nil_sep_star, Data.array_rep_sync_nil_sep_star; auto.
    cancel.
    unfold ndata_log; simpl; repeat rewrite Nat.sub_0_r.
    rewrite <- log_nonzero_addrs.
    rewrite Data.array_rep_size_ok_pimpl, Desc.array_rep_size_ok_pimpl.
    rewrite Data.array_rep_avail, Desc.array_rep_avail.
    simpl; rewrite divup_1; autorewrite with lists.
    cancel.
    rewrite helper_sep_star_reorder.
    rewrite Desc.avail_rep_merge by auto.
    rewrite Data.avail_rep_merge by auto.
    repeat rewrite helper_add_sub_0 by auto.
    cancel.
  Qed.

  Definition trunc_ok : forall xp cs,
    {< F l d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: cs  exists d',
          BUFCACHE.rep cs d' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * [[ (F * (rep xp (Truncated l) hm'))%pred d' ]]
    >} trunc xp cs.
  Proof.
    unfold trunc.
    step.
    step.
    step.
    cancel_by helper_trunc_ok.

    (* crash conditions *)
    xcrash.
    xcrash.
  Qed.

  Definition loglen_valid xp ndesc ndata :=
    ndesc <= LogDescLen xp  /\ ndata <= LogLen xp.

  Definition loglen_invalid xp ndesc ndata :=
    ndesc > LogDescLen xp \/ ndata > LogLen xp.

  Definition loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.
  Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec (LogDescLen xp) ndesc);
    destruct (lt_dec (LogLen xp) ndata); simpl; auto.
    left; intuition.
  Defined.

  Remove Hints goodSize_0.

  Definition entry_valid_ndata : forall l,
    Forall entry_valid l -> ndata_log l = length l.
  Proof.
    unfold ndata_log; induction l; rewrite Forall_forall; intuition.
    destruct a, n; simpl.
    exfalso; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    rewrite Forall_forall; intros.
    apply H; simpl; intuition.
  Qed.

  Lemma loglen_valid_desc_valid : forall xp old new,
    DescSig.xparams_ok xp ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Desc.items_valid xp (ndesc_log old) (map ent_addr new).
  Proof.
    unfold Desc.items_valid, loglen_valid.
    intuition.
    unfold DescSig.RALen; omega.
    autorewrite with lists; unfold DescSig.RALen.
    apply divup_ge; auto.
    unfold ndesc_log in *; omega.
  Qed.
  Local Hint Resolve loglen_valid_desc_valid.


  Lemma loglen_valid_data_valid : forall xp old new,
    DataSig.xparams_ok xp ->
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Data.items_valid xp (ndata_log old) (map ent_valu new).
  Proof.
    unfold Data.items_valid, loglen_valid.
    intuition.
    unfold DataSig.RALen; omega.
    autorewrite with lists; unfold DataSig.RALen.
    apply divup_ge; auto.
    rewrite divup_1; rewrite <- entry_valid_ndata by auto.
    unfold ndata_log in *; omega.
  Qed.
  Local Hint Resolve loglen_valid_data_valid.

  Lemma helper_loglen_desc_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndesc_log new + (LogDescLen xp - ndesc_log old - ndesc_log new) 
      = LogDescLen xp - ndesc_log old.
  Proof.
    unfold loglen_valid, ndesc_log; intros.
    omega.
  Qed.

  Lemma helper_loglen_data_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndata_log new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
  Proof.
    unfold loglen_valid, ndata_log; intros.
    omega.
  Qed.

  Lemma helper_loglen_data_valid_extend_entry_valid : forall xp new old,
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
  Proof.
    intros.
    rewrite <- entry_valid_ndata by auto.
    apply helper_loglen_data_valid_extend; auto.
  Qed.

  Lemma padded_desc_valid : forall xp st l,
    Desc.items_valid xp st (map ent_addr l)
    -> Desc.items_valid xp st (map ent_addr (padded_log l)).
  Proof.
    unfold Desc.items_valid; intuition.
    autorewrite with lists in *.
    rewrite padded_log_length; unfold roundup.
    apply Nat.mul_le_mono_pos_r.
    apply DescDefs.items_per_val_gt_0.
    apply divup_le; lia.
  Qed.

  Lemma mul_le_mono_helper : forall a b,
    b > 0 -> a <= a * b.
  Proof.
    intros; rewrite Nat.mul_comm.
    destruct (mult_O_le a b); auto; omega.
  Qed.

  Lemma loglen_valid_goodSize_l : forall xp a b,
    loglen_valid xp a b -> DescSig.xparams_ok xp -> DataSig.xparams_ok xp ->
    goodSize addrlen a.
  Proof.
    unfold loglen_valid, DescSig.xparams_ok, DataSig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply le_trans. eauto.
    apply le_plus_r. eauto.
  Qed.

  Lemma loglen_valid_goodSize_r : forall xp a b,
    loglen_valid xp a b -> DescSig.xparams_ok xp -> DataSig.xparams_ok xp ->
    goodSize addrlen b.
  Proof.
    unfold loglen_valid, DescSig.xparams_ok, DataSig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply le_trans. eauto.
    apply le_plus_r. eauto.
  Qed.

  Lemma ent_valid_addr_valid : forall l,
    Forall entry_valid l -> Forall addr_valid l.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    apply H; auto.
  Qed.
  Local Hint Resolve ent_valid_addr_valid.
  Local Hint Resolve Forall_append DescDefs.items_per_val_not_0.

  Lemma helper_add_sub : forall a b,
    a <= b -> a + (b - a) = b.
  Proof.
    intros; omega.
  Qed.


  Lemma nonzero_addrs_app : forall a b,
    nonzero_addrs (a ++ b) = nonzero_addrs a + nonzero_addrs b.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; auto.
    rewrite IHa; omega.
  Qed.

  Lemma ndata_log_app : forall a b,
    ndata_log (a ++ b) = ndata_log a + ndata_log b.
  Proof.
    unfold ndata_log;  intros.
    repeat rewrite map_app.
    rewrite nonzero_addrs_app; auto.
  Qed.

  Lemma ndesc_log_padded_log : forall l,
    ndesc_log (padded_log l) = ndesc_log l.
  Proof.
    unfold ndesc_log; intros.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_divup; auto.
  Qed.

  Lemma ndesc_log_app : forall a b,
    length a = roundup (length a) DescSig.items_per_val ->
    ndesc_log (a ++ b) = ndesc_log a + ndesc_log b.
  Proof.
    unfold ndesc_log; intros.
    rewrite app_length, H at 1.
    unfold roundup.
    rewrite Nat.add_comm, Nat.mul_comm.
    rewrite divup_add by auto.
    omega.
  Qed.

  Lemma ndesc_log_padded_app : forall a b,
    ndesc_log (padded_log a ++ b) = ndesc_log a + ndesc_log b.
  Proof.
    intros.
    rewrite ndesc_log_app.
    rewrite ndesc_log_padded_log; auto.
    rewrite padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.

  Lemma ndata_log_padded_log : forall a,
    ndata_log (padded_log a) = ndata_log a.
  Proof.
    unfold ndata_log, padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    repeat rewrite map_app.
    rewrite repeat_map; simpl.
    rewrite nonzero_addrs_app.
    setoid_rewrite <- app_nil_l at 3.
    rewrite nonzero_addrs_app_zeros; auto.
  Qed.


  Lemma ndata_log_padded_app : forall a b,
    ndata_log (padded_log a ++ b) = ndata_log a + ndata_log b.
  Proof.
    intros.
    rewrite ndata_log_app.
    rewrite ndata_log_padded_log; auto.
  Qed.

  Lemma vals_nonzero_app : forall a b,
    vals_nonzero (a ++ b) = vals_nonzero a ++ vals_nonzero b.
  Proof.
    unfold vals_nonzero; induction a; intros; simpl; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma log_nonzero_repeat_0 : forall n,
    log_nonzero (repeat (0, $0) n) = nil.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma log_nonzero_app : forall a b,
    log_nonzero (a ++ b) = log_nonzero a ++ log_nonzero b.
  Proof.
    induction a; simpl; intros; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma vals_nonzero_padded_log : forall l,
    vals_nonzero (padded_log l) = vals_nonzero l.
  Proof.
    unfold vals_nonzero, padded_log, setlen, roundup; simpl.
    induction l; intros; simpl; auto.
    rewrite firstn_oob; simpl; auto.
    rewrite log_nonzero_repeat_0; auto.

    destruct a, n.
    rewrite <- IHl.
    repeat rewrite firstn_oob; simpl; auto.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.

    repeat rewrite firstn_oob; simpl; auto.
    f_equal.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.
    simpl; rewrite app_nil_r; auto.
  Qed.

  Lemma entry_valid_vals_nonzero : forall l,
    Forall entry_valid l ->
    log_nonzero l = l.
  Proof.
    unfold entry_valid; induction l; simpl; auto.
    destruct a, n; simpl; auto; intros.
    exfalso.
    rewrite Forall_forall in H; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma nonzero_addrs_entry_valid : forall l,
    Forall entry_valid l ->
    nonzero_addrs (map fst l) = length l.
  Proof.
    induction l; simpl; intros; auto.
    destruct a, n; simpl.
    exfalso.
    rewrite Forall_forall in H.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma extend_ok_helper : forall F xp old new,
    Forall entry_valid new ->
    Data.array_rep xp (ndata_log old) (Data.Synced (map ent_valu new)) *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new) *
    Data.avail_rep xp (ndata_log old + divup (length (map ent_valu new)) DataSig.items_per_val)
      (LogLen xp - ndata_log old - ndata_log new) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced (map ent_addr (padded_log new))) * F
    =p=>
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ new))) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old ++ new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ new)) 
                      (LogDescLen xp - ndesc_log (padded_log old ++ new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ new))
                      (LogLen xp - ndata_log (padded_log old ++ new)) * F.
  Proof.
    intros.
    repeat rewrite ndesc_log_padded_app, ndata_log_padded_app.
    setoid_rewrite Nat.sub_add_distr.
    unfold ndesc_log.
    rewrite divup_1.
    rewrite entry_valid_ndata with (l := new); auto.
    repeat rewrite map_length.
    rewrite map_app, vals_nonzero_app.
    rewrite <- Desc.array_rep_synced_app.
    rewrite <- Data.array_rep_synced_app.
    repeat rewrite Nat.add_0_l.
    repeat rewrite desc_padding_synced_piff.
    repeat rewrite map_length.
    repeat rewrite vals_nonzero_padded_log.
    rewrite divup_1, padded_log_length.
    unfold roundup; rewrite divup_mul; auto.
    unfold ndata_log; rewrite vals_nonzero_addrs.
    unfold vals_nonzero; rewrite entry_valid_vals_nonzero with (l := new); auto.
    cancel.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.

  Lemma nonzero_addrs_bound : forall l,
    nonzero_addrs l <= length l.
  Proof.
    induction l; simpl; auto.
    destruct a; omega.
  Qed.

  Lemma extend_ok_synced_hdr_helper : forall xp old new,
    Hdr.rep xp (Hdr.Synced (ndesc_log old + ndesc_log new, ndata_log old + ndata_log new))
    =p=>
    Hdr.rep xp (Hdr.Synced (ndesc_log (padded_log old ++ new),
                            ndata_log (padded_log old ++ new))).
  Proof.
    intros.
    rewrite ndesc_log_padded_app, ndata_log_padded_app; auto.
  Qed.

  Local Hint Resolve extend_ok_synced_hdr_helper.

  Lemma nonzero_addrs_roundup : forall B (l : list (addr * B)) n,
    n > 0 ->
    nonzero_addrs (map fst l) <= (divup (length l) n) * n.
  Proof.
    intros.
    eapply le_trans.
    apply nonzero_addrs_bound.
    rewrite map_length.
    apply roundup_ge; auto.
  Qed.

  Lemma loglen_invalid_overflow : forall xp old new,
    LogLen xp = DescSig.items_per_val * LogDescLen xp ->
    loglen_invalid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length (padded_log old ++ new) > LogLen xp.
  Proof.
    unfold loglen_invalid, ndesc_log, ndata_log; intros.
    rewrite app_length; repeat rewrite padded_log_length.
    unfold roundup; intuition.
    rewrite H.
    setoid_rewrite <- Nat.mul_comm at 2.
    apply divup_add_gt; auto.

    eapply lt_le_trans; eauto.
    apply Nat.add_le_mono.
    apply nonzero_addrs_roundup; auto.
    erewrite <- map_length.
    apply nonzero_addrs_bound.
  Qed.

  Hint Rewrite Desc.array_rep_avail Data.array_rep_avail
     padded_log_length divup_mul divup_1 map_length
     ndesc_log_padded_log nonzero_addrs_padded_log using auto: extend_crash.
  Hint Unfold roundup ndata_log : extend_crash.

  Ltac extend_crash :=
     repeat (autorewrite with extend_crash; autounfold with extend_crash; simpl);
     setoid_rewrite <- Desc.avail_rep_merge at 3;
     [ setoid_rewrite <- Data.avail_rep_merge at 3 | ];
     [ cancel
     | apply helper_loglen_data_valid_extend_entry_valid; auto
     | apply helper_loglen_desc_valid_extend; auto ].


  Definition extend T xp log cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    let '(nndesc, nndata) := ((ndesc_log log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
        (* synced *)
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;
       (* extended unsync *)
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;
      cs <- Data.sync_aligned xp ndata nndata cs;
      cs <- Hdr.write xp (ndesc + nndesc, ndata + nndata) cs;
      cs <- Hdr.sync xp cs;
       (* synced*)
      rx ^(cs, true)
    } else {
      rx ^(cs, false)
    }.


  Definition extend_ok : forall xp new cs,
    {< F old d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ Forall entry_valid new ]] *
          [[ (F * rep xp (Synced old) hm)%pred d ]]
    POST:hm' RET: ^(cs, r) exists d',
          BUFCACHE.rep cs d' * (
          [[ r = true /\
             (F * rep xp (Synced ((padded_log old) ++ new)) hm')%pred d' ]] \/
          [[ r = false /\ length ((padded_log old) ++ new) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Synced old) hm')%pred d' ]] \/
          [[  (F * rep xp (Extended old new) hm')%pred d' ]])
    >} extend xp new cs.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      safestep.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      safestep.
      unfold loglen_valid in *; unfold Data.items_valid; intuition.
      unfold DataSig.RALen; omega.
      autorewrite with lists.
      rewrite <- entry_valid_ndata by auto.
      replace DataSig.items_per_val with 1 by (cbv; auto).
      unfold DataSig.RALen; omega.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.

      (* sync content *)
      prestep. norm. cancel. intuition simpl.
      instantiate ( 1 := map ent_addr (padded_log new) ).
      rewrite map_length, padded_log_length; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      rewrite desc_padding_unsync_piff.
      pred_apply; cancel.

      safestep.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      unfold loglen_valid in *; unfold Data.items_valid; intuition.
      unfold DataSig.RALen; omega.
      autorewrite with lists.
      rewrite <- entry_valid_ndata by auto.
      replace DataSig.items_per_val with 1 by (cbv; auto).
      unfold DataSig.RALen; omega.

      (* write header *)
      safestep.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      (* sync header *)
      safestep.

      (* post condition *)
      safestep.
      or_l; cancel.
      cancel_by extend_ok_helper; auto.

      (* crashes *)
      (* after header write : Extended *)
      rewrite ndesc_log_app, ndata_log_app.
      rewrite ndesc_log_padded_log, ndata_log_padded_log.
      eauto.
      rewrite padded_log_length, roundup_roundup; auto.
      xcrash.
      or_r; cancel.
      cancel_by extend_ok_helper; auto.

      (* after header sync : Synced new *)
      xcrash.
      or_r; cancel.
      cancel_by extend_ok_helper; auto.

      (* before header write : ExtendedUnsync *)
      xcrash.
      or_l; cancel.
      extend_crash.

      xcrash.
      or_l; cancel.
      extend_crash.

      xcrash.
      or_l; cancel.
      extend_crash.

      (* before write desc : Synced old *)
      xcrash.
      or_l; cancel.
      rewrite Desc.avail_rep_merge. cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.

    (* false case *)
    - step.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.

    (* crash for the false case *)
    - cancel.
      xcrash.
      or_l; cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _) _) => apply extend_ok : prog.

  Lemma log_nonzero_padded_log : forall l,
    log_nonzero (padded_log l) = log_nonzero l.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    rewrite log_nonzero_app.
    rewrite log_nonzero_repeat_0, app_nil_r; auto.
  Qed.

  Lemma log_nonzero_padded_app : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (padded_log l ++ padded_log new).
  Proof.
    intros.
    rewrite log_nonzero_app.
    repeat rewrite log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.

  Lemma log_nonzero_app_padded : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (l ++ padded_log new).
  Proof.
    intros.
    rewrite log_nonzero_app, log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.

  Theorem rep_synced_length_ok : forall F xp l d hm,
    (F * rep xp (Synced l) hm)%pred d -> length l <= LogLen xp.
  Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    rewrite map_length, Nat.sub_0_r in *.
    rewrite H5, Nat.mul_comm; auto.
  Qed.

  Lemma xform_rep_synced : forall xp l hm,
    crash_xform (rep xp (Synced l) hm) =p=> rep xp (Synced l) hm.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
  Qed.

  Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=>
      rep xp (Synced l) hm \/ rep xp (Synced nil) hm.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_unsync.
    norm; auto.

    or_r; cancel.
    cancel_by helper_trunc_ok.
    or_l; cancel.
  Qed.

  Lemma xform_rep_extended_unsync : forall xp l hm,
    crash_xform (rep xp (ExtendedUnsync l) hm) =p=> rep xp (Synced l) hm.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.

    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
  Qed.


  Theorem rep_extended_facts' : forall xp d old new hm,
    (rep xp (Extended old new) hm)%pred d ->
    Forall entry_valid new /\
    LogLen xp >= ndata_log old + ndata_log new /\ LogDescLen xp >= ndesc_log old + ndesc_log new.
  Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    rewrite map_length, Nat.sub_0_r in *.
    unfold ndata_log, ndesc_log; split; auto; split.

    rewrite H4, Nat.mul_comm.
    eapply le_trans; [ | eauto ].
    rewrite app_length, nonzero_addrs_entry_valid with (l := new) by auto.
    apply plus_le_compat_r.
    eapply le_trans.
    apply nonzero_addrs_bound.
    rewrite padded_log_length, map_length.
    apply roundup_ge; auto.

    eapply Nat.mul_le_mono_pos_r with (p := DescSig.items_per_val).
    apply DescDefs.items_per_val_gt_0.
    rewrite app_length, padded_log_length in H16.
    apply roundup_le in H16.
    rewrite roundup_roundup_add in H16 by auto.
    rewrite Nat.mul_add_distr_r.
    eapply le_trans; eauto.
  Qed.

  Theorem rep_extended_facts : forall xp old new hm,
    rep xp (Extended old new) hm =p=>
    (rep xp (Extended old new) hm *
      [[ LogLen xp >= ndata_log old + ndata_log new ]] *
      [[ LogDescLen xp >= ndesc_log old + ndesc_log new ]] *
      [[ Forall entry_valid new ]] )%pred.
  Proof.
    unfold pimpl; intros.
    pose proof rep_extended_facts' H.
    pred_apply; cancel.
  Qed.

  Lemma helper_sep_star_distr: forall AT AEQ V (a b c d : @pred AT AEQ V),
    a * b * c * d =p=> (c * a) * (d * b).
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_add_sub_add : forall a b c,
    b >= c + a -> a + (b - (c + a)) = b - c.
  Proof.
    intros; omega.
  Qed.

  Lemma xform_rep_extended_helper : forall xp old new,
    Forall entry_valid new ->
    LogLen xp >= ndata_log old + ndata_log new ->
    LogDescLen xp >= ndesc_log old + ndesc_log new ->
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ new))) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old ++ new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ new)) (LogDescLen xp - ndesc_log (padded_log old ++ new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ new)) (LogLen xp - ndata_log (padded_log old ++ new))
    =p=>
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old) *
    Data.avail_rep xp (ndata_log old) (LogLen xp - ndata_log old).
  Proof.
    intros.
    rewrite map_app, vals_nonzero_app.
    rewrite ndesc_log_padded_app, ndata_log_padded_app.
    rewrite Desc.array_rep_synced_app_rev, Data.array_rep_synced_app_rev.
    repeat rewrite Nat.add_0_l.
    rewrite map_length, vals_nonzero_padded_log, padded_log_length.
    setoid_rewrite desc_padding_synced_piff.
    cancel.

    rewrite Data.array_rep_avail, Desc.array_rep_avail; simpl.
    unfold roundup; rewrite divup_divup by auto.
    setoid_rewrite vals_nonzero_addrs.
    setoid_rewrite divup_1.
    setoid_rewrite map_length.
    unfold ndata_log, ndesc_log.
    rewrite helper_sep_star_distr.
    rewrite Desc.avail_rep_merge, Data.avail_rep_merge.
    cancel.
    apply helper_add_sub_add; auto.
    apply helper_add_sub_add; auto.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.

  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (Synced ((padded_log old) ++ new)) hm.
  Proof.
    intros; rewrite rep_extended_facts.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.

    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_unsync.
    norm; auto.

    or_r; cancel.
    rewrite extend_ok_synced_hdr_helper; auto.

    or_l; cancel.
    apply xform_rep_extended_helper; auto.

    apply padded_addr_valid.
    eapply forall_app_r; eauto.
  Qed.

  Lemma rep_synced_app_pimpl : forall xp old new hm,
    rep xp (Synced (padded_log old ++ new)) hm =p=>
    rep xp (Synced (padded_log old ++ padded_log new)) hm.
  Proof.
    unfold rep; simpl; intros; unfold rep_contents; cancel.
    setoid_rewrite ndesc_log_padded_app.
    setoid_rewrite ndata_log_padded_app.
    rewrite ndesc_log_padded_log, ndata_log_padded_log.
    setoid_rewrite map_app.
    setoid_rewrite vals_nonzero_app.
    setoid_rewrite vals_nonzero_padded_log.
    cancel.

    rewrite Desc.array_rep_synced_app_rev.
    setoid_rewrite <- desc_padding_synced_piff at 2.
    eapply pimpl_trans2.
    eapply Desc.array_rep_synced_app.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    cancel.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    apply Forall_append.
    eapply forall_app_r; eauto.
    eapply forall_app_l in H2.
    apply addr_valid_padded; auto.
  Qed.

End PaddedLog.


Module DLog.

  Definition entry := (addr * valu)%type.
  Definition contents := list entry.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (navail : nat) (l: contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated  (old: contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ExtendedUnsync (old: contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | Extended  (old: contents) (new: contents).

  Definition rep_common l padded : rawpred :=
      ([[ l = PaddedLog.log_nonzero padded /\
         length padded = roundup (length padded) PaddedLog.DescSig.items_per_val ]])%pred.

  Definition rep xp st hm :=
    (match st with
    | Synced navail l =>
          exists padded, rep_common l padded *
          [[ navail = (LogLen xp) - (length padded) ]] *
          PaddedLog.rep xp (PaddedLog.Synced padded) hm
    | Truncated l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Truncated padded) hm
    | ExtendedUnsync l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.ExtendedUnsync padded) hm
    | Extended l new =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Extended padded new) hm
    end)%pred.

  Local Hint Unfold rep rep_common : hoare_unfold.

  Section UnifyProof.
  Hint Extern 0 (okToUnify (PaddedLog.rep _ _ _) (PaddedLog.rep _ _ _)) => constructor : okToUnify.

  Definition read T xp cs rx : prog T :=
    r <- PaddedLog.read xp cs;
    rx r.

  Definition read_ok : forall xp cs,
    {< F l d nr,
    PRE:hm    BUFCACHE.rep cs d *
              [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
              BUFCACHE.rep cs d *
              [[ r = l /\ (F * rep xp (Synced nr l) hm')%pred d ]]
    CRASH:hm' exists cs',
              BUFCACHE.rep cs' d *
              [[ (F * rep xp (Synced nr l) hm')%pred d ]]
    >} read xp cs.
  Proof.
    unfold read.
    hoare.
  Qed.

  Definition trunc T xp cs rx : prog T :=
    cs <- PaddedLog.trunc xp cs;
    rx cs.

  Definition trunc_ok : forall xp cs,
    {< F l d nr,
    PRE:hm    BUFCACHE.rep cs d *
              [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: cs exists d',
              BUFCACHE.rep cs d' *
              [[ (F * rep xp (Synced (LogLen xp) nil) hm')%pred d' ]]
    XCRASH:hm' exists cs d',
              BUFCACHE.rep cs d' *
              [[ (F * rep xp (Truncated l) hm')%pred d' ]]
    >} trunc xp cs.
  Proof.
    unfold trunc.
    hoare.
    unfold roundup; rewrite divup_0; omega.

    (* crashes *)
    xcrash.
  Qed.


  Definition avail T xp cs rx : prog T :=
    r <- PaddedLog.avail xp cs;
    rx r.

  Definition avail_ok : forall xp cs,
    {< F l d nr,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]] *
          [[ r = nr ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]]
    >} avail xp cs.
  Proof.
    unfold avail.
    step.
    step.
  Qed.

  End UnifyProof.

  Local Hint Resolve PaddedLog.DescDefs.items_per_val_gt_0.

  Lemma extend_length_ok' : forall l new,
    length l = roundup (length l) PaddedLog.DescSig.items_per_val ->
    length (l ++ PaddedLog.padded_log new)
      = roundup (length (l ++ PaddedLog.padded_log new)) PaddedLog.DescSig.items_per_val.
  Proof.
    intros.
    repeat rewrite app_length.
    repeat rewrite PaddedLog.padded_log_length.
    rewrite H.
    rewrite roundup_roundup_add, roundup_roundup; auto.
  Qed.

  Lemma extend_length_ok : forall l new,
    length l = roundup (length l) PaddedLog.DescSig.items_per_val ->
    length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)
      = roundup (length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)) PaddedLog.DescSig.items_per_val.
  Proof.
    intros.
    apply extend_length_ok'.
    rewrite PaddedLog.padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.

  Lemma helper_extend_length_ok : forall xp padded new F d hm,
    length padded = roundup (length padded) PaddedLog.DescSig.items_per_val
    -> length (PaddedLog.padded_log padded ++ new) > LogLen xp
    -> (F * PaddedLog.rep xp (PaddedLog.Synced padded) hm)%pred d
    -> length new > LogLen xp - length padded.
  Proof.
    intros.
    rewrite app_length in H0.
    pose proof (PaddedLog.rep_synced_length_ok H1).
    generalize H2.
    rewrite H.
    rewrite <- PaddedLog.padded_log_length.
    intro; omega.
  Qed.

  Local Hint Resolve extend_length_ok helper_extend_length_ok PaddedLog.log_nonzero_padded_app.

  Definition extend T xp new cs rx : prog T :=
    r <- PaddedLog.extend xp new cs;
    rx r.

  Definition rounded n := roundup n PaddedLog.DescSig.items_per_val.

  Definition entries_valid l := Forall PaddedLog.entry_valid l.

  Lemma extend_navail_ok : forall xp padded new, 
    length padded = roundup (length padded) PaddedLog.DescSig.items_per_val ->
    LogLen xp - length padded - rounded (length new)
    = LogLen xp - length (PaddedLog.padded_log padded ++ PaddedLog.padded_log new).
  Proof.
    unfold rounded; intros.
    rewrite extend_length_ok by auto.
    rewrite app_length.
    rewrite H.
    repeat rewrite PaddedLog.padded_log_length.
    rewrite roundup_roundup_add by auto.
    rewrite roundup_roundup by auto.
    omega.
  Qed.

  Local Hint Resolve extend_navail_ok PaddedLog.rep_synced_app_pimpl.

  Definition extend_ok : forall xp new cs,
    {< F old d nr,
    PRE:hm
          BUFCACHE.rep cs d * [[ entries_valid new ]] *
          [[ (F * rep xp (Synced nr old) hm)%pred d ]]
    POST:hm' RET: ^(cs, r) exists d',
          BUFCACHE.rep cs d' * (
          [[ r = true /\
            (F * rep xp (Synced (nr - (rounded (length new))) (old ++ new)) hm')%pred d' ]] \/
          [[ r = false /\ length new > nr /\
            (F * rep xp (Synced nr old) hm')%pred d' ]])
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Synced nr old) hm')%pred d' ]] \/
          [[ (F * rep xp (Extended old new) hm')%pred d' ]])
    >} extend xp new cs.
  Proof.
    unfold extend.

    safestep.
    eassign dummy; cancel.
    safestep.

    or_l; norm; [ cancel | intuition; pred_apply; norm ].
    eassign (PaddedLog.padded_log dummy ++ PaddedLog.padded_log new).
    cancel; auto.
    intuition.
    or_r; cancel; eauto.

    xcrash.
    or_l; cancel.
    or_r; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _) _) => apply extend_ok : prog.


  (* ExtendedUnsync is actually a redundent state, it is equivalent to Synced *)
  Lemma extend_unsynced_synced : forall xp l hm,
    rep xp (ExtendedUnsync l) hm =p=> exists na, rep xp (Synced na l) hm.
  Proof.
    unfold rep, rep_common; cancel; eauto.
  Qed.

  Lemma synced_extend_unsynced : forall xp l na hm,
    rep xp (Synced na l) hm =p=> rep xp (ExtendedUnsync l) hm.
  Proof.
    unfold rep, rep_common; cancel; eauto.
  Qed.


  Lemma xform_rep_synced : forall xp na l hm,
    crash_xform (rep xp (Synced na l) hm) =p=> rep xp (Synced na l) hm.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply PaddedLog.xform_rep_synced.
    all: auto.
  Qed.

  Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=> exists na,
      rep xp (Synced na l) hm \/ rep xp (Synced (LogLen xp) nil) hm.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    rewrite PaddedLog.xform_rep_truncated.
    cancel.
    or_r; cancel.
    rewrite roundup_0; auto.
  Qed.

  Lemma xform_rep_extended_unsync : forall xp l hm,
    crash_xform (rep xp (ExtendedUnsync l) hm) =p=> exists na, rep xp (Synced na l) hm.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply PaddedLog.xform_rep_extended_unsync.
    all: auto.
  Qed.

  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       (exists na, rep xp (Synced na old) hm) \/
       (exists na, rep xp (Synced na (old ++ new)) hm).
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite PaddedLog.rep_extended_facts.
    xform; cancel.
    rewrite PaddedLog.xform_rep_extended.
    cancel.
    or_r; norm.
    instantiate (1 := (PaddedLog.padded_log x ++ PaddedLog.padded_log new)).
    cancel; auto.
    intuition.
  Qed.

End DLog.

