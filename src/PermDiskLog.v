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
Require Export PermDiskLogHdr.

Set Implicit Arguments.

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

Definition entry := (addr * tagged_block)%type.
Definition contents := list entry.

Inductive state :=
(* The log is synced on disk *)
| Synced (l: contents)
         
(* The log has been truncated; but the length (0) is unsynced *)
| Truncated (old: contents)
            
(* The log is being extended; only the content has been updated (unsynced) *)
| Extended (old: contents) (new: contents)
           
(* The log immediately after a crash during an extend, when the new header
  gets synced to disk, but we're not sure what data is there yet. This state
  should be hidden from all higher layers. *)
| ExtendedCrashed (old: contents) (new: contents)
                  
(* A special case of ExtendedCrashed. The data in the log definitely does
  not match the header on disk, so we are guaranteed to roll back to the
  previous length during recovery. *)
| Rollback (old: contents)
           
(* The log during recovery, when the data in the log doesn't match the
  header and we're rolling back to the previous log length. The header we will
  recover to hasn't been synced yet *)
| RollbackUnsync (old: contents)
.

Definition ent_addr (e : entry) := addr2w (fst e).
Definition ent_block (e : entry) := snd e.
Definition ent_tag (e : entry) := fst (snd e).
Definition ent_valu (e : entry) := snd (snd e).

Definition ndesc_log (log : contents) := (divup (length log) DescSig.items_per_val).
Definition ndesc_list T (l : list T) := (divup (length l) DescSig.items_per_val).

Fixpoint log_nonzero (log : contents) : contents :=
  match log with
  | (0, _) :: rest => log_nonzero rest
  | e :: rest => e :: log_nonzero rest
  | nil => nil
  end.

Definition blocks_nonzero (log : contents) := map ent_block (log_nonzero log).
Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).
Definition tags_nonzero (log : contents) := map ent_tag (log_nonzero log).

Fixpoint nonzero_addrs (al : list addr) : nat :=
  match al with
  | 0 :: rest => nonzero_addrs rest
  | e :: rest => S (nonzero_addrs rest)
  | nil => 0
  end.

Fixpoint combine_nonzero (al : list addr) (vl : list tagged_block) : contents :=
  match al, vl with
  | 0 :: al', v :: vl' => combine_nonzero al' vl
  | a :: al', v :: vl' => (a, v) :: (combine_nonzero al' vl')
  | _, _ => nil
  end.

Definition ndata_log (log : contents) := nonzero_addrs (map fst log) .

Definition addr_valid (e : entry) := goodSize addrlen (fst e).

Definition entry_valid (ent : entry) := fst ent <> 0 /\ addr_valid ent.

Definition addr_tags n := repeat Public n.

Definition rep_contents xp (log : contents) : rawpred :=
  ( [[ Forall addr_valid log ]] *
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log log)) (map ent_addr log)) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero log) (vals_nonzero log)) *
    Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
    Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))
  )%pred.

Definition padded_addr (al : list addr) :=
  setlen al (roundup (length al) DescSig.items_per_val) 0.

Definition padded_log (log : contents) :=
  setlen log (roundup (length log) DescSig.items_per_val) (0, tagged_block0).

Definition rep_contents_unmatched xp (old : contents) new_addr new_tag new_valu : rawpred :=
  ( [[ Forall addr_valid old ]] *
    (*[[ Forall addr_valid new ]] **)
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log (padded_log old)))
                                     (map ent_addr (padded_log old))) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced  (addr_tags (ndesc_list new_addr)) new_addr) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero (padded_log old))
                                     (vals_nonzero (padded_log old))) *
    Data.array_rep xp (ndata_log old) (Data.Synced new_tag new_valu) *
    Desc.avail_rep xp (ndesc_log old + ndesc_list new_addr)
                   (LogDescLen xp - (ndesc_log old) - (ndesc_list new_addr)) *
    Data.avail_rep xp (ndata_log old + length new_valu)
                   (LogLen xp - (ndata_log old) - (length new_valu))
  )%pred.

Definition loglen_valid xp ndesc ndata :=
  ndesc <= LogDescLen xp  /\ ndata <= LogLen xp.

Definition loglen_invalid xp ndesc ndata :=
  ndesc > LogDescLen xp \/ ndata > LogLen xp.

Definition checksums_match (l : contents) h hm :=
  hash_list_rep (rev (combine (addr_tags (ndesc_log l))
                              (DescDefs.ipack (map ent_addr l)))) (fst h) hm /\
  hash_list_rep (rev (blocks_nonzero l)) (snd h) hm.

Definition hide_or (P : Prop) := P.
Opaque hide_or.

Definition rep_inner xp (st : state) hm : rawpred :=
  (match st with
   | Synced l =>
     exists prev_len h,
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len,
                             (ndesc_log l, ndata_log l),
                             h)) *
     rep_contents xp l *
     [[ checksums_match l h hm ]]
       
   | Truncated old =>
     exists prev_len h h',
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Unsync ((ndesc_log old, ndata_log old), (0, 0), h')
                            (prev_len, (ndesc_log old, ndata_log old), h)) *
     rep_contents xp old *
     [[ checksums_match old h hm ]] *
     [[ checksums_match nil h' hm ]]
       
   | Extended old new =>
     exists prev_len h h',
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Unsync ((ndesc_log old, ndata_log old),
                             (ndesc_log old + ndesc_log new,
                              ndata_log old + ndata_log new), h')
                            (prev_len, (ndesc_log old, ndata_log old), h)) *
     rep_contents xp old *
     [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                     (ndata_log old + ndata_log new) ]] *
     [[ checksums_match old h hm ]] *
     [[ checksums_match (padded_log old ++ new) h' hm ]] *
     [[ Forall entry_valid new ]]
       
   | ExtendedCrashed old new =>
     exists h synced_addr synced_tag synced_valu ndesc,
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced ((ndesc_log old, ndata_log old),
                             (ndesc_log old + ndesc_log new,
                              ndata_log old + ndata_log new),
                             h)) *
     rep_contents_unmatched xp old synced_addr synced_tag synced_valu *
     [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                     (ndata_log old + ndata_log new) ]] *
     (* Whatever got synced on disk takes up just as many desc blocks as new should've. *)
     [[ length synced_addr = (ndesc * DescSig.items_per_val)%nat ]] *
     [[ ndesc = ndesc_log new ]] *
     [[ length synced_valu = ndata_log new ]] *
     [[ checksums_match (padded_log old ++ new) h hm ]] *
     [[ Forall entry_valid new ]]
       
   | Rollback old =>
     exists synced_addr synced_tag synced_valu h new,
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced ((ndesc_log old, ndata_log old),
                             (ndesc_log old + ndesc_log new,
                              ndata_log old + ndata_log new),
                             h)) *
     rep_contents_unmatched xp old synced_addr synced_tag synced_valu *
     [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                     (ndata_log old + ndata_log new) ]] *
     (* Whatever got synced on disk takes up just as many desc blocks as new should've. *)
     [[ length synced_addr = ((ndesc_log new) * DescSig.items_per_val)%nat ]] *
     [[ length synced_valu = ndata_log new ]] *
     [[ checksums_match (padded_log old ++ new) h hm ]] *
     [[ hide_or (DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr \/
                 vals_nonzero new <> synced_valu) ]] *
     [[ Forall entry_valid new ]]
       
  | RollbackUnsync old =>
    exists synced_addr synced_tag synced_valu h h' new prev_len,
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Unsync (prev_len, (ndesc_log old, ndata_log old), h')
                           ((ndesc_log old, ndata_log old),
                            (ndesc_log old + ndesc_log new,
                             ndata_log old + ndata_log new), h)) *
    rep_contents_unmatched xp old synced_addr synced_tag synced_valu *
    [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                    (ndata_log old + ndata_log new) ]] *
    (* Whatever got synced on disk takes up just as many desc blocks as new should've. *)
    [[ length synced_addr = ((ndesc_log new) * DescSig.items_per_val)%nat ]] *
    [[ length synced_valu = ndata_log new ]] *
    [[ checksums_match old h' hm ]] *
    [[ checksums_match (padded_log old ++ new) h hm ]] *
    [[ hide_or (DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr \/
                vals_nonzero new <> synced_valu) ]] *
    [[ Forall entry_valid new ]]
      
   end)%pred.

Definition xparams_ok xp := 
  DescSig.xparams_ok xp /\ DataSig.xparams_ok xp /\
  (LogLen xp) = DescSig.items_per_val * (LogDescLen xp).

Definition rep xp st hm:=
  ([[ xparams_ok xp ]] * rep_inner xp st hm)%pred.

Definition would_recover' xp l hm :=
  (rep xp (Synced l) hm \/
   rep xp (Rollback l) hm \/
   rep xp (RollbackUnsync l) hm)%pred.

Definition would_recover xp F l hm :=
  (exists cs d bm,
     PermCacheDef.rep cs d bm *
     [[ (F * would_recover' xp l hm)%pred d ]])%pred.


Theorem sync_invariant_rep :
  forall xp st hm,
    sync_invariant (rep xp st hm).
Proof.
  unfold rep, rep_inner, rep_contents, rep_contents_unmatched.
  destruct st; intros; eauto 50.
Qed.

Hint Resolve sync_invariant_rep.

Theorem sync_invariant_would_recover' :
  forall xp l hm,
    sync_invariant (would_recover' xp l hm).
Proof.
  unfold would_recover'; intros; eauto.
Qed.

Theorem sync_invariant_would_recover :
  forall xp F l hm,
    sync_invariant (would_recover xp F l hm).
Proof.
  unfold would_recover; intros; eauto.
Qed.

Hint Resolve sync_invariant_would_recover sync_invariant_would_recover'.
Local Hint Unfold rep rep_inner rep_contents xparams_ok: hoare_unfold.




Definition unseal_all (hl: list handle) :=
  let^ (bl) <- ForN i < length hl
        Blockmem bm
        Ghost [ crash ]
        Loopvar [ tbl ]
        Invariant
           [[ rev (tbl) = map snd (extract_blocks bm (firstn i hl)) ]]
        OnCrash
           crash
        Begin
           tb <- Unseal (selN hl i 0);;
           Ret ^(tb::tbl)
       Rof ^((nil: list block));;
  Ret (rev bl).

Definition avail xp cs :=
  let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, (ndesc, _), _) := nr in
    Ret ^(cs, ((LogLen xp) - ndesc * DescSig.items_per_val)).

  Definition read xp cs :=
    let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, (ndesc, ndata), _) := nr in
    let^ (cs, ahl) <- Desc.read_all xp ndesc cs;;
    abl <- unseal_all ahl;;
                   
    let al := map (@wordToNat addrlen) wal in
    let^ (cs, vl) <- Data.read_all xp ndata cs;;
    Ret ^(cs, combine_nonzero al vl).

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

  Lemma padded_log_idem : forall l,
    padded_log (padded_log l) = padded_log l.
  Proof.
    intros.
    unfold padded_log.
    rewrite setlen_length.
    rewrite roundup_roundup; auto.
    rewrite setlen_exact; auto.
    rewrite setlen_length; auto.
  Qed.

  Lemma padded_log_app : forall l1 l2,
    padded_log (padded_log l1 ++ l2) = padded_log l1 ++ padded_log l2.
  Proof.
    intros.
    unfold padded_log.
    rewrite setlen_app_r.
    f_equal.
    rewrite app_length, setlen_length.
    rewrite roundup_roundup_add; auto.
    f_equal; omega.
    rewrite app_length, setlen_length.
    rewrite roundup_roundup_add; auto.
    omega.
  Qed.

  Ltac solve_checksums :=
  try (match goal with
    | [ |- checksums_match _ _ _ ]
      => unfold checksums_match in *
    end; intuition;
    [
      solve_hash_list_rep;
      try (rewrite map_app;
      erewrite DescDefs.ipack_app;
      try solve [ rewrite map_length, padded_log_length; unfold roundup; eauto ];
      rewrite rev_app_distr)
      | solve_hash_list_rep;
      try rewrite vals_nonzero_app, vals_nonzero_padded_log, rev_app_distr;
      try rewrite padded_log_app, map_app, rev_app_distr
    ];
    repeat match goal with
    | [ H: context[hash_list_rep (_ ++ [])] |- _ ]
      => rewrite app_nil_r in H
    end;
    try rewrite <- desc_ipack_padded in *;
    solve_hash_list_rep).


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
