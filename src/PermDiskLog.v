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
Require Export PermDiskLogHdr PermAsyncRecArray.

Set Implicit Arguments.

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

Fixpoint combine_nonzero_gen (al : list addr) (vl : list handle) :=
  match al, vl with
  | 0 :: al', v :: vl' => combine_nonzero_gen al' vl
  | a :: al', v :: vl' => (a, v) :: (combine_nonzero_gen al' vl')
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
    let wal := fold_left DescDefs.iunpack abl nil in               
    let al := map (@wordToNat addrlen) wal in
    let^ (cs, vl) <- Data.read_all xp ndata cs;;
    Ret ^(cs, (al, vl)).

  (* this is an evil hint *)
  Remove Hints Forall_nil.

  Lemma Forall_True : forall A (l : list A),
    Forall (fun _ : A => True) l.
  Proof.
    intros; rewrite Forall_forall; auto.
  Qed.
  Hint Resolve Forall_True.

  Lemma combine_nonzero_ok : forall l,
    combine_nonzero (map fst l) (blocks_nonzero l) = log_nonzero l.
  Proof.
    unfold blocks_nonzero.
    induction l; intros; simpl; auto.
    destruct a, n; simpl.
    case_eq (map ent_block (log_nonzero l)); intros; simpl.
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
    combine_nonzero (map (@wordToNat _) (map ent_addr (padded_log l))) (blocks_nonzero l) = log_nonzero l.
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

  Lemma tags_nonzero_addrs : forall l,
    length (tags_nonzero l) = nonzero_addrs (map fst l).
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
    Desc.array_rep xp a (Desc.Synced (addr_tags (ndesc_log l)) (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (addr_tags (ndesc_log l)) (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym.
     rewrite  desc_ipack_padded; auto.
     rewrite  <- desc_ipack_padded; auto.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     rewrite <- desc_ipack_padded; auto.
     rewrite <- desc_ipack_padded; auto.
  Qed.

  Lemma desc_padding_unsync_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Unsync (addr_tags (ndesc_log l)) (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (addr_tags (ndesc_log l)) (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H.
     rewrite firstn_oob, map_app in H by auto.
     apply Desc.items_valid_app in H; intuition.
     rewrite desc_ipack_padded; auto.
     rewrite <- desc_ipack_padded; auto.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     rewrite <- desc_ipack_padded; auto.
     rewrite <- desc_ipack_padded; auto.
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

  Lemma tags_nonzero_app : forall a b,
    tags_nonzero (a ++ b) = tags_nonzero a ++ tags_nonzero b.
  Proof.
    unfold tags_nonzero; induction a; intros; simpl; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma log_nonzero_repeat_0 : forall n,
    log_nonzero (repeat (0, tagged_block0) n) = nil.
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

  Lemma tags_nonzero_padded_log : forall l,
    tags_nonzero (padded_log l) = tags_nonzero l.
  Proof.
    unfold tags_nonzero, padded_log, setlen, roundup; simpl.
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
  Hint Extern 0 (okToUnify (PermDiskLogHdr.rep _ _) (PermDiskLogHdr.rep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.array_rep _ _ _) (Desc.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.array_rep _ _ _) (Data.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.avail_rep _ _ _) (Desc.avail_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.avail_rep _ _ _) (Data.avail_rep _ _ _)) => constructor : okToUnify.


  Definition avail_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr                      
    PRE:bm, hm,
      PermCacheDef.rep cs d bm *
      [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET: ^(cs, r)
          PermCacheDef.rep cs d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = (LogLen xp) - roundup (length l) DescSig.items_per_val ]]
    CRASH:bm'', hm_crash, exists cs',
          PermCacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} avail xp cs.
  Proof.
    unfold avail.
    safestep.
    safestep.
    safestep.
    solve_checksums.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    cancel; eauto.
    rewrite <- H1; cancel.
    solve_checksums.
    eauto.
  Qed.


Theorem unseal_all_ok :
    forall hl pr,
    {!< F tbl,
    PERM: pr                      
    PRE:bm, hm,
        F * [[ tbl = extract_blocks bm hl ]] *
        [[ length tbl = length hl ]] *
        [[ forall t, In t (map fst tbl) -> can_access pr t ]]
    POST:bm', hm', RET: r
        F * [[ r = map snd tbl ]]
    CRASH:bm'', hm_crash,
        false_pred (* Can't crash *)              
    >!} unseal_all hl.
  Proof.
    unfold unseal_all; step.
    safestep.
    apply H3.
    apply in_selN with (n:= m).
    rewrite map_length.
    setoid_rewrite H4; auto.
    eassign (selN (map snd (extract_blocks bm hl)) m ($0)).
    erewrite extract_blocks_selN.
    repeat erewrite selN_map.
    rewrite <- surjective_pairing; auto.
    unfold block_mem_subset in *.

    erewrite extract_blocks_subset with (bm:= bm); eauto.
    setoid_rewrite H4; omega.
    setoid_rewrite H4; omega.
    erewrite <- extract_blocks_subset with (bm:= bm); eauto.
    auto.

    step.
    step.
    rewrite H11.
    replace ([(map snd (extract_blocks bm hl)) ⟦ m ⟧]) with
        (map snd [selN (extract_blocks bm hl) m tagged_block0]).
    rewrite <- map_app.
    erewrite <- extract_blocks_subset with (bm:= bm); eauto.
    erewrite extract_blocks_selN_inside; auto.
    rewrite <- extract_blocks_app.
    rewrite <- firstn_S_selN; auto.
    erewrite extract_blocks_subset with (bm:= bm); eauto.

    erewrite extract_blocks_firstn_length; auto.
    erewrite extract_blocks_firstn_length; auto.
    simpl; erewrite selN_map; auto.
    setoid_rewrite H4; omega.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    cancel; eauto.

    step.
    step.
    rewrite H9, firstn_exact.
    erewrite extract_blocks_subset with (bm:= bm); eauto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    eassign (lift_empty(False) (AT:= addr)(AEQ:=addr_eq_dec)(V:=valuset))%pred; cancel.
    Unshelve.
    all: eauto.
    exact tt.
    exact Public.
    exact tagged_block0.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (unseal_all _) _) => apply unseal_all_ok : prog.



  Lemma combine_tags_vals:
    forall l,
      combine (tags_nonzero l) (Data.Defs.ipack (vals_nonzero l)) = blocks_nonzero l.
  Proof.
    induction l; simpl; intuition.
    destruct a, n, t; auto.
    unfold Data.Defs.ipack in *.
    unfold Data.Defs.list_chunk, DataSig.items_per_val in *.
    rewrite divup_1 in *.
    simpl.
    rewrite setlen_inbound; simpl.
    unfold tags_nonzero, blocks_nonzero, vals_nonzero in *; simpl.
    setoid_rewrite IHl.
    unfold ent_tag, ent_valu; simpl.
    admit.
    omega.
  Admitted.

  

  Definition read_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr                      
    PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET: ^(cs, r)
          PermCacheDef.rep cs d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ combine_nonzero (fst r) (extract_blocks bm' (snd r)) = log_nonzero l ]]
    CRASH:bm'', hm_crash, exists cs',
          PermCacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} read xp cs.
  Proof.
    unfold read.
    safestep.

    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    rewrite map_length, padded_log_length.
    auto.
    eassign (addr_tags (ndesc_log l)).
    unfold addr_tags; apply repeat_length.
    auto.
    pred_apply.
    rewrite desc_padding_synced_piff; cancel.
    subst.

    step.
    rewrite H18, H19; auto.
    rewrite H19 in H8.
    apply in_map_fst_exists_snd in H8; cleanup.
    apply in_combine_l in H8.
    unfold addr_tags in H8.
    apply repeat_spec in H8; subst; auto.

    safestep; subst.
    erewrite block_mem_subset_rep; eauto.
    eassign (vals_nonzero l).
    setoid_rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    eassign (tags_nonzero l).
    setoid_rewrite tags_nonzero_addrs; unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    pred_apply; cancel.
    auto.
    
    safestep.
    safestep.
    rewrite desc_padding_synced_piff; cancel.
    solve_checksums.

    subst.
    rewrite H19, H26.
    rewrite map_snd_combine.
    erewrite DescDefs.iunpack_ipack; eauto.

    rewrite combine_tags_vals.
    apply combine_nonzero_padded_wordToNat; auto.
    rewrite map_length.
    rewrite padded_log_length.
    unfold roundup; eauto.
    unfold addr_tags; rewrite repeat_length.
    unfold ndesc_log.
    rewrite Desc.Defs.ipack_length.
    rewrite map_length.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_mul; auto.
    unfold DescSig.items_per_val.
    rewrite valulen_is. cbv; omega.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.

    cancel; eauto.
    rewrite <- H1; cancel.
    rewrite desc_padding_synced_piff; cancel.
    solve_checksums.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.

    rewrite <- H1; cancel.
    solve_checksums.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.

    rewrite <- H1; cancel.
    solve_checksums.
    eexists; repeat (eapply hashmap_subset_trans; eauto).

    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
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


  Definition init xp cs :=
    cs <- PermDiskLogHdr.init xp cs;;
    Ret cs.

  Definition trunc xp cs :=
    let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, current_length, _) := nr in
    h <- Hash default_encoding;; 
    cs <- PermDiskLogHdr.write xp (current_length, (0, 0), (h, h)) cs;;
    cs <- PermDiskLogHdr.sync_now xp cs;;
    Ret cs.

  Local Hint Resolve Forall_nil.


  Definition initrep xp :=
    (exists hdr, LogHeader xp |+> hdr *
     Desc.avail_rep xp 0 (LogDescLen xp) *
     Data.avail_rep xp 0 (LogLen xp))%pred.


  Definition init_ok' :
    forall xp cs pr,
    {< F d,
    PERM: pr   
    PRE:bm, hm,
      PermCacheDef.rep cs d bm *
      [[ (F * initrep xp)%pred d ]] *
      [[ xparams_ok xp /\ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d',
          PermCacheDef.rep cs d' bm' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, any
    >} init xp cs.
  Proof.
    unfold init, initrep.
    prestep; unfold rep, PermDiskLogHdr.LAHdr; safecancel.
    eassign (t,l); cancel.
    auto.
    step.
    step.
    unfold ndesc_log, ndata_log; rewrite divup_0; simpl; cancel.
    repeat rewrite Nat.sub_0_r; cbn; cancel.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil by (auto; omega); cancel.
    solve_checksums; simpl; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    unfold ndesc_log, addr_tags; rewrite divup_0; simpl.
    solve_hash_list_rep; auto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
  Qed.

  Definition init_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr
    PRE:bm, hm,
      PermCacheDef.rep cs d bm *
      [[ (F * arrayS (LogHeader xp) l)%pred d ]] *
      [[ length l = (1 + LogDescLen xp + LogLen xp) /\
         LogDescriptor xp = LogHeader xp + 1 /\
         LogData xp = LogDescriptor xp + LogDescLen xp /\
         xparams_ok xp ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d',
      PermCacheDef.rep cs d' bm' *
      [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, any
    >} init xp cs.
  Proof.
    intros.
    eapply pimpl_ok2. apply init_ok'.
    intros; unfold initrep; safecancel.
    unfold Desc.avail_rep, Data.avail_rep.
    rewrite arrayN_isolate_hd by omega.
    repeat rewrite Nat.add_0_r.
    rewrite arrayN_split with (i := LogDescLen xp).
    rewrite surjective_pairing with (p := selN l 0 valuset0).
    substl (LogData xp); substl (LogDescriptor xp).
    cancel.
    eassign F; cancel.
    rewrite firstn_length_l; auto.
    setoid_rewrite skipn_length with (n := 1); omega.
    setoid_rewrite skipn_skipn with (m := 1).
    rewrite skipn_length; omega.
    auto.
    step.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (init _ _) _) => apply init_ok : prog.

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

  Lemma helper_trunc_ok : forall xp l prev_len h,
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log l)) (map ent_addr l)) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero l) (vals_nonzero l)) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len, (0, 0), h))
    =p=>
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len, (ndesc_log [], ndata_log []), h)) *
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log [])) []) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero []) (vals_nonzero [])) *
    Desc.avail_rep xp (ndesc_log []) (LogDescLen xp - ndesc_log []) *
    Data.avail_rep xp (ndata_log []) (LogLen xp - ndata_log []).
  Proof.
    intros.
    unfold ndesc_log, tags_nonzero, vals_nonzero; simpl; rewrite divup_0.
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


  (* XXX:
    Ideally XCRASH can contain only Truncated state, whose crash_xform 
    covers the Synced state's crash_xform. However, to prove that, we need 
    to construct a raw disk that satisifies the Truncated state given a raw
    disk of Synced state.  This involves reverse engineering Hdr.rep.
  *)
  Definition trunc_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr                       
    PRE:bm, hm,
     PermCacheDef.rep cs d bm *
     [[ (F * rep xp (Synced l) hm)%pred d ]] *
     [[ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d',
     PermCacheDef.rep cs d' bm' *
     [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, exists cs' d',
     PermCacheDef.rep cs' d' bm'' * (
       [[ (F * (rep xp (Synced l) hm_crash))%pred d' ]] \/
       [[ (F * (rep xp (Truncated l) hm_crash))%pred d' ]] )
    >} trunc xp cs.
  Proof.
    unfold trunc.
    step.
    step.
    step.

    unfold PermDiskLogHdr.rep in H0.
    destruct_lift H0.
    unfold hdr_goodSize in *; intuition.

    step.
    step.
    step.

    (* post condition *)
    cancel_by helper_trunc_ok.
    solve_checksums.
    replace (DescDefs.ipack (map ent_addr [])) with (@nil valu).
    unfold ndesc_log, addr_tags; rewrite divup_0; simpl.
    solve_hash_list_rep; auto.
    symmetry. apply DescDefs.ipack_nil.
    auto.
    eexists; repeat (eapply hashmap_subset_trans; eauto).

    (* crash conditions *)
    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.
    
    xform_norm. cancel. xform_normr; cancel.
    eassign cs'; eassign d'; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    unfold ndesc_log, addr_tags; rewrite divup_0; simpl.
    solve_hash_list_rep; auto.

    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.
    repeat xcrash_rewrite.
    xform_norm; cancel. xform_normr; cancel.
    eassign x; eassign x0; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    unfold ndesc_log, addr_tags; rewrite divup_0; simpl.
    solve_hash_list_rep; auto.

    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).     
    xform_normr; cancel.
    eassign cs'; eassign d; cancel.
    or_l; cancel.
    solve_checksums.

    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.



  Theorem loglen_valid_dec xp ndesc ndata :
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
    apply (H (0, t)); simpl; auto.
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

  Lemma log_nonzero_rev_comm : forall l,
    log_nonzero (rev l) = rev (log_nonzero l).
  Proof.
    induction l; simpl; intros; auto.
    destruct a, n; simpl; auto;
    rewrite log_nonzero_app; simpl.
    rewrite app_nil_r. congruence.
    congruence.
  Qed.

  Lemma entry_valid_vals_nonzero : forall l,
    Forall entry_valid l ->
    log_nonzero l = l.
  Proof.
    unfold entry_valid; induction l; simpl; auto.
    destruct a, n; simpl; auto; intros.
    exfalso.
    rewrite Forall_forall in H; intuition.
    apply (H (0, t)); simpl; auto.
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
    apply (H (0, t)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma desc_ipack_injective : forall l1 l2 n1 n2,
    length l1 = n1 * DescSig.items_per_val ->
    length l2 = n2 * DescSig.items_per_val ->
    DescDefs.ipack l1 = DescDefs.ipack l2 ->
    l1 = l2.
  Proof.
    intros.
    erewrite <- DescDefs.iunpack_ipack; eauto.
    erewrite <- DescDefs.iunpack_ipack at 1; eauto.
    congruence.
  Qed.

  Lemma ndesc_log_ndesc_list : forall l,
    ndesc_log l = ndesc_list (map ent_addr (padded_log l)).
  Proof.
    unfold ndesc_log, ndesc_list.
    intros.
    autorewrite with lists.
    rewrite padded_log_length.
    unfold roundup.
    rewrite divup_divup; auto.
  Qed.

  Lemma addr_tags_app:
    forall n m,
      addr_tags (n + m) = addr_tags n ++ addr_tags m.
  Proof.
    induction n; simpl; intros; auto.
    unfold addr_tags in *; simpl; auto.
    rewrite IHn; auto.
  Qed.
  
  Lemma extend_ok_helper : forall F xp old new,
    Forall entry_valid new ->
    Data.array_rep xp (ndata_log old) (Data.Synced (map ent_tag new) (map ent_valu new)) *
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log old)) (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero old) (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new) *
    Data.avail_rep xp (ndata_log old + divup (length (map ent_valu new)) DataSig.items_per_val)
      (LogLen xp - ndata_log old - ndata_log new) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced (addr_tags (ndesc_log new)) (map ent_addr (padded_log new))) * F
    =p=>
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log (padded_log old ++ new))) (map ent_addr (padded_log old ++ new))) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero (padded_log old ++ new)) (vals_nonzero (padded_log old ++ new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ new)) 
                      (LogDescLen xp - ndesc_log (padded_log old ++ new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ new))
                      (LogLen xp - ndata_log (padded_log old ++ new)) * F.
  Proof.
    intros.
    repeat rewrite ndesc_log_padded_app, ndata_log_padded_app.
    setoid_rewrite Nat.sub_add_distr.
    (* unfold ndesc_log. *)
    rewrite divup_1.
    rewrite entry_valid_ndata with (l := new); auto.
    repeat rewrite map_length.
    rewrite map_app, vals_nonzero_app.
    rewrite addr_tags_app.
    rewrite <- Desc.array_rep_synced_app.
    rewrite tags_nonzero_app.
    rewrite <- Data.array_rep_synced_app.
    repeat rewrite Nat.add_0_l.
    repeat rewrite desc_padding_synced_piff.
    repeat rewrite map_length.
    repeat rewrite vals_nonzero_padded_log, tags_nonzero_padded_log.
    repeat rewrite divup_1, padded_log_length.
    unfold roundup; rewrite divup_mul; auto.
    unfold ndata_log; rewrite vals_nonzero_addrs.
    unfold tags_nonzero, vals_nonzero; rewrite entry_valid_vals_nonzero with (l := new); auto.
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

  Lemma extend_ok_synced_hdr_helper : forall xp prev_len old new h,
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len,
                            (ndesc_log old + ndesc_log new,
                             ndata_log old + ndata_log new),
                            h))
    =p=>
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len,
                            (ndesc_log (padded_log old ++ new),
                             ndata_log (padded_log old ++ new)),
                            h)).
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




(* Need to add If statement and alighned functions *)

  

  Definition extend xp log cs :=
    (* Synced *)
    let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, (ndesc, ndata), (h_addr, h_valu)) := nr in
    let '(nndesc, nndata) := ((ndesc_log log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
      h_addr <- hash_list h_addr (DescDefs.nopad_ipack (map ent_addr log));
      h_valu <- hash_list h_valu (vals_nonzero log);
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;
      cs <- Hdr.write xp ((ndesc, ndata),
                          (ndesc + nndesc, ndata + nndata),
                          (h_addr, h_valu)) cs;
      (* Extended *)
      cs <- BUFCACHE.begin_sync cs;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;
      cs <- Data.sync_aligned xp ndata nndata cs;
      cs <- Hdr.sync xp cs;
      cs <- BUFCACHE.end_sync cs;
      (* Synced *)
      Ret ^(cs, true)
    } else {
      Ret ^(cs, false)
    }.

  Lemma rep_hashmap_subset : forall xp hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st hm
        =p=> rep xp st hm'.
  Proof.
    intros.
    destruct st; unfold rep, rep_inner; cancel; solve_checksums.
    auto.
  Qed.

  Lemma would_recover'_hashmap_subset : forall xp l hm hm',
    (exists l, hashmap_subset l hm hm') ->
    would_recover' xp l hm
    =p=> would_recover' xp l hm'.
  Proof.
    unfold would_recover'.
    intros.
    cancel;
    rewrite rep_hashmap_subset; auto; cancel.
  Qed.

  Definition extend_ok : forall xp new cs,
    {< F old d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced old) hm)%pred d ]] *
          [[ Forall entry_valid new /\ sync_invariant F ]]
    POST:hm' RET: ^(cs, r) exists d',
          BUFCACHE.rep cs d' * (
          [[ r = true /\
             (F * rep xp (Synced ((padded_log old) ++ new)) hm')%pred d' ]] \/
          [[ r = false /\ length ((padded_log old) ++ new) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:hm_crash exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Synced old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (Extended old new) hm_crash)%pred d' ]])
    >} extend xp new cs.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      rewrite <- DescDefs.ipack_nopad_ipack_eq.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.

      safestep.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      safestep.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.

      (* write header *)
      safestep.
      denote Hdr.rep as Hx; unfold Hdr.rep in Hx.
      destruct_lift Hx.
      unfold Hdr.hdr_goodSize in *; intuition.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      (* sync content *)
      step.
      eauto 10.
      prestep. norm. cancel. intuition simpl.
      instantiate ( 1 := map ent_addr (padded_log new) ).
      rewrite desc_padding_unsync_piff.
      pred_apply; cancel.
      rewrite map_length, padded_log_length; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      eauto 10.

      safestep.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      eauto 10.

      (* sync header *)
      safestep.
      eauto 10.
      step.

      (* post condition *)
      safestep.
      or_l; cancel.
      cancel_by extend_ok_helper; auto.
      solve_checksums.

      (* crash conditons *)
      (* after sync data : Extended *)
      cancel.
      repeat xcrash_rewrite.
      xform_norm. cancel. xform_normr. cancel.
      or_r. cancel.
      extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.


      (* before writes *)
      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_l; cancel. extend_crash.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_l; cancel.
      rewrite Desc.avail_rep_merge. cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.
      solve_checksums.

      xcrash.
      or_l; cancel.
      solve_checksums.

      xcrash.
      or_l; cancel.
      solve_checksums.

    (* false case *)
    - safestep.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.
      solve_checksums.

    (* crash for the false case *)
    - xcrash.
      or_l; cancel.
      solve_checksums.
  Qed.


  Hint Extern 1 ({{_}} Bind (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} Bind (extend _ _ _) _) => apply extend_ok : prog.
