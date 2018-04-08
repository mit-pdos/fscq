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

Require Export PermDiskLogHdr.

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

Definition generic_entry {B} := (addr * B)%type.
Definition generic_contents {B} := list (@generic_entry B).
Definition entry := @generic_entry tagged_block.
Definition contents := @generic_contents block.
Definition input_entry := @generic_entry handle.
Definition input_contents := @generic_contents handle.

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

Definition ent_addr {B} (e : @generic_entry B) := addr2w (fst e).
Definition ent_handle {A} (e : A * handle) := snd e.
Definition ent_valu {A} (e : A *  valu) := snd e.

Definition ndesc_log {T} (log : @generic_contents T) := (divup (length log) DescSig.items_per_val).
Definition ndesc_list {T} (l : list T) := (divup (length l) DescSig.items_per_val).

Fixpoint log_nonzero {T} (log : @generic_contents T) :=
  match log with
  | (0, _) :: rest => log_nonzero rest
  | e :: rest => e :: log_nonzero rest
  | nil => nil
  end.

Definition handles_nonzero (log : input_contents) := map ent_handle (log_nonzero log).
Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).

Fixpoint nonzero_addrs (al : list addr) : nat :=
  match al with
  | 0 :: rest => nonzero_addrs rest
  | e :: rest => S (nonzero_addrs rest)
  | nil => 0
  end.

Fixpoint combine_nonzero {B} (al : list addr) (vl : list B) : @generic_contents B :=
  match al, vl with
  | 0 :: al', v :: vl' => combine_nonzero al' vl
  | a :: al', v :: vl' => (a, v) :: (combine_nonzero al' vl')
  | _, _ => nil
  end.

Definition ndata_log {B} (log : @generic_contents B) := nonzero_addrs (map fst log) .

Definition addr_valid {B} (e : @generic_entry B) := goodSize addrlen (fst e).

Definition entry_valid {B} (ent : @generic_entry B) := fst ent <> 0 /\ addr_valid ent.

Definition rep_contents xp (log : contents) : rawpred :=
  ( [[ Forall addr_valid log ]] *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr log)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero log)) *
    Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
    Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))              
  )%pred.

Definition padded_addr (al : list addr) :=
  setlen al (roundup (length al) DescSig.items_per_val) 0.

Definition padded_log_gen {T} def (log : @generic_contents T) :=
  setlen log (roundup (length log) DescSig.items_per_val) (0, def).

Definition padded_log (log : contents) := padded_log_gen $0 log.

Definition rep_contents_unmatched xp (old : contents) new_addr new_valu : rawpred :=
  ( [[ Forall addr_valid old ]] *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old))) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced new_addr) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old))) *
    Data.array_rep xp (ndata_log old) (Data.Synced new_valu) *
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
  hash_list_rep (rev (DescDefs.ipack (map ent_addr l))) (fst h) hm /\
  hash_list_rep (rev (vals_nonzero l)) (snd h) hm.

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
     exists h synced_addr synced_valu ndesc,
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced ((ndesc_log old, ndata_log old),
                             (ndesc_log old + ndesc_log new,
                              ndata_log old + ndata_log new),
                             h)) *
     rep_contents_unmatched xp old synced_addr synced_valu *
     [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                     (ndata_log old + ndata_log new) ]] *
     (* Whatever got synced on disk takes up just as many desc blocks as new should've. *)
     [[ length synced_addr = (ndesc * DescSig.items_per_val)%nat ]] *
     [[ ndesc = ndesc_log new ]] *
     [[ length synced_valu = ndata_log new ]] *
     [[ checksums_match (padded_log old ++ new) h hm ]] *
     [[ Forall entry_valid new ]]
       
   | Rollback old =>
     exists synced_addr synced_valu h new,
     PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced ((ndesc_log old, ndata_log old),
                             (ndesc_log old + ndesc_log new,
                              ndata_log old + ndata_log new),
                             h)) *
     rep_contents_unmatched xp old synced_addr synced_valu *
     [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                     (ndata_log old + ndata_log new) ]] *
     (* Whatever got synced on disk takes up just as many desc blocks as new should've. *)
     [[ length synced_addr = ((ndesc_log new) * DescSig.items_per_val)%nat ]] *
     [[ length synced_valu = ndata_log new ]] *
     [[ checksums_match (padded_log old ++ new) h hm ]] *
     [[ hide_or (vals_nonzero new <> synced_valu \/
                 DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr) ]] *
     [[ Forall entry_valid new ]]
       
  | RollbackUnsync old =>
    exists synced_addr synced_valu h h' new prev_len,
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Unsync (prev_len, (ndesc_log old, ndata_log old), h')
                           ((ndesc_log old, ndata_log old),
                            (ndesc_log old + ndesc_log new,
                             ndata_log old + ndata_log new), h)) *
    rep_contents_unmatched xp old synced_addr synced_valu *
    [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                    (ndata_log old + ndata_log new) ]] *
    (* Whatever got synced on disk takes up just as many desc blocks as new should've. *)
    [[ length synced_addr = ((ndesc_log new) * DescSig.items_per_val)%nat ]] *
    [[ length synced_valu = ndata_log new ]] *
    [[ checksums_match old h' hm ]] *
    [[ checksums_match (padded_log old ++ new) h hm ]] *
    [[  hide_or (vals_nonzero new <> synced_valu \/
                 DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr) ]] *
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

Definition would_recover xp F l bm hm :=
  (exists cs d,
     PermCacheDef.rep cs d bm *
     [[ (F * would_recover' xp l hm)%pred d ]])%pred.


Definition avail xp cs :=
  let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
  let '(_, (ndesc, _), _) := nr in
  Ret ^(cs, ((LogLen xp) - ndesc * DescSig.items_per_val)).

Definition read xp cs :=
  let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
  let '(_, (ndesc, ndata), _) := nr in
  let^ (cs, wal) <- Desc.read_all xp ndesc cs;;              
  let al := map (@wordToNat addrlen) wal in
  let^ (cs, vl) <- Data.read_all xp ndata cs;;
  Ret ^(cs, (combine_nonzero al vl)).


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
  forall xp F l bm hm,
    sync_invariant (would_recover xp F l bm hm).
Proof.
  unfold would_recover; intros; eauto.
Qed.

Hint Resolve sync_invariant_would_recover sync_invariant_would_recover'.
Local Hint Unfold rep rep_inner rep_contents xparams_ok: hoare_unfold.


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

  Lemma combine_nonzero_nil : forall a T,
    combine_nonzero a (nil: list T) = nil.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.
  Local Hint Resolve combine_nonzero_nil.

  Lemma combine_nonzero_app_zero : forall T a (b: list T),
    combine_nonzero (a ++ [0]) b = combine_nonzero a b.
  Proof.
    induction a; intros; simpl; auto.
    destruct b; auto.
    destruct a, b; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma combine_nonzero_app_zeros : forall T n a (b: list T),
    combine_nonzero (a ++ repeat 0 n) b = combine_nonzero a b.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply combine_nonzero_app_zero.
  Qed.

  Local Hint Resolve roundup_ge DescDefs.items_per_val_gt_0.

  Lemma combine_nonzero_padded_addr : forall T a (b: list T),
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

  Lemma map_entaddr_repeat_0 : forall T n (b: T),
    map ent_addr (repeat (0, b) n) = repeat $0 n.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.

  Lemma combine_nonzero_padded_log : forall T A (l: @generic_contents A) (def: A) (b: list T),
    combine_nonzero (map fst (padded_log_gen def l)) b = combine_nonzero (map fst l) b.
  Proof.
    unfold padded_log_gen, setlen, roundup; intros.
    induction l; simpl.
    rewrite divup_0; simpl; auto.
    
    rewrite <- IHl.
    destruct a, b, n; simpl; auto;
    repeat rewrite firstn_oob; simpl; auto;
    repeat rewrite map_app;
    setoid_rewrite map_fst_repeat;
    repeat rewrite combine_nonzero_app_zeros; auto.
  Qed.

  Lemma addr_valid_padded : forall T (l: @generic_contents T) def,
    Forall addr_valid l -> Forall addr_valid (padded_log_gen def l).
  Proof.
    unfold padded_log_gen, setlen, roundup; intros.
    rewrite firstn_oob; simpl; auto.
    apply Forall_append; auto.
    rewrite Forall_forall; intros.
    apply repeat_spec in H0; subst.
    unfold addr_valid; simpl.
    apply zero_lt_pow2.
  Qed.

  Lemma padded_addr_valid : forall T (l: @generic_contents T) def,
    Forall addr_valid (padded_log_gen def l) ->
    Forall addr_valid l.
  Proof.
    unfold padded_log_gen, setlen; intros.
    rewrite firstn_oob in H; auto.
    eapply forall_app_r; eauto.
  Qed.

  Local Hint Resolve addr_valid_padded padded_addr_valid.

  Lemma map_wordToNat_ent_addr : forall T (l: @generic_contents T),
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
    erewrite <- combine_nonzero_padded_log.
    f_equal.
    unfold padded_log; rewrite map_wordToNat_ent_addr; eauto.
  Qed.

  Lemma vals_nonzero_addrs : forall l,
    length (vals_nonzero l) = nonzero_addrs (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.

  Lemma log_nonzero_addrs : forall T (l: @generic_contents T),
    length (log_nonzero l) = nonzero_addrs (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.

  Lemma desc_ipack_padded : forall T (l: @generic_contents T) def,
    DescDefs.ipack (map ent_addr l) = DescDefs.ipack (map ent_addr (padded_log_gen def l)).
  Proof.
    unfold padded_log_gen, setlen; intros.
    rewrite firstn_oob, map_app, map_entaddr_repeat_0 by auto.
    rewrite DescDefs.ipack_app_item0; auto.
    rewrite map_length; auto.
  Qed.


  Local Hint Resolve combine_nonzero_padded_wordToNat.
  
Lemma desc_padding_synced_piff : forall xp a T (l: @generic_contents T) def,
    Desc.array_rep xp a (Desc.Synced (map ent_addr (padded_log_gen def l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log_gen, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym.
     erewrite  desc_ipack_padded; eauto.
     unfold padded_log_gen, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     rewrite <- desc_ipack_padded; auto.
  Qed.

  Lemma desc_padding_unsync_piff : forall xp a T (l: @generic_contents T) def,
    Desc.array_rep xp a (Desc.Unsync (map ent_addr (padded_log_gen def l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log_gen, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     rewrite <- desc_ipack_padded; auto.

     unfold padded_log_gen, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     rewrite <- desc_ipack_padded; auto.
  Qed.

  Lemma goodSize_ndesc : forall T (l: @generic_contents T),
    goodSize addrlen (length l) -> goodSize addrlen (ndesc_log l).
  Proof.
    intros; unfold ndesc_log.
    eapply goodSize_trans; [ apply divup_le | eauto ].
    destruct (mult_O_le (length l) DescSig.items_per_val); auto.
    contradict H0; apply DescDefs.items_per_val_not_0.
  Qed.
  Local Hint Resolve goodSize_ndesc.

  Lemma padded_log_length: forall T (l: @generic_contents T) def,
    length (padded_log_gen def l) = roundup (length l) DescSig.items_per_val.
  Proof.
    unfold padded_log_gen, roundup; intros.
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

  Lemma nonzero_addrs_padded_log : forall T (l: @generic_contents T) def,
    nonzero_addrs (map fst (padded_log_gen def l)) = nonzero_addrs (map fst l).
  Proof.
    unfold padded_log_gen; induction l; simpl; intros; auto.
    rewrite setlen_nil, repeat_is_nil; simpl; auto.
    unfold roundup; rewrite divup_0; omega.
    
    destruct a, n; simpl;
    erewrite <- IHl;
    unfold setlen, roundup;
    repeat rewrite firstn_oob, map_app by auto;
    setoid_rewrite map_fst_repeat;
    repeat rewrite nonzero_addrs_app_zeros; simpl; auto.
    Unshelve.
    all: auto.
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
    log_nonzero (repeat (0, natToWord valulen 0) n) = nil.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma log_nonzero_app : forall T (a b: @generic_contents T),
    log_nonzero (a ++ b) = log_nonzero a ++ log_nonzero b.
  Proof.
    induction a; simpl; intros; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma vals_nonzero_padded_log : forall l,
    vals_nonzero (padded_log l) = vals_nonzero l.
  Proof.
    unfold vals_nonzero, padded_log, padded_log_gen, setlen, roundup; simpl.
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


  Lemma nonzero_addrs_length : forall l,
    nonzero_addrs l <= length l.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl; auto; omega.
  Qed.

  Lemma ndata_log_goodSize : forall T (l: @generic_contents T),
    goodSize addrlen (length l) -> goodSize addrlen (ndata_log l).
  Proof.
    unfold ndata_log; induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
    apply IHl.
    simpl in *; eapply goodSize_trans.
    2: eauto.
    omega.
    simpl in *.
    eapply goodSize_trans.
    2: eauto.
    pose proof nonzero_addrs_length (map fst l);
    repeat rewrite map_length in *.
    apply le_n_S; auto.
  Qed.
  Local Hint Resolve ndata_log_goodSize.

  Lemma padded_log_idem : forall T (l: @generic_contents T) def1 def2,
    padded_log_gen def2 (padded_log_gen def1 l) = padded_log_gen def1 l.
  Proof.
    intros.
    unfold padded_log_gen.
    rewrite setlen_length.
    rewrite roundup_roundup; auto.
    rewrite setlen_exact; auto.
    rewrite setlen_length; auto.
  Qed.

  Lemma padded_log_app : forall T (l1 l2: @generic_contents T) def1 def2,
    padded_log_gen def2 (padded_log_gen def1 l1 ++ l2) = padded_log_gen def1 l1 ++ padded_log_gen def2 l2.
  Proof.
    intros.
    unfold padded_log_gen.
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

  (** Lemmas **)
   Lemma block2val_noop:
    forall a,
      Data.Defs.block2val [a] = a.
  Proof.  
    intros.
    unfold Data.Defs.block2val, Rec.to_word; simpl.
    unfold Word.combine.
    rewrite combine_n_0.
    unfold Data.Defs.word2val, eq_rec_r, DataSig.itemtype; simpl.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    erewrite <- Eqdep.EqdepTheory.eq_rect_eq; auto.
  Qed.

  
    Lemma ipack_noop:
    forall l,
      Data.Defs.ipack l = l.
  Proof.
    induction l; simpl; intros; auto.
    unfold Data.Defs.ipack, Data.Defs.list_chunk,
    DataSig.items_per_val in *.
    rewrite divup_1 in *; simpl.
    rewrite setlen_inbound; try (simpl; omega).
    simpl.
    setoid_rewrite IHl.
    rewrite block2val_noop; auto.
  Qed.

Hint Unfold padded_log.

Lemma map_snd_combine_le:
  forall A B (lb: list B) (la: list A),
    length la >= length lb ->
    map snd (combine la lb) = lb.
Proof.
  induction lb; simpl; intros; auto.
  rewrite combine_l_nil; simpl; auto.
  destruct la; simpl in *; try omega.
  rewrite IHlb; eauto; omega.
Qed.

Lemma map_fst_combine_le:
  forall A B (la: list A) (lb: list B),
    length lb >= length la ->
    map fst (combine la lb) = la.
Proof.
  induction la; simpl; intros; auto.
  destruct lb; simpl in *; try omega.
  rewrite IHla; eauto; omega.
Qed.

Lemma map_fst_combine_le_firstn:
  forall A B (la: list A) (lb: list B),
    length la >= length lb ->
    map fst (combine la lb) = firstn (length lb) la.
Proof.
  induction la; simpl; intros; auto.
  rewrite firstn_nil; auto.
  destruct lb; simpl in *; try omega; auto.
  rewrite IHla; eauto; omega.
Qed.


Lemma map_snd_combine_nonzero:
  forall A al (l: list A),
    nonzero_addrs al >= length l ->
    map snd (combine_nonzero al l) = l.
Proof.
  induction al; simpl; intros; auto.
  destruct l; simpl in *; auto; omega.
  destruct a;
  destruct l; simpl in *; auto.
  rewrite IHal; auto; omega.
Qed.

Lemma nonzero_addrs_maps:
  forall l,
    Forall addr_valid l ->
    nonzero_addrs
      (map (wordToNat (sz:=addrlen))
           (map ent_addr (padded_log l))) =
    nonzero_addrs (map fst l).
Proof.
  induction l; simpl; intros; auto;
  unfold padded_log, padded_log_gen in *; simpl.
  rewrite setlen_nil, map_entaddr_repeat_0, repeat_map;
  simpl; rewrite roundup_0; simpl; auto.

  inversion H; subst.
  rewrite setlen_oob, map_app, map_app in *.
  rewrite map_entaddr_repeat_0, repeat_map in *; simpl repeat in *.
  rewrite nonzero_addrs_app_zeros in *.
  destruct a, n; simpl; auto.
  unfold ent_addr at 1; simpl.
  unfold addr2w; simpl.
  
  rewrite wordToNat_natToWord_idempotent'.
  rewrite IHl; auto.
  unfold addr_valid in *; auto.
  
  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.
  
  simpl; unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.

  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.
Qed.


Lemma combine_nonzero_extract_blocks_comm:
  forall al hl bm,
    handles_valid bm hl ->
    nonzero_addrs al >= length hl ->
    extract_blocks bm (map snd (combine_nonzero al hl)) =
    map snd (combine_nonzero al (extract_blocks bm hl)).
Proof.
  induction al; simpl; intros; auto.
  destruct hl; try destruct n; auto.
  destruct a; simpl in *; auto.
  destruct a; simpl in *; auto.
  {
    inversion H; subst.
    unfold handle_valid in *; cleanup.
    rewrite IHal; simpl; auto.
    cleanup; auto.
  }
  {
    inversion H; subst.
    unfold handle_valid in *; cleanup; simpl in *.
    rewrite IHal; simpl; auto; omega.
  }
Qed.

(*
Lemma combine_nonzero_log_nonzero:
  forall A l (hl: list A),
    Forall addr_valid l ->
    length (log_nonzero l) = length hl ->
    combine (map fst (combine_nonzero
            (map (wordToNat (sz:=addrlen))
                 (map ent_addr (padded_log l))) hl))
            (blocks_nonzero l) = log_nonzero l.
Proof.
  induction l; simpl; intros; auto.
  unfold blocks_nonzero; simpl;
  apply combine_l_nil.

  destruct a, n; simpl in *.
  unfold blocks_nonzero in *; simpl in *.
  unfold padded_log, padded_log_gen in *; simpl.

  inversion H; subst.
  rewrite setlen_oob, map_app, map_app in *.
  rewrite map_entaddr_repeat_0, repeat_map in *; simpl repeat in *.
  erewrite <- IHl at 2; eauto.
  repeat rewrite combine_nonzero_app_zeros in *; simpl.
  destruct hl; simpl.
  rewrite combine_nonzero_nil; simpl; auto.
  auto.
  
  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.

  simpl; unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.
  
  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.

  unfold blocks_nonzero in *; simpl in *.
  unfold padded_log, padded_log_gen in *; simpl.

  inversion H; subst.
  rewrite setlen_oob, map_app, map_app in *.
  rewrite map_entaddr_repeat_0, repeat_map in *; simpl repeat in *.
  simpl (map _ (_::_)); unfold ent_addr in *; simpl fst.
  destruct hl; simpl in *.
  omega.

  unfold addr2w; simpl.
  rewrite wordToNat_natToWord_idempotent'.
  simpl.
  erewrite <- IHl at 2; auto.
  repeat rewrite combine_nonzero_app_zeros in *; eauto.
  omega.
  unfold addr_valid in *; auto.

  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.

  simpl; unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.
  
  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.
Qed.
*)

Lemma in_combine_nonzero:
  forall A al (l: list A) x,
    In x (combine_nonzero al l) ->
    fst x <> 0.
Proof.
  induction al; simpl; intros; auto.
  destruct a;
  destruct l; eauto.
  inversion H; subst; simpl; eauto.
Qed.

Lemma in_combine_nonzero_not_0:
  forall A al (l: list A) x,
    In x (combine_nonzero al l) ->
    In (fst x) al.
Proof.
  induction al; simpl; intros; auto.
  destruct a, l; intuition.
  right; eauto.
  inversion H; subst; simpl; eauto.
Qed.

Lemma entry_valid_combine_nonzero:
  forall A l (hl: list A),
    Forall addr_valid l ->
    Forall entry_valid (combine_nonzero
                          (map (wordToNat (sz:=addrlen)) (map ent_addr (padded_log l))) hl).
Proof.
  intros; rewrite Forall_forall; intros.
  unfold entry_valid; split.
  eapply in_combine_nonzero; eauto.

  unfold padded_log, padded_log_gen in *; simpl. 
  rewrite setlen_oob, map_app, map_app in *.
  rewrite map_entaddr_repeat_0, repeat_map in *; simpl repeat in *.
  repeat rewrite combine_nonzero_app_zeros in *; simpl.
  rewrite map_wordToNat_ent_addr in *; auto.

  apply in_combine_nonzero_not_0 in H0.
  unfold addr_valid in *.
  apply Forall_map in H.
  rewrite Forall_forall in H; apply H; auto.

  unfold roundup; apply divup_n_mul_n_le.
  unfold DescSig.items_per_val.
  rewrite valulen_is. cbv; omega.
Qed.

  Lemma goodSize_0 : forall sz, goodSize sz 0.
  Proof.
    unfold goodSize; intros.
    apply zero_lt_pow2.
  Qed.

  Lemma ndesc_log_nil : forall T, ndesc_log (nil: @generic_contents T) = 0.
  Proof.
    unfold ndesc_log; simpl.
    rewrite divup_0; auto.
  Qed.

  Lemma ndata_log_nil : forall T, ndata_log (nil: @generic_contents T) = 0.
  Proof.
    unfold ndata_log; simpl; auto.
  Qed.


  Definition initrep xp :=
    (exists hdr, LogHeader xp |+> hdr *
            Desc.avail_rep xp 0 (LogDescLen xp) *
            Data.avail_rep xp 0 (LogLen xp))%pred.


  
  Theorem loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.
  Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec (LogDescLen xp) ndesc);
    destruct (lt_dec (LogLen xp) ndata); simpl; auto.
    left; intuition.
  Defined.

  Definition entry_valid_ndata : forall T (l: @generic_contents T),
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

  Lemma loglen_valid_desc_valid : forall TO TN xp (old: @ generic_contents TO) (new: @generic_contents TN),
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


  Lemma loglen_valid_data_valid :forall T xp (old: @generic_contents T) (new: @generic_contents valu),
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

  Lemma helper_loglen_desc_valid_extend : forall TO TN xp (old: @ generic_contents TO) (new: @generic_contents TN),
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndesc_log new + (LogDescLen xp - ndesc_log old - ndesc_log new) 
      = LogDescLen xp - ndesc_log old.
  Proof.
    unfold loglen_valid, ndesc_log; intros.
    omega.
  Qed.

  Lemma helper_loglen_data_valid_extend : forall TO TN xp (old: @ generic_contents TO) (new: @generic_contents TN),
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndata_log new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
  Proof.
    unfold loglen_valid, ndata_log; intros.
    omega.
  Qed.

  Lemma helper_loglen_data_valid_extend_entry_valid : forall TO TN xp (old: @ generic_contents TO) (new: @generic_contents TN),
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
  Proof.
    intros.
    rewrite <- entry_valid_ndata by auto.
    apply helper_loglen_data_valid_extend; auto.
  Qed.

  Lemma padded_desc_valid : forall xp st T (l: @generic_contents T) def,
    Desc.items_valid xp st (map ent_addr l)
    -> Desc.items_valid xp st (map ent_addr (padded_log_gen def l)).
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

  Lemma ent_valid_addr_valid : forall T (l: @generic_contents T),
    Forall entry_valid l -> Forall addr_valid l.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    apply H; auto.
  Qed.

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

  Lemma ndata_log_app : forall T (a b: @generic_contents T),
    ndata_log (a ++ b) = ndata_log a + ndata_log b.
  Proof.
    unfold ndata_log;  intros.
    repeat rewrite map_app.
    rewrite nonzero_addrs_app; auto.
  Qed.

  Lemma ndesc_log_padded_log : forall T (l: @generic_contents T) def,
    ndesc_log (padded_log_gen def l) = ndesc_log l.
  Proof.
    unfold ndesc_log; intros.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_divup; auto.
  Qed.

  Local Hint Resolve DescDefs.items_per_val_not_0.

  Lemma ndesc_log_app : forall T (a b: @generic_contents T),
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

  Lemma ndesc_log_padded_app : forall T (a b: @generic_contents T) def,
    ndesc_log (padded_log_gen def a ++ b) = ndesc_log a + ndesc_log b.
  Proof.
    intros.
    rewrite ndesc_log_app.
    rewrite ndesc_log_padded_log; auto.
    rewrite padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.

  Lemma ndata_log_padded_log : forall T (a: @generic_contents T) def,
    ndata_log (padded_log_gen def a) = ndata_log a.
  Proof.
    unfold ndata_log, padded_log_gen, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    repeat rewrite map_app.
    rewrite repeat_map; simpl.
    rewrite nonzero_addrs_app.
    setoid_rewrite <- app_nil_l at 3.
    rewrite nonzero_addrs_app_zeros; auto.
  Qed.


  Lemma ndata_log_padded_app : forall T (a b: @generic_contents T) def,
    ndata_log (padded_log_gen def a ++ b) = ndata_log a + ndata_log b.
  Proof.
    intros.
    rewrite ndata_log_app.
    rewrite ndata_log_padded_log; auto.
  Qed.

  Lemma log_nonzero_rev_comm : forall T (l: @generic_contents T),
    log_nonzero (rev l) = rev (log_nonzero l).
  Proof.
    induction l; simpl; intros; auto.
    destruct a, n; simpl; auto;
    rewrite log_nonzero_app; simpl.
    rewrite app_nil_r. congruence.
    congruence.
  Qed.

  Lemma entry_valid_vals_nonzero : forall T (l: @generic_contents T),
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

  Lemma nonzero_addrs_entry_valid : forall T (l: @generic_contents T),
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

  Lemma ndesc_log_ndesc_list : forall T (l: @generic_contents T) def,
    ndesc_log l = ndesc_list (map ent_addr (padded_log_gen def l)).
  Proof.
    unfold ndesc_log, ndesc_list.
    intros.
    autorewrite with lists.
    rewrite padded_log_length.
    unfold roundup.
    rewrite divup_divup; auto.
  Qed.

    Lemma nonzero_addrs_bound : forall l,
    nonzero_addrs l <= length l.
  Proof.
    induction l; simpl; auto.
    destruct a; omega.
  Qed.

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

  Lemma loglen_invalid_overflow : forall xp T (old new: @generic_contents T) def,
    LogLen xp = DescSig.items_per_val * LogDescLen xp ->
    loglen_invalid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length (padded_log_gen def old ++ new) > LogLen xp.
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

    Lemma log_nonzero_padded_log : forall l,
    log_nonzero (padded_log l) = log_nonzero l.
  Proof.
    unfold padded_log, padded_log_gen, setlen, roundup; intros.
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

    Lemma rep_hashmap_subset : forall xp hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st hm
        =p=> rep xp st hm'.
  Proof.
    intros.
    destruct st; unfold rep, rep_inner;
    cancel; solve_checksums.
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
    rewrite rep_hashmap_subset; auto; try solve_hashmap_subset; cancel.
  Qed.

  Lemma length_map_fst_extract_blocks_eq:
    forall A bm (new: list (A * handle)),
      handles_valid bm (map ent_handle new) ->
      length (map fst new) = length (extract_blocks bm (map ent_handle new)).
  Proof.
    intros.      
    rewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
  Qed.

  Lemma ndesc_log_combine_eq:
    forall bm new,
      handles_valid bm (map ent_handle new) ->
      ndesc_log (combine (map fst new)
                         (extract_blocks bm (map ent_handle new))) =
      ndesc_list new.
  Proof.
    intros.
    unfold ndesc_log, ndesc_list.
    setoid_rewrite combine_length_eq; rewrite map_length; auto.
    rewrite extract_blocks_length; auto.
    rewrite map_length; auto.
  Qed.
      
  Lemma ndata_log_combine_eq:
    forall bm new,
      handles_valid bm (map ent_handle new) ->
      ndata_log (combine (map fst new)
                         (extract_blocks bm (map ent_handle new))) =
      ndata_log new.
  Proof.
    unfold ndata_log; intros.
    rewrite map_fst_combine; auto.
    rewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
  Qed.


  Lemma map_ent_addr_combine_eq:
  forall bm new,
    handles_valid bm (map ent_handle new) ->
    map ent_addr (combine (map fst new) (extract_blocks bm (map ent_handle new))) = map ent_addr new.
Proof.
  unfold ent_addr; intros.
  rewrite <- map_map at 1.
  setoid_rewrite map_fst_combine.
  apply map_map.
  apply length_map_fst_extract_blocks_eq; auto.
Qed.

Lemma Forall_entry_valid_combine:
  forall bm new,
    Forall entry_valid new ->
    Forall entry_valid (combine (map fst new) (extract_blocks bm (map ent_handle new))).
Proof.
  intros;
  unfold entry_valid, addr_valid in *; apply Forall_forall; intros.
  destruct x; simpl.
  apply in_combine_l in H0; simpl.
  eapply in_map_fst_exists_snd in H0; cleanup.
  eapply Forall_forall in H; simpl in *; eauto.
  simpl in *; auto.
Qed.

(*
Lemma vals_nonzero_combine_entry_valid:
  forall bm new,
    Forall entry_valid new ->
    handles_valid bm (map ent_handle new) ->
    vals_nonzero (combine (map fst new) (extract_blocks bm (map ent_handle new)))
    = map ent_valu (combine (map fst new) (extract_blocks bm (map ent_handle new))).
Proof.
  induction new; simpl; intros; auto.
  unfold handles_valid, handle_valid in *.
  inversion H0; subst.
  cleanup.
  unfold vals_nonzero in *; simpl.
  unfold entry_valid in *; inversion H; subst.
  destruct (fst a); intuition; simpl.
  rewrite H7; auto.
Qed.
*)
Lemma combine_eq_r:
    forall A B (l: list A) (l1 l2: list B),
      combine l l1 = combine l l2 ->
      length l = length l2 ->
      length l1 = length l2 ->
      l1 = l2.
  Proof.
    induction l; simpl; intros;
    destruct l1, l2; simpl in *; try congruence.
    inversion H; subst; erewrite (IHl l1 l2); eauto.
  Qed.
(*
  Lemma rep_contents_unmatched_tag_length:
      forall xp old atags addrs tags valus,
        rep_contents_unmatched xp old addrs valus =p=>
    [[ length atags = ndesc_list addrs ]] *
    rep_contents_unmatched xp old atags addrs tags valus.
    Proof.
      unfold rep_contents_unmatched, ndesc_list; intros.
      unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, eqlen.
      repeat rewrite Desc.Defs.ipack_length; cancel.
    Qed.
*)
    Lemma combine_eq_r2:
      forall A B (lx ly: list A) (l1 l2: list B),
        combine lx l1 = combine ly l2 ->
        length lx = length l2 ->
        length lx = length ly ->
        length l1 = length l2 ->
        l1 = l2.
    Proof.
      induction lx; simpl; intros;
      destruct ly, l1, l2; simpl in *; try congruence.
      inversion H; subst; erewrite (IHlx ly l1 l2); eauto.
    Qed.

    Lemma combine_eq_l2:
      forall A B (lx ly: list A) (l1 l2: list B),
        combine lx l1 = combine ly l2 ->
        length lx = length l2 ->
        length lx = length ly ->
        length l1 = length l2 ->
        lx = ly.
    Proof.
      induction lx; simpl; intros;
      destruct ly, l1, l2; simpl in *; try congruence.
      inversion H; subst; erewrite (IHlx ly l1 l2); eauto.
    Qed.
      
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

  
  Lemma helper_trunc_ok : forall T xp l prev_len h,
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr l)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero l)) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len, (0, 0), h))
    =p=>
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len, (@ndesc_log T [], @ndata_log T []), h)) *
    Desc.array_rep xp 0 (Desc.Synced []) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero [])) *
    Desc.avail_rep xp (@ndesc_log T []) (LogDescLen xp - @ndesc_log T []) *
    Data.avail_rep xp (@ndata_log T []) (LogLen xp - @ndata_log T []).
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
(** Specs **)

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
    solve_hashmap_subset.
    cancel.
    rewrite <- H1; cancel.
    solve_checksums.
    eauto.
  Qed.


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
          [[ r = log_nonzero l ]] *
          [[ Forall entry_valid r ]]
    CRASH:bm'', hm_crash, exists cs',
          PermCacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} read xp cs.
  Proof.
    unfold read, extract_blocks_list, handles_valid_list.
    safestep.

    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    rewrite map_length; unfold padded_log; rewrite padded_log_length.
    auto.
    rewrite Forall_forall; intros; auto.
    pred_apply.
    unfold padded_log; rewrite desc_padding_synced_piff; cancel.
    subst.

    safestep; subst.
    setoid_rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    
    safestep.
    safestep.
    unfold padded_log; rewrite desc_padding_synced_piff; cancel.
    solve_checksums.

    subst.
    apply entry_valid_combine_nonzero; eauto.
    solve_hashmap_subset.
    solve_blockmem_subset.

    cancel; eauto.
    rewrite <- H1; cancel.
    unfold padded_log; rewrite desc_padding_synced_piff; cancel.
    solve_checksums.
    solve_hashmap_subset.
    solve_blockmem_subset.

    rewrite <- H1; cancel.
    solve_checksums.
    solve_hashmap_subset.
    solve_blockmem_subset.

    rewrite <- H1; cancel.
    solve_checksums.
    solve_hashmap_subset.

    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Local Hint Resolve goodSize_0.


  Definition init xp cs :=
    cs <- PermDiskLogHdr.init xp cs;;
    Ret cs.

  Definition trunc xp cs :=
    let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, current_length, _) := nr in
    h <- Hash default_valu;; 
    cs <- PermDiskLogHdr.write xp (current_length, (0, 0), (h, h)) cs;;
    cs <- PermDiskLogHdr.sync_now xp cs;;
    Ret cs.

  Local Hint Resolve Forall_nil.


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
    eassign (dummy_cur, dummy_old); cancel.
    auto.
    step.
    step.
    unfold ndesc_log, ndata_log; rewrite divup_0; simpl; cancel.
    repeat rewrite Nat.sub_0_r; cbn; cancel.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil by (auto; omega); cancel.
    solve_checksums; simpl; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    solve_hash_list_rep; auto.
    solve_hashmap_subset.
  Qed.

  (** There is a problem in here because we don't know the underlying tags 
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
   **)
  
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
    unfold ndesc_log; simpl.
    solve_hash_list_rep; auto.
    symmetry. apply DescDefs.ipack_nil.
    solve_hash_list_rep; auto.
    solve_hashmap_subset.

    (* crash conditions *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    xform_norm. cancel. xform_normr; cancel.
    eassign cs'; eassign d'; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    unfold ndesc_log; simpl.
    solve_hash_list_rep; auto.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    repeat xcrash_rewrite.
    xform_norm; cancel. xform_normr; cancel.
    eassign x; eassign x0; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    unfold ndesc_log; simpl.
    solve_hash_list_rep; auto.

    rewrite <- H1; cancel.
    solve_hashmap_subset.    
    xform_normr; cancel.
    eassign cs'; eassign d; cancel.
    or_l; cancel.
    solve_checksums.

    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Remove Hints goodSize_0.

  Local Hint Resolve ent_valid_addr_valid.
  Local Hint Resolve Forall_append.

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
    intros. unfold padded_log.
    repeat rewrite ndesc_log_padded_app, ndata_log_padded_app.
    setoid_rewrite Nat.sub_add_distr.
    (* unfold ndesc_log. *)
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
    repeat rewrite divup_1, padded_log_length.
    unfold roundup; rewrite divup_mul; auto.
    unfold ndata_log; repeat rewrite vals_nonzero_addrs.
    unfold vals_nonzero;
    repeat setoid_rewrite entry_valid_vals_nonzero with (l:= new); auto.
    repeat setoid_rewrite nonzero_addrs_entry_valid with (l:= new); auto; cancel.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.

  Lemma extend_ok_synced_hdr_helper : forall xp prev_len T (old new: @generic_contents T) def h,
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len,
                            (ndesc_log old + ndesc_log new,
                             ndata_log old + ndata_log new),
                            h))
    =p=>
    PermDiskLogHdr.rep xp (PermDiskLogHdr.Synced (prev_len,
                            (ndesc_log (padded_log_gen def old ++ new),
                             ndata_log (padded_log_gen def old ++ new)),
                            h)).
  Proof.
    intros.
    rewrite ndesc_log_padded_app, ndata_log_padded_app; auto.
  Qed.
 
  
  Local Hint Resolve extend_ok_synced_hdr_helper.
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



(* I am doing something ugly in here. Type of the input 'log' has type list (addr * handle)
   and blocks of the "real log" is sitting in the block memory *)
Definition extend xp (log: contents) cs :=
    (* Synced *)
    let^ (cs, nr) <- PermDiskLogHdr.read xp cs;;
    let '(_, (ndesc, ndata), (h_addr, h_valu)) := nr in
    let '(nndesc, nndata) := ((ndesc_list log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
      h_addr <- hash_list h_addr (DescDefs.ipack (map ent_addr log));;
      h_valu <- hash_list h_valu (map ent_valu log);;
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;;
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;;
      cs <- PermDiskLogHdr.write xp ((ndesc, ndata),
                          (ndesc + nndesc, ndata + nndata),
                          (h_addr, h_valu)) cs;;
      (* Extended *)
      cs <- PermCacheDef.begin_sync cs;;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;;
      cs <- Data.sync_aligned xp ndata nndata cs;;
      cs <- PermDiskLogHdr.sync xp cs;;
      cs <- PermCacheDef.end_sync cs;;
      (* Synced *)
      Ret ^(cs, true)
    } else {
      Ret ^(cs, false)
    }.


  Hint Extern 1 ({{_|_}} Bind (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (trunc _ _) _) => apply trunc_ok : prog.

Lemma vals_nonzero_map_ent_valu:
  forall l,
    Forall entry_valid l ->
    map ent_valu l = vals_nonzero l.
Proof.
  induction l; intros; simpl.
  unfold vals_nonzero; simpl; auto.
  unfold vals_nonzero in *; simpl; auto.
  inversion H; subst.
  unfold entry_valid  in H2; cleanup.
  destruct a; simpl in *.
  destruct n; simpl in *; try congruence.
  rewrite IHl; auto.
Qed.

      
Lemma extend_crash_helper:
  forall xp (old: contents) new,
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ((Data.array_rep xp (ndata_log old) (Data.Unsync (map ent_valu new))
    ✶ Desc.array_rep xp (ndesc_log old) (Desc.Unsync (map ent_addr new)))
   ✶ Data.avail_rep xp
       (ndata_log old + divup (length (map ent_valu new)) DataSig.items_per_val)
       (LogLen xp - ndata_log old - ndata_log new))
  ✶ Desc.avail_rep xp
      (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new)
    =p=> Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old) *
        Data.avail_rep xp (ndata_log old) (LogLen xp - ndata_log old).
Proof.
  intros.
  rewrite Desc.array_rep_avail, Data.array_rep_avail.
  unfold Data.nr_blocks, Desc.nr_blocks.
  rewrite helper_sep_star_reorder.
  rewrite  Desc.avail_rep_merge, Data.avail_rep_merge.
  cancel.
  
  rewrite divup_1.
  rewrite map_length.
  apply helper_loglen_data_valid_extend_entry_valid; auto.
  rewrite map_length.
  apply helper_loglen_desc_valid_extend; auto.
Qed.


Lemma extend_crash_helper_synced:
  forall xp (old: contents) new,
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ((Data.avail_rep xp (ndata_log old)
      (divup (length (map ent_valu new)) DataSig.items_per_val)
    ✶ Desc.array_rep xp (ndesc_log old) (Desc.Unsync (map ent_addr new)))
   ✶ Data.avail_rep xp
       (ndata_log old + divup (length (map ent_valu new)) DataSig.items_per_val)
       (LogLen xp - ndata_log old - ndata_log new))
  ✶ Desc.avail_rep xp
      (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new)
    =p=> Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old) *
        Data.avail_rep xp (ndata_log old) (LogLen xp - ndata_log old).
Proof.
  intros.
  rewrite Desc.array_rep_avail.
  unfold Data.nr_blocks, Desc.nr_blocks.
  rewrite helper_sep_star_reorder.
  rewrite  Desc.avail_rep_merge, Data.avail_rep_merge.
  cancel.
  
  rewrite divup_1.
  rewrite map_length.
  apply helper_loglen_data_valid_extend_entry_valid; auto.
  rewrite map_length.
  apply helper_loglen_desc_valid_extend; auto.
Qed.

 Definition extend_ok :
    forall xp (new: contents) cs pr,
    {< F old d,
    PERM:pr   
    PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * rep xp (Synced old) hm)%pred d ]] *
          [[ Forall entry_valid new /\ sync_invariant F ]]
    POST:bm', hm', RET: ^(cs, r) exists d',
          PermCacheDef.rep cs d' bm' * 
          ([[ r = true /\
              (F * rep xp (Synced ((padded_log old) ++ new)) hm')%pred d' ]] \/
           [[ r = false /\ length ((padded_log old) ++ new) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:bm'', hm_crash, exists cs' d',
          PermCacheDef.rep cs' d' bm'' *
          ([[ (F * rep xp (Synced old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (Extended old new) hm_crash)%pred d' ]])
    >} extend xp new cs.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      (* rewrite <- DescDefs.ipack_nopad_ipack_eq. *)
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.

      safestep.
      eassign F_.
      erewrite block_mem_subset_rep.
      cancel.
      solve_blockmem_subset.
      pred_apply.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.
      auto.
      
      safestep; eauto.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.
      
      (* write header *)
      safestep.
      denote PermDiskLogHdr.rep as Hx; unfold PermDiskLogHdr.rep in Hx.
      destruct_lift Hx.
      unfold PermDiskLogHdr.hdr_goodSize in *; intuition.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      (* sync content *)
      step.
      eauto 10.
      prestep. norm. eassign F_; cancel. intuition simpl.
      

      rewrite desc_padding_unsync_piff.       
      pred_apply; cancel.
      exact default_valu.
      rewrite map_length; auto.
      rewrite padded_log_length.
      unfold ndesc_list, roundup; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      eauto 10.

      safestep.
      eassign F_; cancel.
      pred_apply; cancel.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      eapply loglen_valid_data_valid; auto.
      eauto 10.
      auto.

      (* sync header *)
      safestep.
      eassign F_; cancel.
      pred_apply; cancel.
      eauto 10.
      auto.
      
      safestep.
      eassign F_; cancel.
      auto.

      (* post condition *)
      safestep.
      safestep.
      or_l.
      repeat rewrite ndesc_log_app.
      repeat rewrite ndata_log_app.      
      cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      
      unfold padded_log;
      repeat rewrite ndesc_log_padded_log, ndata_log_padded_log.
      repeat rewrite vals_nonzero_app, map_app; auto.
      rewrite <- Desc.array_rep_synced_app; simpl; auto.
  
      repeat (erewrite <- extract_blocks_subset_trans; eauto).
      repeat rewrite map_length.
      repeat setoid_rewrite combine_length_eq; auto.
      repeat rewrite vals_nonzero_padded_log.
      repeat rewrite tags_nonzero_padded_log.
      repeat rewrite padded_log_length.
      unfold roundup; repeat rewrite divup_mul.
      repeat rewrite map_length.
      cancel.
      repeat rewrite desc_padding_synced_piff.
      cancel.
      rewrite <- Data.array_rep_synced_app; simpl.
      repeat rewrite Nat.sub_add_distr.
      repeat rewrite map_ent_addr_combine_eq.
      setoid_rewrite (entry_valid_ndata (l:=new)); auto.
      rewrite divup_1.
      unfold ndesc_log; cancel.

      
      rewrite vals_nonzero_addrs, divup_1.
      unfold ndata_log; auto.
      auto.     
      rewrite vals_nonzero_map_ent_valu; auto.      
      symmetry; apply Nat.mul_1_r.

      apply Desc.Defs.items_per_val_not_0.
      rewrite map_length, padded_log_length; unfold roundup; eauto.
      
      apply Forall_append; auto.
      apply addr_valid_padded; auto.

      solve_checksums; simpl.
      erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.
      unfold padded_log; rewrite padded_log_length;
      unfold roundup; rewrite divup_mul; auto.
      
      solve_hashmap_subset.
      solve_blockmem_subset.

      
      (* crash conditons *)
      (* after sync data : Extended *)
      (* Crash 1 *)
      cancel.

      (* Crash 2 *)
      rewrite <- H1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_r; cancel.
      cancel.
      apply extend_crash_helper; auto.
      solve_checksums.
      solve_checksums; simpl.
       erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.
      solve_hashmap_subset.
      solve_blockmem_subset.

      (* Crash 3 *)
      rewrite <- H1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_r; cancel.
      cancel.
      
      apply extend_crash_helper; auto.
      solve_checksums.
      solve_checksums; simpl.
      erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.
      solve_hashmap_subset.
      solve_blockmem_subset.

      (* Crash 4 *)
      rewrite <- H1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_r; cancel.
      cancel.
      
      apply extend_crash_helper; auto.
      solve_checksums.
      solve_checksums; simpl.
      erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.
      solve_hashmap_subset.
      solve_blockmem_subset.

      
      (* Crash 5 *)
      rewrite <- H1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_r; cancel.
      cancel.
      
      apply extend_crash_helper; auto.
      solve_checksums.
      solve_checksums; simpl.
      erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).


      (* Crash 6 *)
      rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign cs'; eassign d'1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_r; cancel.
      cancel.
      
      apply extend_crash_helper; auto.
      solve_checksums.
      solve_checksums; simpl.
      erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).


      (* Crash 7 *)
      destruct_lift H17; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign x0; eassign x1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_r; cancel.
      cancel.
      
      apply extend_crash_helper; auto.
      solve_checksums.
      solve_checksums; simpl.
      erewrite map_app, DescDefs.ipack_app.
      rewrite rev_app_distr.
      unfold padded_log; rewrite <- desc_ipack_padded.
      solve_hash_list_rep.
      unfold padded_log; rewrite map_length, padded_log_length.
      unfold roundup; eauto.
      rewrite <- vals_nonzero_map_ent_valu; auto.
      solve_hash_list_rep.

      (* before writes *)
      (* Crash 8 *)
      unfold pimpl; intros mx Hx;
      destruct_lift Hx; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign x0; eassign x1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      apply extend_crash_helper_synced; auto.
      solve_checksums.

      (* Crash 9 *)
      unfold pimpl; intros mx Hx;
      destruct_lift Hx; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign x0; eassign x1; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.

      rewrite  Desc.avail_rep_merge.
      cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.
      solve_checksums.

    (* false case *)
    - safestep.
      safestep.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.
      solve_checksums.
      solve_hashmap_subset.
      cancel.
      
    (* crash for the false case *)
    - rewrite <- H1; cancel.
      solve_hashmap_subset.
      xcrash.
      eassign cs'; eassign d; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      solve_checksums.
      Unshelve.
      all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (extend _ _ _) _) => apply extend_ok : prog.

  
Theorem entry_valid_dec : forall B (ent: addr * B),
                            {entry_valid ent} + {~ entry_valid ent}.
Proof.
  unfold entry_valid, addr_valid, goodSize; intuition.
  destruct (addr_eq_dec (fst (a,b)) 0); destruct (lt_dec (fst (a,b)) (pow2 addrlen)).
  right; tauto.
  right; tauto.
  left; tauto.
  right; tauto.
Defined.

Theorem rep_synced_length_ok : forall F xp l d hm,
                                 (F * rep xp (Synced l) hm)%pred d -> length l <= LogLen xp.
Proof.
  unfold rep, rep_inner, rep_contents, xparams_ok.
  unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
  intros; destruct_lifts.
  rewrite map_length, Nat.sub_0_r in H17.
  rewrite H5, Nat.mul_comm; auto.
Qed.

Lemma xform_rep_synced : forall xp l hm,
                           crash_xform (rep xp (Synced l) hm) =p=> rep xp (Synced l) hm.
Proof.
  unfold rep; simpl; unfold rep_contents; intros.
  xform.
  norm'l. unfold stars; cbn.
  xform.
  norm'l. unfold stars; cbn.
  xform.
  rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
  rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
  rewrite PermDiskLogHdr.xform_rep_synced.
  cancel.
Qed.

Lemma xform_rep_truncated : forall xp l hm,
                              crash_xform (rep xp (Truncated l) hm) =p=>
rep xp (Synced l) hm \/ rep xp (Synced nil) hm.
Proof.
  unfold rep; simpl; unfold rep_contents; intros.
  xform; cancel.
  xform; cancel.
  rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
  rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
  rewrite PermDiskLogHdr.xform_rep_unsync.
  norm; auto.

  or_r; cancel.
  cancel_by helper_trunc_ok.
  auto.
  or_l; cancel.
Qed.

Lemma xform_rep_extendedcrashed :
  forall xp old new hm,
    crash_xform (rep xp (ExtendedCrashed old new) hm) =p=> rep xp (ExtendedCrashed old new) hm.
Proof.
  unfold rep; simpl; unfold rep_contents_unmatched; intros.
  do 6 (xform;
        norm'l; unfold stars; cbn).
  xform.
  rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
  rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
  rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
  rewrite PermDiskLogHdr.xform_rep_synced.
  cancel.
  congruence.
Qed.

Theorem rep_extended_facts' :
  forall xp d old new hm,
    (rep xp (Extended old new) hm)%pred d ->
    Forall entry_valid new /\
    LogLen xp >= ndata_log old + ndata_log new /\
    LogDescLen xp >= ndesc_log old + ndesc_log new.
Proof.
  unfold rep, rep_inner, rep_contents, xparams_ok.
  unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
  intros; destruct_lifts.
  intuition.
  unfold loglen_valid in *; intuition.
  unfold loglen_valid in *; intuition.
Qed.

Theorem rep_extended_facts :
  forall xp old new hm,
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

Lemma helper_sep_star_distr:
  forall AT AEQ V (a b c d : @pred AT AEQ V),
    a * b * c * d =p=> (c * a) * (d * b).
Proof.
  intros; cancel.
Qed.

Lemma helper_add_sub_add :
  forall a b c,
    b >= c + a -> a + (b - (c + a)) = b - c.
Proof.
  intros; omega.
Qed.

  Lemma xform_rep_extended_helper :
    forall B xp old (new: @generic_contents B),
    xparams_ok xp
    -> LogLen xp >= ndata_log old + ndata_log new
    -> LogDescLen xp >= ndesc_log old + ndesc_log new
    -> Forall addr_valid old
    -> Forall entry_valid new
    -> crash_xform
    (Desc.array_rep xp 0
       (Desc.Synced (map ent_addr old)))
  ✶ (crash_xform
       (Data.array_rep xp 0 (Data.Synced (vals_nonzero old)))
     ✶ (crash_xform
          (Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old))
        ✶ crash_xform
            (Data.avail_rep xp (ndata_log old) (LogLen xp - ndata_log old))))
      =p=> exists synced_addr synced_valu ndesc,
        rep_contents_unmatched xp old synced_addr synced_valu *
        [[ length synced_addr = (ndesc * DescSig.items_per_val)%nat ]] *
        [[ ndesc = ndesc_log new ]] *
        [[ length synced_valu = ndata_log new ]].
  Proof.
    intros.
    rewrite Data.avail_rep_split with (n1:=ndata_log new).
    rewrite Desc.avail_rep_split with (n1:=ndesc_log new).
    xform.
    erewrite Data.xform_avail_rep_array_rep, Desc.xform_avail_rep_array_rep.
    norml. unfold stars; simpl.
    norm.
    unfold stars; simpl.
    cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    unfold rep_contents_unmatched, padded_log.
    rewrite vals_nonzero_padded_log.
    cancel.
    repeat rewrite ndesc_log_padded_log.
    replace (ndesc_list _) with (ndesc_log new).
    rewrite <- desc_padding_synced_piff.
    cancel.
 
    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
    unfold ndesc_list.
    substl (length l0).
    rewrite Nat.mul_1_r; cancel.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
    unfold ndesc_list.
    substl (length l).
    rewrite divup_mul; auto.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
    intuition; auto.
    all: unfold DescSig.RALen, DataSig.RALen, xparams_ok in *;
          try omega; auto; intuition.

    apply mult_le_compat_r; omega.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
  Qed.

Lemma sep_star_pimpl_trans :
  forall AT AEQ V (F p q r: @pred AT AEQ V),
    p =p=> q ->
    F * q =p=> r ->
    F * p =p=> r.
Proof.
  intros.
  cancel; auto.
Qed.

  Lemma xform_rep_extended' : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (ExtendedCrashed old new) hm.
  Proof.
    intros; rewrite rep_extended_facts.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    xform; cancel.
    rewrite PermDiskLogHdr.xform_rep_unsync; cancel.

    - or_r.
      repeat rewrite sep_star_assoc.
      eapply sep_star_pimpl_trans.
      eapply pimpl_trans.
      2: apply xform_rep_extended_helper; try eassumption.
      cancel.
      cancel.
      subst; auto.

    - or_l.
      cancel.
      rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
      rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
      cancel.
  Qed.
  
  Lemma rep_synced_app_pimpl : forall xp old new hm,
    rep xp (Synced (padded_log old ++ new)) hm =p=>
    rep xp (Synced (padded_log old ++ padded_log new)) hm.
  Proof.
    unfold rep; simpl; intros; unfold rep_contents, padded_log; cancel.
    repeat rewrite ndesc_log_padded_app.
    repeat rewrite ndata_log_padded_app.
    rewrite ndesc_log_padded_log, ndata_log_padded_log.
    setoid_rewrite map_app.
    setoid_rewrite vals_nonzero_app.
    setoid_rewrite vals_nonzero_padded_log.
    cancel.
    
    erewrite Desc.array_rep_synced_app_rev.
    erewrite <- Desc.array_rep_synced_app with (a:=map ent_addr (padded_log_gen $ (0) old)) (b:=map ent_addr (padded_log_gen $ (0) new)).
    cancel.
    erewrite desc_padding_synced_piff; eauto.
    
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite map_length, padded_log_length; unfold roundup; eauto.

    apply Forall_append.
    eapply forall_app_r; eauto.
    apply addr_valid_padded; auto.
    eapply forall_app_l; eauto.
    solve_checksums.
    erewrite map_app, DescDefs.ipack_app in *.
    repeat rewrite <- desc_ipack_padded in *.
    rewrite <- rev_app_distr; auto.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite vals_nonzero_app in *.
    rewrite vals_nonzero_padded_log in *;
    unfold padded_log in *; eauto.
    rewrite <- rev_app_distr; auto.
  Qed.


Lemma combine_eq:
  forall A B (l l': list A) (x x': list B),
    length l = length l' ->
    length x = length x' ->
    length l = length x ->
    combine l x = combine l' x' ->
    l = l' /\ x = x'.
Proof.
  induction l; simpl; intros.
  symmetry in H; apply length_zero_iff_nil in H;
  symmetry in H1; apply length_zero_iff_nil in H1;
  subst; symmetry in H0; apply length_zero_iff_nil in H0;
  subst; auto.
  destruct l', x , x'; simpl in *; auto; try congruence.
  inversion H2; subst.
  edestruct IHl; [| | | eauto |].
  all: eauto.
  subst; eauto.
Qed.

  
  Lemma rep_extendedcrashed_pimpl : forall xp old new hm,
    rep xp (ExtendedCrashed old new) hm
    =p=> rep xp (Synced ((padded_log old) ++ new)) hm \/
          rep xp (Rollback old) hm.
  Proof.
    intros.
    unfold rep at 1, rep_inner; simpl.
    norm'l. unfold stars; simpl.
    destruct (list_eq_dec (@weq valulen) (DescDefs.ipack
             (map ent_addr (padded_log new))) (DescDefs.ipack synced_addr)).
    destruct (list_eq_dec (@weq valulen) (vals_nonzero new) synced_valu).

    - eapply desc_ipack_injective in e.
      unfold rep, rep_inner, rep_contents_unmatched, rep_contents.
      or_l; cancel.
      rewrite map_app.
      rewrite vals_nonzero_app.
      rewrite vals_nonzero_padded_log.
      rewrite <- Data.array_rep_synced_app.
      replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
      rewrite divup_1; simpl.
      repeat rewrite vals_nonzero_addrs.
      unfold padded_log.
      rewrite ndata_log_app, ndata_log_padded_log.
      rewrite Nat.sub_add_distr.
      cancel.

      rewrite ndesc_log_app,
      <- Desc.array_rep_synced_app.
      simpl.
      replace (divup _ _) with (ndesc_log old).
      rewrite ndesc_log_padded_log.
      rewrite Nat.sub_add_distr.
      replace (ndesc_list _) with (ndesc_log new).
      cancel.
      rewrite desc_padding_synced_piff.
      cancel.

      erewrite ndesc_log_ndesc_list; auto.
      rewrite map_length, padded_log_length.
      unfold roundup.
      rewrite divup_divup; auto.
      autorewrite with lists.
      rewrite padded_log_length.
      unfold roundup.
      eauto.
      rewrite padded_log_length.
      unfold roundup.
      rewrite divup_divup; auto.
      replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
      rewrite Nat.mul_1_r; eauto.
      unfold padded_log.
      apply Forall_append; auto.
      auto.
      
      autorewrite with lists.
      unfold padded_log; rewrite padded_log_length.
      unfold roundup; eauto.
      eauto.

    - unfold rep, rep_inner.
      unfold pimpl; intros m Hm;
      pose proof Hm as Hx;
      pred_apply.
      or_r; cancel.
      left; auto.

    - unfold rep, rep_inner.
      unfold pimpl; intros m Hm;
      pose proof Hm as Hx;
      pred_apply.
      or_r; cancel.
      right; auto.
  Qed.

 
  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (Synced (padded_log old ++ new)) hm \/
       rep xp (Rollback old) hm.
  Proof.
    intros.
    rewrite xform_rep_extended'.
    rewrite rep_extendedcrashed_pimpl.
    auto.
  Qed.
  
  Lemma xform_rep_rollback : forall xp old hm,
    crash_xform (rep xp (Rollback old) hm) =p=>
      rep xp (Rollback old) hm.
  Proof.
    unfold rep; simpl; unfold rep_contents_unmatched; intros.
    do 6 (xform; norm'l; unfold stars; simpl).
    xform.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    repeat rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite PermDiskLogHdr.xform_rep_synced.
    cancel.
  Qed.

  Lemma recover_desc_avail_helper : forall B T xp (old: @generic_contents B) (new : list T) ndata,
    loglen_valid xp (ndesc_log old + ndesc_list new) ndata ->
    (Desc.avail_rep xp (ndesc_log old) (ndesc_list new)
     * Desc.avail_rep xp (ndesc_log old + ndesc_list new)
         (LogDescLen xp - ndesc_log old - ndesc_list new))
    =p=> Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old).
  Proof.
    intros.
    rewrite Desc.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    omega.
  Qed.

  Lemma recover_data_avail_helper : forall B T xp (old: @generic_contents B) (new : list T) ndesc,
    loglen_valid xp ndesc (ndata_log old + length new) ->
    Data.avail_rep xp (ndata_log old)
          (divup (length new) DataSig.items_per_val)
    * Data.avail_rep xp (ndata_log old + length new)
        (LogLen xp - ndata_log old - length new)
    =p=> Data.avail_rep xp (nonzero_addrs (map fst old))
           (LogLen xp - nonzero_addrs (map fst old)).
  Proof.
    intros.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite divup_1, Data.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    omega.
  Qed.

  Lemma xform_rep_rollbackunsync : forall xp l hm,
    crash_xform (rep xp (RollbackUnsync l) hm) =p=>
      rep xp (Rollback l) hm \/
      rep xp (Synced l) hm.
  Proof.
    unfold rep; simpl; unfold rep_contents_unmatched; intros.
    do 9 (xform; norm'l; unfold stars; simpl).
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    repeat rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite PermDiskLogHdr.xform_rep_unsync.
    cancel.

    unfold rep_contents.
    or_r.
    unfold padded_log.
    rewrite desc_padding_synced_piff,
    vals_nonzero_padded_log.
    cancel.
    rewrite Desc.array_rep_avail_synced, Data.array_rep_avail_synced.
    rewrite <- recover_desc_avail_helper.
    setoid_rewrite <- recover_data_avail_helper.
    cancel.
    denote (length _ = ndata_log _) as Hndata.
    rewrite Hndata; eauto.
    denote (length _ = _ * _) as Hndesc.
    unfold ndesc_list.
    rewrite Hndesc, divup_mul; eauto.

    Unshelve.
    all: eauto.
  Qed.


  Lemma xform_would_recover' : forall xp l hm,
    crash_xform (would_recover' xp l hm) =p=>
      rep xp (Synced l) hm \/
      rep xp (Rollback l) hm.
  Proof.
    unfold would_recover'.
    intros.
    xform.
    cancel; (rewrite xform_rep_synced ||
              rewrite xform_rep_rollback ||
              rewrite xform_rep_rollbackunsync); cancel.
  Qed.

  Lemma weq2 : forall sz (x y : word sz) (a b : word sz),
    {x = y /\ a = b} + {(x = y /\ a <> b) \/
                        (x <> y /\ a = b) \/
                        (x <> y /\ a <> b)}.
  Proof.
    intros.
    destruct (weq x y); destruct (weq a b); intuition.
  Defined.

  Definition recover xp cs :=
    let^ (cs, header) <- PermDiskLogHdr.read xp cs;;
    let '((prev_ndesc, prev_ndata),
          (ndesc, ndata),
          (addr_checksum, valu_checksum)) := header in
    let^ (cs, wal) <- Desc.read_all xp ndesc cs;;
    let^ (cs, vl) <- Data.read_all xp ndata cs;;
    default_hash <- Hash default_valu;;
    h_addr <- hash_list default_hash (DescDefs.ipack wal);;
    h_valu <- hash_list default_hash vl;;
    If (weq2 addr_checksum h_addr valu_checksum h_valu) {
      Ret cs
    } else {
      let^ (cs, wal) <- Desc.read_all xp prev_ndesc cs;;
      let^ (cs, vl) <- Data.read_all xp prev_ndata cs;;
      addr_checksum <- hash_list default_hash (DescDefs.ipack wal);;
      valu_checksum <- hash_list default_hash vl;;
      cs <- PermDiskLogHdr.write xp ((prev_ndesc, prev_ndata),
                          (prev_ndesc, prev_ndata),
                          (addr_checksum, valu_checksum)) cs;;
      cs <- PermDiskLogHdr.sync_now xp cs;;
      Ret cs
    }.

(*
  Lemma recover_read_ok_helper : forall xp old new tags,
     Desc.array_rep xp 0 (Desc.Synced tags (map ent_addr (padded_log old ++ new))) =p=>
      Desc.array_rep xp 0 (Desc.Synced tags (map ent_addr (padded_log old ++ padded_log new))).
  Proof.
    intros.
    repeat rewrite map_app.
    rewrite Desc.array_rep_synced_app_rev.
    rewrite <- Desc.array_rep_synced_app.
    cancel.
    rewrite desc_padding_synced_piff.
    cancel.
    rewrite map_length, padded_log_length. unfold roundup; eauto.
    rewrite map_length, padded_log_length. unfold roundup; eauto.
  Qed.

  Lemma recover_ok_addr_helper : forall xp old new,
    Desc.array_rep xp 0
        (Desc.Synced
          (map ent_addr (padded_log old) ++ map ent_addr (padded_log new))) =p=>
    Desc.array_rep xp 0
      (Desc.Synced (map ent_addr (padded_log old ++ new))).
  Proof.
    intros.
    rewrite map_app.
    eapply pimpl_trans; [ | eapply Desc.array_rep_synced_app ].
    rewrite Desc.array_rep_synced_app_rev.
    cancel.
    apply desc_padding_synced_piff.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
  Qed.
*)

Definition recover_ok_Synced :
  forall xp cs pr,
    {< F l d,
     PERM:pr
     PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET:cs'
          PermCacheDef.rep cs' d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    CRASH:bm'', hm_crash, exists cs',
          PermCacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} recover xp cs.
  Proof. 
    unfold recover.
    step.
    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    unfold padded_log.
    rewrite map_length, padded_log_length.
    all: eauto.
    unfold padded_log; rewrite desc_padding_synced_piff.
    pred_apply; cancel.

    safestep.
    rewrite vals_nonzero_addrs.
    replace DataSig.items_per_val with 1 by (cbv; auto).
    unfold ndata_log; omega.
    step.
    step.

    solve_hash_list_rep; auto.
    step.
    solve_hash_list_rep; auto.

    step.
    {
      step.
      step.
      apply desc_padding_synced_piff.
      solve_checksums.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).      
    }
    {
      eapply pimpl_ok2; monad_simpl; eauto with prog.
      intros.
      unfold pimpl; intros.
      unfold checksums_match in *; intuition.
      unfold padded_log in *.
      rewrite app_nil_r, <- desc_ipack_padded in *.
      denote (_ m) as Hx; destruct_lift Hx; intuition.
      all: denote (_ -> False) as Hx; contradict Hx;
      eapply hash_list_injective2; solve_hash_list_rep.
    }

    all: rewrite <- H1; try cancel; unfold padded_log;
    solve [ apply desc_padding_synced_piff |
            solve_checksums |
            solve_hashmap_subset |
            unfold pimpl; intros; simpl;
            repeat (eapply block_mem_subset_trans; eauto)].

    Unshelve.
    all: eauto; try easy; try solve [constructor].
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Definition recover_ok_Rollback :
    forall xp cs pr,
    {< F old d,
    PERM:pr   
    PRE:bm, hm,
        PermCacheDef.rep cs d bm *
        [[ (F * rep xp (Rollback old) hm)%pred d ]] *
        [[ sync_invariant F ]]
    POST:bm', hm', RET:cs' exists d',
          PermCacheDef.rep cs' d' bm' *
          [[ (F * rep xp (Synced old) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, exists cs' d',
          PermCacheDef.rep cs' d' bm'' * (
          [[ (F * rep xp (Rollback old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (RollbackUnsync old) hm_crash)%pred d' ]])
    >} recover xp cs.
  Proof. 
    unfold recover.
    step.
    safestep.

    cleanup.
    eassign (map ent_addr (padded_log old) ++ dummy).
    autorewrite with lists.
    rewrite Nat.mul_add_distr_r.
    unfold padded_log; rewrite padded_log_length.
    unfold roundup, ndesc_log.
    all: auto.

    unfold rep_contents_unmatched.
    rewrite <- Desc.array_rep_synced_app.
    unfold padded_log; repeat rewrite desc_padding_synced_piff.
    autorewrite with lists.
    unfold checksums_match in *.
    erewrite <- ndesc_log_padded_log.
    simpl.
    autorewrite with lists.
    repeat rewrite ndesc_log_padded_log.
    cancel.

    unfold ndesc_log, roundup;
    repeat rewrite padded_log_length; unfold roundup;
    repeat rewrite divup_divup.
    cancel.
    eauto.
    unfold padded_log; rewrite map_length, padded_log_length;
    unfold roundup; eauto.

    prestep. norm. cancel. intuition simpl.
    eassign (vals_nonzero (padded_log old) ++ dummy0).
    autorewrite with lists.
    unfold padded_log.
    rewrite vals_nonzero_addrs, nonzero_addrs_padded_log,
    Nat.mul_add_distr_r.
    unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    repeat rewrite Nat.mul_1_r.
    all: auto.
    autorewrite with lists.
    unfold padded_log.
    
    rewrite <- Data.array_rep_synced_app.
    pred_apply.
    unfold padded_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite vals_nonzero_addrs, nonzero_addrs_padded_log, divup_1.
    cancel.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite Nat.mul_1_r; eauto.

    step.
    step.
    solve_hash_list_rep; auto.
    step.
    solve_hash_list_rep; auto.
    step.

    (* Impossible case: the hash could not have matched what was on disk. *)
    {
      prestep. norm'l.
      Transparent hide_or.
      unfold hide_or in *.
      intuition; exfalso;
      denote (False) as Hcontra; apply Hcontra.
      
      rewrite app_nil_r in *.
      unfold checksums_match in *; intuition.
      apply rev_injective.
      eapply app_inv_tail.

      simpl in *.
      denote (hash_list_rep (rev (vals_nonzero _)) _ _) as Hhlr.
      erewrite vals_nonzero_app in Hhlr.
      erewrite rev_app_distr in Hhlr.

    
      rewrite rev_app_distr in *; simpl in *.
      eapply hash_list_injective; [ | solve_hash_list_rep].
      solve_hash_list_rep.

      rewrite app_nil_r in *.
      unfold checksums_match in *; intuition; simpl in *.
      unfold padded_log in *.

      unfold padded_log; simpl in *.
      rewrite <- desc_ipack_padded.
      eapply app_inv_head.
      repeat erewrite <- DescDefs.ipack_app.
      erewrite <- map_app.
      eapply rev_injective.
      eapply hash_list_injective; [ | solve_hash_list_rep ].
      solve_hash_list_rep.
      
      repeat rewrite  map_length.
      rewrite padded_log_length.
      unfold roundup; eauto.
      repeat rewrite  map_length.
      rewrite padded_log_length.
      unfold roundup; eauto.
    }

    (* False case: the hash did not match what was on disk and we need to recover. *)
    {
      prestep. norm;
      match goal with
      | [ Hor: (_ \/ _) |- _ ] => clear Hor
      end.
      cancel.
      rewrite block_mem_subset_rep.
      cancel.
      repeat (eapply block_mem_subset_trans; eauto).
      intuition simpl.
      instantiate (1:= map ent_addr (padded_log old)).
      unfold padded_log;
      rewrite map_length, padded_log_length.
      all: auto.
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      pred_apply.
      unfold rep_contents_unmatched, padded_log;
      cancel.

      safestep.
      rewrite vals_nonzero_padded_log, vals_nonzero_addrs.
      unfold ndata_log.
      replace DataSig.items_per_val with 1 by (cbv; auto); omega.

      step.
      solve_hash_list_rep; eauto.
      step.
      solve_hash_list_rep; eauto.

      safestep.
      rewrite block_mem_subset_rep.
      cancel.
      repeat (eapply block_mem_subset_trans; eauto). 
      match goal with
      | [ H: ( _ )%pred d |- _ ]
        => unfold PermDiskLogHdr.rep in H; destruct_lift H
      end.
      unfold PermDiskLogHdr.hdr_goodSize in *; intuition.
      2: pred_apply; cancel.
      unfold previous_length, current_length; simpl.
      all: auto.
      
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      step.
      eauto 10.
      step.
      step.


      (* post condition: Synced old *)
      unfold padded_log.
      rewrite desc_padding_synced_piff, vals_nonzero_padded_log.
      cancel.
      rewrite Desc.array_rep_avail_synced, Data.array_rep_avail_synced.
      rewrite <- recover_desc_avail_helper.
      setoid_rewrite <- recover_data_avail_helper.
      cancel.
      rewrite H15; eauto.
      unfold ndesc_list.
      rewrite H16, divup_mul; eauto.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      rewrite vals_nonzero_padded_log in *.
      solve_checksums.
      unfold padded_log in *. erewrite <- desc_ipack_padded in *.
      simpl; solve_hash_list_rep.

      solve_hashmap_subset.
      unfold pimpl; intros; simpl; 
      repeat (eapply block_mem_subset_trans; eauto).
      
      (* Crash conditions. *)
      (* After header write, before header sync: RollbackUnsync *)
      rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl; 
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign cs'; eassign d'; cancel.
      or_r.
      safecancel.
      unfold rep_contents_unmatched, padded_log.
      rewrite desc_padding_synced_piff,
      vals_nonzero_padded_log.
      cancel.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      all: auto.

      (* Make below a lemma *)
      solve_checksums.
      unfold padded_log in *. erewrite <- desc_ipack_padded in *.
      simpl; solve_hash_list_rep.
   
      rewrite vals_nonzero_padded_log in *.
      simpl; solve_hash_list_rep.
      
      solve_checksums.

      (* Crash 2 *)
      unfold pimpl; intros m Hm; destruct_lift Hm; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl; 
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign x0; eassign x1; cancel.
      or_r.
      safecancel.
      unfold rep_contents_unmatched, padded_log.
      rewrite desc_padding_synced_piff,
      vals_nonzero_padded_log.
      cancel.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      all: auto.

      (* Make below a lemma *)
      solve_checksums.
      unfold padded_log in *. erewrite <- desc_ipack_padded in *.
      simpl; solve_hash_list_rep.
      
      rewrite vals_nonzero_padded_log in *.
      simpl; solve_hash_list_rep.
      
      solve_checksums.

      (* Crash 4 *)
     unfold pimpl; intros m Hm; destruct_lift Hm; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl; 
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign dummy1; eassign d; cancel.
      or_l.
      safecancel.
      unfold rep_contents_unmatched, padded_log.
      cancel.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      all: auto.

      solve_checksums.

      (* Crash 5 *)
      unfold pimpl; intros mx Hmx; destruct_lift Hmx; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl; 
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign dummy1; eassign d; cancel.
      or_l.
      safecancel.
      unfold rep_contents_unmatched, padded_log.
      cancel.
      rewrite  desc_padding_synced_piff,
      vals_nonzero_padded_log; cancel.
      rewrite Data.array_rep_synced_app_rev,
      Desc.array_rep_synced_app_rev; simpl.

        
      rewrite map_length, padded_log_length,
      vals_nonzero_addrs.
      unfold roundup; rewrite divup_divup, desc_padding_synced_piff.
      cancel.
      unfold ndata_log.
      rewrite divup_1.
      cancel.
      all: eauto.
      rewrite map_length, padded_log_length;
      unfold roundup; eauto.
      symmetry; apply Nat.mul_1_r.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      solve_checksums.
    }

    (* Rest of the crash conditions. All before header write: Rollback. *)
    (* Crash 6 *)
    unfold pimpl; intros m Hm; destruct_lift Hm; cleanup.
    pred_apply; rewrite <- H1; cancel.
    solve_hashmap_subset.
    unfold pimpl; intros; simpl; 
    repeat (eapply block_mem_subset_trans; eauto).
    xcrash.
    eassign dummy1; eassign d; cancel.
    or_l.
    denote (Data.avail_rep) as Hx; clear Hx.
    denote (Data.avail_rep) as Hx; clear Hx.
    safecancel.
    solve_checksums.

    (* Crash 7 *)
    rewrite <- H1; cancel.
    cancel.
    or_l.
    denote (Data.avail_rep) as Hx; clear Hx.
    safecancel.
    solve_checksums.
    solve_hashmap_subset.
    unfold pimpl; intros; simpl; 
    repeat (eapply block_mem_subset_trans; eauto).

    (* Crash 8 *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    eassign cs'; eassign d; cancel.
    or_l.
    denote (Data.avail_rep) as Hx; clear Hx.
    safecancel.
    solve_checksums.

    Unshelve.
    all: try solve [eauto; econstructor].
    apply tagged_block0.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Definition recover_ok :
    forall xp cs pr,
    {< F st l,
    PERM:pr   
    PRE:bm, hm,
      exists d, PermCacheDef.rep cs d bm *
          [[ (F * rep xp st hm)%pred d ]] *
          [[ st = Synced l \/ st = Rollback l ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET:cs' exists d',
          PermCacheDef.rep cs' d' bm' *
          [[ (F * rep xp (Synced l) hm')%pred d' ]]
    XCRASH:bm', hm',
          would_recover xp F l bm' hm'
    >} recover xp cs.
  Proof.
    unfold would_recover, would_recover';
    intros; eapply corr2_or_helper.
    apply recover_ok_Synced.
    apply recover_ok_Rollback.
    intros; simpl; cancel; subst.
    or_l; cancel.
    eassign l; cancel.
    step.
    rewrite <- H1; cancel.
    cancel.
    or_l; eauto.
    eauto.

    or_r; safecancel.
    eassign l; cancel.
    auto.
    step.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    or_r; or_l; eauto.
    or_r; or_r; eauto.
  Qed.
 
  Hint Extern 1 ({{_ | _}} Bind (recover _ _) _) => apply recover_ok : prog.
