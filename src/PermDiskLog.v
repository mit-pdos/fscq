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
Definition ent_tag (e : entry) := fst (snd e).
Definition ent_valu (e : entry) := snd (snd e).

Definition ndesc_log (log : contents) := (divup (length log) DescSig.items_per_val).
Definition ndesc_list T (l : list T) := (divup (length l) DescSig.items_per_val).

Fixpoint log_nonzero (log : contents) : list entry :=
  match log with
  | (0, _) :: rest => log_nonzero rest
  | e :: rest => e :: log_nonzero rest
  | nil => nil
  end.

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

Definition rep_contents xp (log : contents) : rawpred :=
  ( [[ Forall addr_valid log ]] *
    Desc.array_rep xp 0 (Desc.Synced (map ent_tag log) (map ent_addr log)) *
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
    Desc.array_rep xp 0 (Desc.Synced (map ent_tag (padded_log old))
                                     (map ent_addr (padded_log old))) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced new_tag new_addr) *
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
  hash_list_rep (rev (DescDefs.ipack (map ent_addr l))) (fst h) hm /\
  hash_list_rep (rev (vals_nonzero l)) (snd h) hm.

Definition hide_or (P : Prop) := P.
Opaque hide_or.

Definition rep_inner xp (st : state) hm : rawpred :=
  (match st with
   | Synced l =>
     exists prev_len h,
     Hdr.rep xp (Hdr.Synced (prev_len,
                             (ndesc_log l, ndata_log l),
                             h)) *
     rep_contents xp l *
     [[ checksums_match l h hm ]]
       
   | Truncated old =>
     exists prev_len h h',
     Hdr.rep xp (Hdr.Unsync ((ndesc_log old, ndata_log old), (0, 0), h')
                            (prev_len, (ndesc_log old, ndata_log old), h)) *
     rep_contents xp old *
     [[ checksums_match old h hm ]] *
     [[ checksums_match [] h' hm ]]
       
   | Extended old new =>
     exists prev_len h h',
     Hdr.rep xp (Hdr.Unsync ((ndesc_log old, ndata_log old),
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
     Hdr.rep xp (Hdr.Synced ((ndesc_log old, ndata_log old),
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
     Hdr.rep xp (Hdr.Synced ((ndesc_log old, ndata_log old),
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
     [[ hide_or (DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr \/
                 vals_nonzero new <> synced_valu) ]] *
     [[ Forall entry_valid new ]]
       
  | RollbackUnsync old =>
    exists synced_addr synced_valu h h' new prev_len,
    Hdr.rep xp (Hdr.Unsync (prev_len, (ndesc_log old, ndata_log old), h')
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
  (exists cs d,
     BUFCACHE.rep cs d *
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
