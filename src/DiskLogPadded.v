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

Require Export DiskLogHdr.

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
Definition contents := @generic_contents tagged_block.
Definition input_entry := @generic_entry handle.
Definition input_contents := @generic_contents handle.

Inductive state :=
(* The log is synced on disk *)
| Synced (l: contents)
         
(* The log has been truncated; but the length (0) is unsynced *)
| Truncated (old: contents)
            
(* The log is being extended; only the content has been updated (unsynced) *)
| Extended (old: contents) (new: contents).

Definition ent_addr {B} (e : @generic_entry B) := addr2w (fst e).
Definition ent_handle {A} (e : A * handle) := snd e.
Definition ent_block {A} (e : A * tagged_block) := snd e.
Definition ent_tag {A C} (e : A * (tag * C)) := fst (snd e).
Definition ent_valu {A B} (e : A * (B * valu)) := snd (snd e).

Definition ndesc_log {T} (log : @generic_contents T) := (divup (length log) DescSig.items_per_val).
Definition ndesc_list {T} (l : list T) := (divup (length l) DescSig.items_per_val).

Fixpoint log_nonzero {T} (log : @generic_contents T) :=
  match log with
  | (0, _) :: rest => log_nonzero rest
  | e :: rest => e :: log_nonzero rest
  | nil => nil
  end.

Definition blocks_nonzero (log : contents) := map ent_block (log_nonzero log).
Definition handles_nonzero (log : input_contents) := map ent_handle (log_nonzero log).
Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).
Definition tags_nonzero (log : contents) := map ent_tag (log_nonzero log).

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

Definition addr_tags n := repeat Public n.

Definition rep_contents xp (log : contents) : rawpred tagged_block :=
  ( [[ Forall addr_valid log ]] *
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log log)) (map ent_addr log)) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero log) (vals_nonzero log)) *
    Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
    Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))
  )%pred.

Definition padded_addr (al : list addr) :=
  setlen al (roundup (length al) DescSig.items_per_val) 0.

Definition padded_log_gen {T} def (log : @generic_contents T) :=
  setlen log (roundup (length log) DescSig.items_per_val) (0, def).

Definition padded_log (log : contents) := padded_log_gen tagged_block0 log.

Definition loglen_valid xp ndesc ndata :=
  ndesc <= LogDescLen xp  /\ ndata <= LogLen xp.

Definition loglen_invalid xp ndesc ndata :=
  ndesc > LogDescLen xp \/ ndata > LogLen xp.

Definition hide_or (P : Prop) := P.
Opaque hide_or.

Definition rep_inner xp (st : state) (hm: hashmap): rawpred tagged_block:=
  (match st with
   | Synced l =>
     DiskLogHdr.rep xp (DiskLogHdr.Synced (ndesc_log l, ndata_log l)) *
     rep_contents xp l
       
   | Truncated old =>
     DiskLogHdr.rep xp (DiskLogHdr.Unsync (0, 0) (ndesc_log old, ndata_log old)) *
     rep_contents xp old
       
   | Extended old new =>
     DiskLogHdr.rep xp (DiskLogHdr.Unsync (ndesc_log old + ndesc_log new,
                                           ndata_log old + ndata_log new)
                                          (ndesc_log old, ndata_log old)) *
     rep_contents xp ((padded_log old) ++ new) *
     [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                     (ndata_log old + ndata_log new) ]] *
     [[ Forall entry_valid new ]]
   end)%pred.

Definition xparams_ok xp := 
  DescSig.xparams_ok xp /\ DataSig.xparams_ok xp /\
  (LogLen xp) = DescSig.items_per_val * (LogDescLen xp).

Definition rep xp st hm:=
  ([[ xparams_ok xp ]] * rep_inner xp st hm)%pred.

  Theorem loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.
  Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec (LogDescLen xp) ndesc);
    destruct (lt_dec (LogLen xp) ndata); simpl; auto.
    left; intuition.
  Defined.

  Lemma weq2 : forall sz (x y : word sz) (a b : word sz),
    {x = y /\ a = b} + {(x = y /\ a <> b) \/
                        (x <> y /\ a = b) \/
                        (x <> y /\ a <> b)}.
  Proof.
    intros.
    destruct (weq x y); destruct (weq a b); intuition.
  Defined.
  

(** API **)
Definition avail xp cs :=
  let^ (cs, nr) <- DiskLogHdr.read xp cs;;
  let '(ndesc, _) := nr in
  Ret ^(cs, ((LogLen xp) - ndesc * DescSig.items_per_val)).

Definition read xp cs :=
  let^ (cs, nr) <- DiskLogHdr.read xp cs;;
  let '(ndesc, ndata) := nr in
  let^ (cs, ahl) <- Desc.read_all xp ndesc cs;;
  abl <- unseal_all ahl;;
  let wal := fold_left DescDefs.iunpack abl nil in               
  let al := map (@wordToNat addrlen) wal in
  let^ (cs, vl) <- Data.read_all xp ndata cs;;
  Ret ^(cs, (combine_nonzero al vl)).

Definition init xp cs :=
  cs <- DiskLogHdr.init xp cs;;
  Ret cs.

Definition trunc xp cs :=
  cs <- DiskLogHdr.write xp (0, 0) cs;;
  cs <- DiskLogHdr.sync_now xp cs;;
  Ret cs.

(* I am doing something ugly in here. Type of the input 'log' has type list (addr * handle)
   and blocks of the "real log" is sitting in the block memory *)
Definition extend xp (log: input_contents) cs :=
    (* Synced *)
    let^ (cs, nr) <- DiskLogHdr.read xp cs;;
    let '(ndesc, ndata) := nr in
    let '(nndesc, nndata) := ((ndesc_list log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
       (* I need to seal addr blocks to write them back *)
      ahl <- seal_all (addr_tags nndesc)
             (DescDefs.ipack (map ent_addr log));;
      cs <- Desc.write_aligned xp ndesc ahl cs;;
      (* I need handles to be supplied to me to write data blocks back *) 
      cs <- Data.write_aligned xp ndata (map ent_handle log) cs;;
      (* Extended *)
      cs <- CacheDef.begin_sync cs;;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;;
      cs <- Data.sync_aligned xp ndata nndata cs;;
      cs <- CacheDef.end_sync cs;;
      
      cs <- DiskLogHdr.write xp (ndesc + nndesc, ndata + nndata) cs;;
      cs <- CacheDef.begin_sync cs;;
      cs <- DiskLogHdr.sync xp cs;;
      cs <- CacheDef.end_sync cs;;
      (* Synced *)
      Ret ^(cs, true)
    } else {
      Ret ^(cs, false)
    }.

Definition recover xp cs :=
  let^ (cs, header) <- DiskLogHdr.read xp cs;;
  let '(ndesc, ndata) := header in
  let^ (cs, wal) <- Desc.read_all xp ndesc cs;;
  let^ (cs, vl) <- Data.read_all xp ndata cs;;
  Ret cs.


     
(** Helpers **)
Theorem sync_invariant_rep :
  forall xp st hm,
    sync_invariant (rep xp st hm).
Proof.
  unfold rep, rep_inner, rep_contents.
  destruct st; intros; eauto 50.
Qed.

Hint Resolve sync_invariant_rep.
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
    combine_nonzero (map (@wordToNat _) (map ent_addr (padded_log l))) (blocks_nonzero l) = log_nonzero l.
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

  Lemma tags_nonzero_addrs : forall l,
    length (tags_nonzero l) = nonzero_addrs (map fst l).
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
    Desc.array_rep xp a (Desc.Synced (addr_tags (ndesc_log l)) (map ent_addr (padded_log_gen def l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (addr_tags (ndesc_log l)) (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log_gen, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym.
     erewrite  desc_ipack_padded; eauto.
     rewrite  <- desc_ipack_padded; auto.
     unfold padded_log_gen, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     rewrite <- desc_ipack_padded; auto.
     rewrite <- desc_ipack_padded; auto.
  Qed.

  Lemma desc_padding_unsync_piff : forall xp a T (l: @generic_contents T) def,
    Desc.array_rep xp a (Desc.Unsync (addr_tags (ndesc_log l)) (map ent_addr (padded_log_gen def l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (addr_tags (ndesc_log l)) (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log_gen, setlen, roundup in H.
     rewrite firstn_oob, map_app in H by auto.
     apply Desc.items_valid_app in H; intuition.
     erewrite desc_ipack_padded; eauto.
     rewrite <- desc_ipack_padded; auto.
     unfold padded_log_gen, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     rewrite <- desc_ipack_padded; auto.
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

  Lemma tags_nonzero_padded_log : forall l,
    tags_nonzero (padded_log l) = tags_nonzero l.
  Proof.
    unfold tags_nonzero, padded_log, padded_log_gen, setlen, roundup; simpl.
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

  Arguments Desc.array_rep : simpl never.
  Arguments Data.array_rep : simpl never.
  Arguments Desc.avail_rep : simpl never.
  Arguments Data.avail_rep : simpl never.
  Arguments divup : simpl never.
  Hint Extern 0 (okToUnify (DiskLogHdr.rep _ _) (DiskLogHdr.rep _ _)) => constructor : okToUnify.
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
    rewrite block2val_noop; auto.
    omega.
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
Qed.


Lemma combine_nonzero_extract_blocks_comm:
  forall V al hl (bm: block_mem V),
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
Qed.


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


  Lemma loglen_valid_data_valid :forall T TB xp (old: @generic_contents T) (new: @generic_contents (TB * valu)),
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

  Lemma addr_tags_app:
    forall n m,
      addr_tags (n + m) = addr_tags n ++ addr_tags m.
  Proof.
    induction n; simpl; intros; auto.
    unfold addr_tags in *; simpl; auto.
    rewrite IHn; auto.
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
    cancel.
  Qed.

  Lemma length_map_fst_extract_blocks_eq:
    forall A V (bm: block_mem V) (new: list (A * handle)),
      handles_valid bm (map ent_handle new) ->
      length (map fst new) = length (extract_blocks bm (map ent_handle new)).
  Proof.
    intros.      
    rewrite extract_blocks_length; auto.
    repeat rewrite map_length; auto.
  Qed.

  Lemma ndesc_log_combine_eq:
    forall V (bm: block_mem V) new,
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
    forall V (bm: block_mem V) new,
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
  forall V (bm: block_mem V) new,
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
  forall V (bm: block_mem V) new,
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

Lemma tags_nonzero_combine_entry_valid:
  forall (bm: block_mem _) new,
    Forall entry_valid new ->
    handles_valid bm (map ent_handle new) ->
    tags_nonzero (combine (map fst new) (extract_blocks bm (map ent_handle new)))
    = map fst (extract_blocks bm (map ent_handle new)).
Proof.
  induction new; simpl; intros; auto.
  unfold handles_valid, handle_valid in *.
  inversion H0; subst.
  cleanup.
  unfold tags_nonzero in *; simpl.
  unfold entry_valid in *; inversion H; subst.
  destruct (fst a); intuition; simpl.
  unfold ent_tag in *; simpl.
  rewrite H7; auto.
Qed.

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
      
   Lemma helper_sep_star_reorder : forall V (a b c d : rawpred V),
    a * b * c * d =p=> (a * c) * (b * d).
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_add_sub_0 : forall a b,
    a <= b -> a + (b - a)= b.
  Proof.
    intros; omega.
  Qed.

  
  Lemma helper_trunc_ok : forall T xp l,
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log l)) (map ent_addr l)) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero l) (vals_nonzero l)) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    DiskLogHdr.rep xp (DiskLogHdr.Synced (0, 0))
    =p=>
    DiskLogHdr.rep xp (DiskLogHdr.Synced (@ndesc_log T [], @ndata_log T [])) *
    Desc.array_rep xp 0 (Desc.Synced (addr_tags (@ndesc_log T [])) []) *
    Data.array_rep xp 0 (Data.Synced (tags_nonzero []) (vals_nonzero [])) *
    Desc.avail_rep xp (@ndesc_log T []) (LogDescLen xp - @ndesc_log T []) *
    Data.avail_rep xp (@ndata_log T []) (LogLen xp - @ndata_log T []).
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
  rewrite map_length, Nat.sub_0_r in H16.
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
  rewrite DiskLogHdr.xform_rep_synced.
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
  rewrite DiskLogHdr.xform_rep_unsync.
  norm; auto.

  or_r; cancel.
  cancel_by helper_trunc_ok.
  apply Forall_nil.
  auto.
  or_l; cancel.
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

Lemma sep_star_pimpl_trans :
  forall AT AEQ V (F p q r: @pred AT AEQ V),
    p =p=> q ->
    F * q =p=> r ->
    F * p =p=> r.
Proof.
  intros.
  cancel; auto.
Qed.

  Lemma blocks_nonzero_app : forall a b,
    blocks_nonzero (a ++ b) = blocks_nonzero a ++ blocks_nonzero b.
  Proof.
    unfold blocks_nonzero; induction a; intros; simpl; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.


  Lemma blocks_nonzero_padded_log : forall l,
    blocks_nonzero (padded_log l) = blocks_nonzero l.
  Proof.
    unfold blocks_nonzero, padded_log, padded_log_gen, setlen, roundup; simpl.
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

    repeat rewrite addr_tags_app.
    rewrite Desc.array_rep_synced_app_rev.
    setoid_rewrite <- desc_padding_synced_piff.
    rewrite Desc.array_rep_synced_app.
    cancel.
    repeat rewrite tags_nonzero_app.
    rewrite <- tags_nonzero_padded_log with (l:=new).
    unfold padded_log; cancel.

    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    unfold addr_tags; rewrite repeat_length.
    rewrite Desc.Defs.ipack_length.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite divup_divup; eauto.
    
    apply Forall_append.
    eapply forall_app_r; eauto.
    apply addr_valid_padded; auto.
    eapply forall_app_l; eauto.
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

  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (Synced (padded_log old ++ new)) hm.
  Proof. 
    intros; rewrite rep_extended_facts.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    xform; cancel.
    rewrite DiskLogHdr.xform_rep_unsync; cancel.

    - or_r.
      cancel.
      rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
      rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
      cancel.
      rewrite ndesc_log_app, ndata_log_app.
      unfold padded_log; rewrite ndesc_log_padded_log, ndata_log_padded_log; cancel.
      unfold padded_log; repeat rewrite padded_log_length.
      unfold roundup; rewrite divup_mul; eauto.
    - or_l.
      rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
      rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
      rewrite ndesc_log_app, ndata_log_app.
      rewrite addr_tags_app, map_app.
      rewrite tags_nonzero_app, vals_nonzero_app.
      rewrite vals_nonzero_padded_log, tags_nonzero_padded_log.
      rewrite Data.array_rep_synced_app_rev, Desc.array_rep_synced_app_rev.
      cancel.
      rewrite <- desc_padding_synced_piff.
      unfold padded_log.
      repeat rewrite ndesc_log_padded_log, ndata_log_padded_log.
      cancel.
      rewrite <- Data.avail_rep_merge with (n1:=ndata_log new)(start :=ndata_log old).
      rewrite <- Desc.avail_rep_merge with (n1:=ndesc_log new)(start:=ndesc_log old).
      cancel.
      rewrite Data.array_rep_avail, Desc.array_rep_avail.
      unfold Data.nr_blocks, Desc.nr_blocks.
      unfold ndesc_log, ndata_log.
      repeat rewrite divup_1.
      repeat rewrite map_length.
      rewrite padded_log_length;
      unfold roundup; rewrite divup_divup.
      cancel.
      repeat rewrite vals_nonzero_addrs. cancel.
      all: eauto; try omega.
      all: try apply helper_add_sub_add; eauto.
      eapply padded_addr_valid; eapply forall_app_r; eauto.
      unfold padded_log; rewrite map_length, padded_log_length; unfold roundup; eauto.
      unfold addr_tags; rewrite repeat_length.
      erewrite ndesc_log_ndesc_list.
      unfold padded_log, ndesc_list.
      rewrite DescDefs.ipack_length; eauto.
      rewrite padded_log_idem; eauto.
      rewrite Nat.mul_1_r; eauto.
      rewrite ipack_noop.
      rewrite vals_nonzero_addrs; apply tags_nonzero_addrs.
      unfold padded_log; repeat rewrite padded_log_length.
      unfold roundup; rewrite divup_divup; eauto.
      Unshelve.
      exact tagged_block0.
  Qed.

  
  
(** Specs **)

  Definition avail_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr                      
    PRE:bm, hm,
      CacheDef.rep cs d bm *
      [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET: ^(cs, r)
          CacheDef.rep cs d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = (LogLen xp) - roundup (length l) DescSig.items_per_val ]]
    CRASH:bm'', hm_crash, exists cs',
          CacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} avail xp cs.
  Proof.
    unfold avail.
    safestep.
    safestep.
    safestep.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    cancel; eauto.
    rewrite <- H1; cancel.
    eauto.
  Qed.


  Definition read_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr                      
    PRE:bm, hm,
          CacheDef.rep cs d bm *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET: ^(cs, r)
          CacheDef.rep cs d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ extract_blocks_list bm' r = log_nonzero l ]] *
          [[ handles_valid_list bm' r ]] *
          [[ Forall entry_valid r ]]
    CRASH:bm'', hm_crash, exists cs',
          CacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} read xp cs.
  Proof.
    unfold read, extract_blocks_list, handles_valid_list.
    safestep.

    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    rewrite map_length; unfold padded_log; rewrite padded_log_length.
    auto.
    eassign (addr_tags (ndesc_log l)).
    unfold addr_tags; apply repeat_length.
    auto.
    pred_apply.
    unfold padded_log; rewrite desc_padding_synced_piff; cancel.
    subst.

    step.
    rewrite H18 in H8.
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
    unfold padded_log; rewrite desc_padding_synced_piff; cancel.

    subst.
    setoid_rewrite H18.
    repeat rewrite map_snd_combine_le.
    erewrite DescDefs.iunpack_ipack; eauto.
    rewrite map_snd_combine_nonzero.

    rewrite H25, combine_tags_vals.
    apply combine_nonzero_log_nonzero; auto.
    apply extract_blocks_length in H24; rewrite <- H24, H25.
    setoid_rewrite combine_length_eq.
    rewrite tags_nonzero_addrs, log_nonzero_addrs; auto.
    rewrite ipack_noop;
    rewrite tags_nonzero_addrs, vals_nonzero_addrs; auto.

    rewrite nonzero_addrs_maps; auto.
    apply extract_blocks_length in H24; rewrite <- H24, H25.
    setoid_rewrite combine_length_eq.
    rewrite tags_nonzero_addrs; auto.
    rewrite ipack_noop;
    rewrite tags_nonzero_addrs, vals_nonzero_addrs; auto.

    unfold padded_log; rewrite map_length, padded_log_length.
    unfold roundup; eauto.

    unfold addr_tags; rewrite repeat_length.
    unfold ndesc_log.
    rewrite Desc.Defs.ipack_length.
    rewrite map_length.
    unfold padded_log; rewrite padded_log_length.
    unfold roundup; rewrite divup_mul; auto.

    setoid_rewrite H18.
    repeat rewrite map_snd_combine_le.
    erewrite DescDefs.iunpack_ipack; eauto.
    rewrite map_snd_combine_nonzero; auto.

    rewrite nonzero_addrs_maps; auto.
    apply extract_blocks_length in H24; rewrite <- H24, H25.
    setoid_rewrite combine_length_eq.
    rewrite tags_nonzero_addrs; auto.
    rewrite ipack_noop;
    rewrite tags_nonzero_addrs, vals_nonzero_addrs; auto.
    unfold padded_log; rewrite map_length, padded_log_length.
    unfold roundup; eauto.
    
    unfold addr_tags; rewrite repeat_length.
    unfold ndesc_log.
    rewrite Desc.Defs.ipack_length.
    rewrite map_length.
    unfold padded_log; rewrite padded_log_length.
    unfold roundup; rewrite divup_mul; auto.

    setoid_rewrite H18.
    repeat rewrite map_snd_combine_le.
    erewrite DescDefs.iunpack_ipack; eauto.

    apply entry_valid_combine_nonzero; auto.
    
    rewrite map_length.
    unfold padded_log; rewrite padded_log_length.
    unfold roundup; eauto.
    
    unfold padded_log, addr_tags, ndesc_log;
    rewrite repeat_length, DescDefs.ipack_length,
    map_length, padded_log_length.
    unfold roundup; rewrite divup_divup; auto.
    solve_hashmap_subset.
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.
    
    cancel; eauto.
    rewrite <- H1; cancel.
    unfold padded_log; rewrite desc_padding_synced_piff; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.

    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.

    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).

    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Local Hint Resolve goodSize_0.


 

  Local Hint Resolve Forall_nil.


  Definition init_ok' :
    forall xp cs pr,
    {< F d,
    PERM: pr   
    PRE:bm, hm,
      CacheDef.rep cs d bm *
      [[ (F * initrep xp)%pred d ]] *
      [[ xparams_ok xp /\ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d',
          CacheDef.rep cs d' bm' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, any
    >} init xp cs.
  Proof.
    unfold init, initrep.
    prestep; unfold rep, DiskLogHdr.LAHdr; safecancel.
    eassign (dummy_cur, dummy_old); cancel.
    auto.
    step.
    step.
    unfold ndesc_log, ndata_log; rewrite divup_0; simpl; cancel.
    repeat rewrite Nat.sub_0_r; cbn; cancel.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil by (auto; omega); cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
  Qed.

  Definition init_ok :
    forall xp cs pr,
    {< F l d,
    PERM: pr
    PRE:bm, hm,
      CacheDef.rep cs d bm *
      [[ (F * arrayS (LogHeader xp) l)%pred d ]] *
      [[ length l = (1 + LogDescLen xp + LogLen xp) /\
         LogDescriptor xp = LogHeader xp + 1 /\
         LogData xp = LogDescriptor xp + LogDescLen xp /\
         xparams_ok xp ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d',
      CacheDef.rep cs d' bm' *
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
     CacheDef.rep cs d bm *
     [[ (F * rep xp (Synced l) hm)%pred d ]] *
     [[ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d',
     CacheDef.rep cs d' bm' *
     [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, exists cs' d',
     CacheDef.rep cs' d' bm'' *(
       [[ (F * (rep xp (Synced l) hm_crash))%pred d' ]] \/
       [[ (F * (rep xp (Truncated l) hm_crash))%pred d' ]] )
    >} trunc xp cs.
  Proof.
    unfold trunc.
    step.
    unfold hdr_goodSize in *; intuition.
    step.
    step.
    step.

    (* post condition *)
    cancel_by helper_trunc_ok.
    eexists; repeat (eapply hashmap_subset_trans; eauto).

    (* crash conditions *)
    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    unfold pimpl; intros; eapply block_mem_subset_trans; eauto.
    
    xform_norm. cancel. xform_normr; cancel.
    eassign cs'; eassign d'; cancel.
    or_r; cancel.
    rewrite <- H1; cancel.
    eexists; repeat (eapply hashmap_subset_trans; eauto).
    repeat xcrash_rewrite.
    xform_norm; cancel. xform_normr; cancel.
    eassign x; eassign x0; cancel.
    or_r; cancel.

    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (trunc _ _) _) => apply trunc_ok : prog.

  Remove Hints goodSize_0.

  Local Hint Resolve ent_valid_addr_valid.
  Local Hint Resolve Forall_append.

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
    intros. unfold padded_log.
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
    unfold ndata_log; repeat rewrite vals_nonzero_addrs.
    unfold tags_nonzero, vals_nonzero;
    repeat setoid_rewrite entry_valid_vals_nonzero with (l:= new); auto.
    repeat setoid_rewrite nonzero_addrs_entry_valid with (l:= new); auto; cancel.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.

  Lemma extend_ok_synced_hdr_helper : forall xp T (old new: @generic_contents T) def,
    DiskLogHdr.rep xp (DiskLogHdr.Synced 
                            (ndesc_log old + ndesc_log new,
                             ndata_log old + ndata_log new))
    =p=>
    DiskLogHdr.rep xp (DiskLogHdr.Synced 
                            (ndesc_log (padded_log_gen def old ++ new),
                             ndata_log (padded_log_gen def old ++ new))).
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





Lemma extend_crash_helper:
  forall xp bm (old: contents) new,
    Forall entry_valid new ->
    handles_valid bm (map ent_handle new) ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ((Data.array_rep xp (ndata_log old)
                     (Data.Unsync (map fst (extract_blocks bm (map ent_handle new)))
                                  (map ent_valu (combine (map fst new) (extract_blocks bm (map ent_handle new))))) *
      Desc.array_rep xp (ndesc_log old) (Desc.Unsync (addr_tags (ndesc_list new)) (map ent_addr new))) *
     Data.avail_rep xp
        (ndata_log old + divup (length (map ent_valu (combine (map fst new)
           (extract_blocks bm (map ent_handle new))))) DataSig.items_per_val)
        (LogLen xp - ndata_log old - ndata_log new)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
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
  rewrite combine_length_eq by
      (apply length_map_fst_extract_blocks_eq; eauto).
  rewrite map_length.
  apply helper_loglen_data_valid_extend_entry_valid; auto.
  rewrite map_length.
  apply helper_loglen_desc_valid_extend; auto.
Qed.


Lemma extend_crash_helper_synced:
  forall V xp (bm: block_mem (V * valu)) (old: contents) new,
    Forall entry_valid new ->
    handles_valid bm (map ent_handle new) ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ((Data.avail_rep xp (ndata_log old)
      (divup  (length  (map ent_valu
               (combine (map fst new)
                  (extract_blocks bm (map ent_handle new)))))
         DataSig.items_per_val) *
      Desc.array_rep xp (ndesc_log old) (Desc.Unsync (addr_tags (ndesc_list new)) (map ent_addr new))) *
     Data.avail_rep xp
        (ndata_log old + divup (length (map ent_valu (combine (map fst new)
           (extract_blocks bm (map ent_handle new))))) DataSig.items_per_val)
        (LogLen xp - ndata_log old - ndata_log new)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
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
  rewrite combine_length_eq by
      (apply length_map_fst_extract_blocks_eq; eauto).
  rewrite map_length.
  apply helper_loglen_data_valid_extend_entry_valid; auto.
  rewrite map_length.
  apply helper_loglen_desc_valid_extend; auto.
Qed.

Lemma extend_crash_helper_full_synced:
  forall xp bm (old: contents) new,
    Forall entry_valid new ->
    handles_valid bm (map ent_handle new) ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
((((Desc.array_rep xp (ndesc_log old)
        (Desc.Synced (addr_tags (ndesc_log new))
           (map ent_addr (padded_log_gen dummy_handle new)))
      ✶ Desc.array_rep xp 0 (Desc.Synced (addr_tags (ndesc_log old)) (map ent_addr old)))
     ✶ Data.array_rep xp 0 (Data.Synced (tags_nonzero old) (vals_nonzero old)))
    ✶ Desc.avail_rep xp
        (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
        (LogDescLen xp - ndesc_log old - ndesc_log new))
   ✶ Data.avail_rep xp
       (ndata_log old +
        divup
          (length
             (map ent_valu
                (combine (map fst new) (extract_blocks bm (map ent_handle new)))))
          DataSig.items_per_val) (LogLen xp - ndata_log old - ndata_log new))
  ✶ Data.array_rep xp (ndata_log old)
      (Data.Synced (map fst (extract_blocks bm (map ent_handle new)))
         (map ent_valu (combine (map fst new) (extract_blocks bm (map ent_handle new)))))
  ⇨⇨ ((Desc.array_rep xp 0
         (Desc.Synced (addr_tags (ndesc_log (padded_log old) + ndesc_list new))
            (map ent_addr
               (padded_log old ++
                combine (map fst new) (extract_blocks bm (map ent_handle new)))))
       ✶ Data.array_rep xp 0
           (Data.Synced
              (tags_nonzero
                 (padded_log old ++
                  combine (map fst new) (extract_blocks bm (map ent_handle new))))
              (vals_nonzero
                 (padded_log old ++
                  combine (map fst new) (extract_blocks bm (map ent_handle new))))))
      ✶ Desc.avail_rep xp (ndesc_log (padded_log old) + ndesc_list new)
          (LogDescLen xp - (ndesc_log (padded_log old) + ndesc_list new)))
     ✶ Data.avail_rep xp (ndata_log (padded_log old) + ndata_log new)
         (LogLen xp - (ndata_log (padded_log old) + ndata_log new)).
Proof.
  intros.
  repeat rewrite map_app; repeat rewrite addr_tags_app.
  repeat rewrite vals_nonzero_app, tags_nonzero_app.
  rewrite <- Data.array_rep_synced_app, <- Desc.array_rep_synced_app; simpl.
  unfold padded_log; rewrite tags_nonzero_padded_log, vals_nonzero_padded_log; cancel.
  rewrite ndesc_log_padded_log; cancel.
  repeat rewrite desc_padding_synced_piff.
  cancel.
  unfold ndesc_list.
  repeat rewrite map_length; repeat rewrite padded_log_length; cancel.
  unfold ndesc_log at 5; repeat rewrite Nat.sub_add_distr; cancel.
  repeat rewrite ndata_log_padded_log.
  unfold roundup; rewrite divup_divup.
  unfold ndata_log at 6.
  rewrite nonzero_addrs_entry_valid; eauto.
  rewrite combine_length_eq.
  rewrite map_length, divup_1.
  cancel.
  rewrite map_ent_addr_combine_eq; auto.
  unfold ndesc_log at 1 2; cancel.
  rewrite vals_nonzero_combine_entry_valid; auto.
  rewrite tags_nonzero_combine_entry_valid; auto.
  unfold ndata_log.
  rewrite divup_1, vals_nonzero_addrs; eauto.
  apply length_map_fst_extract_blocks_eq; eauto.
  eauto.
  unfold padded_log; rewrite map_length, padded_log_length.
  unfold roundup; eauto.
  rewrite Nat.mul_1_r; eauto.
Qed.


 Definition extend_ok :
    forall xp (new: input_contents) cs pr,
    {< F old d blocks,
    PERM:pr   
    PRE:bm, hm,
          CacheDef.rep cs d bm *
          [[ (F * rep xp (Synced old) hm)%pred d ]] *
          [[ handles_valid bm (map ent_handle new) ]] *
          [[ blocks = extract_blocks bm (map ent_handle new) ]] *
          [[ Forall entry_valid new /\ sync_invariant F ]]
    POST:bm', hm', RET: ^(cs, r) exists d',
          CacheDef.rep cs d' bm' * 
          ([[ r = true /\
              (F * rep xp (Synced ((padded_log old) ++
                                   (combine (map fst new) blocks))) hm')%pred d' ]] \/
           [[ r = false /\ length ((padded_log old) ++
                                   (combine (map fst new) blocks)) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:bm'', hm_crash, exists cs' d',
          CacheDef.rep cs' d' bm'' *
          ([[ (F * rep xp (Synced old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (Extended old (combine (map fst new) blocks)) hm_crash)%pred d' ]])
    >} extend xp new cs.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      (* rewrite <- DescDefs.ipack_nopad_ipack_eq. *)
      step.
      unfold addr_tags, ndesc_list;
      rewrite repeat_length, DescDefs.ipack_length, map_length; auto.
      unfold addr_tags in *; apply repeat_spec in H5; subst; auto.

      safestep; eauto.
      erewrite block_mem_subset_rep.
      cancel.
      repeat (eapply block_mem_subset_trans; eauto).
      apply loglen_valid_desc_valid; eauto.
      repeat (eapply handles_valid_subset_trans; eauto).
      unfold addr_tags, ndesc_list;
      rewrite repeat_length, DescDefs.ipack_length, map_length; auto.
      pred_apply.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      safestep; eauto.
      eassign (map ent_valu (combine (map fst new)
                                     (extract_blocks bm (map ent_handle new)))).
      
      pose proof (length_map_fst_extract_blocks_eq new H7) as A.
      eapply loglen_valid_data_valid; auto.
      
      
      apply Forall_entry_valid_combine; auto.
      rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      repeat (eapply handles_valid_subset_trans; eauto).

      pose proof (length_map_fst_extract_blocks_eq new H7) as A.
      eassign (map fst (extract_blocks bm (map ent_handle new))).
      rewrite Data.Defs.ipack_length.
      repeat rewrite map_length.
      rewrite divup_1.
      repeat setoid_rewrite combine_length_eq; auto.

      pose proof (length_map_fst_extract_blocks_eq new H7) as A.
      repeat (erewrite <- extract_blocks_subset_trans; eauto). 
      unfold ent_valu; rewrite <- map_map with (f:= snd).
      rewrite map_snd_combine; auto.
      rewrite ipack_noop.
      rewrite combine_map_fst_snd; auto.
      
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      repeat (erewrite <- extract_blocks_subset_trans; eauto).      
      rewrite extract_blocks_length; auto.
      rewrite map_length, min_l.
      apply helper_loglen_data_valid_extend; auto.
      unfold ndata_log.
      eapply le_trans.
      apply nonzero_addrs_bound.
      autorewrite with lists; auto.


      (* sync content *)
      step.
      eauto 10.
      prestep. norm. eassign F_; cancel. intuition simpl.
      
      rewrite desc_padding_unsync_piff.       
      pred_apply; cancel.
      exact dummy_handle.
      rewrite map_length; auto.
      rewrite padded_log_length.
      unfold ndesc_list, roundup; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      eauto 10.

      pose proof (length_map_fst_extract_blocks_eq new H7) as A.
      safestep.
      eassign F_; cancel.
      pred_apply; cancel.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      repeat (erewrite <- extract_blocks_subset_trans; eauto).      
      rewrite extract_blocks_length; auto.
      rewrite map_length, min_l; auto.
      eapply loglen_valid_data_valid; auto.
      apply Forall_entry_valid_combine; auto.
      rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      eauto 10.
      auto.

      safestep.
      eassign F_; cancel.
      auto.

      (* write header *)
      safestep.
      denote DiskLogHdr.rep as Hx; unfold DiskLogHdr.rep in Hx.
      destruct_lift Hx.
      unfold DiskLogHdr.hdr_goodSize in *; intuition.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      step.
      eauto 10.
      
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
      repeat rewrite tags_nonzero_app, vals_nonzero_app,
      map_app, addr_tags_app; auto.
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
      rewrite (entry_valid_ndata (l:=new)); auto.
      rewrite divup_1.
      unfold ndesc_log; cancel.
      
      rewrite tags_nonzero_combine_entry_valid,
      vals_nonzero_combine_entry_valid; auto.
      rewrite vals_nonzero_addrs, divup_1.
      unfold ndata_log; auto.
      auto.
      symmetry; apply Nat.mul_1_r.

      unfold DescSig.items_per_val.
      rewrite valulen_is; unfold addrlen.
      simpl. omega.
      rewrite map_length, padded_log_length; unfold roundup; eauto.
      
      apply Forall_append; auto.
      apply addr_valid_padded; auto.
      apply ent_valid_addr_valid.
      apply Forall_entry_valid_combine; auto.
      
      unfold padded_log; rewrite padded_log_length;
      unfold roundup; rewrite divup_mul; auto.
      
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      
      (* crash conditons *)
      (* after sync data : Extended *)
      (* Crash 1 *)
      solve [unfold false_pred; cancel].

      rewrite <- H1; cancel.
      repeat rewrite ndesc_log_app, ndata_log_app.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_r; cancel.
      apply extend_crash_helper_full_synced; auto.
      apply Forall_append; eauto.
      apply addr_valid_padded; auto.
      apply ent_valid_addr_valid.
      apply Forall_entry_valid_combine; auto.
      apply Forall_entry_valid_combine; auto.
      unfold padded_log; rewrite padded_log_length.
      unfold roundup; rewrite divup_divup; auto.
      solve_hashmap_subset.
      solve_blockmem_subset.

      rewrite <- H1; cancel.
      repeat rewrite ndesc_log_app, ndata_log_app.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_r; cancel.
      apply extend_crash_helper_full_synced; auto.
      apply Forall_append; eauto.
      apply addr_valid_padded; auto.
      apply ent_valid_addr_valid.
      apply Forall_entry_valid_combine; auto.
      apply Forall_entry_valid_combine; auto.
      unfold padded_log; rewrite padded_log_length.
      unfold roundup; rewrite divup_divup; auto.
      solve_hashmap_subset.
      solve_blockmem_subset.


      rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign cs'; eassign d'4; cancel.
     repeat rewrite ndesc_log_app, ndata_log_app.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_r; cancel.
      apply extend_crash_helper_full_synced; auto.
      apply Forall_append; eauto.
      apply addr_valid_padded; auto.
      apply ent_valid_addr_valid.
      apply Forall_entry_valid_combine; auto.
      apply Forall_entry_valid_combine; auto.
      unfold padded_log; rewrite padded_log_length.
      unfold roundup; rewrite divup_divup; auto.

      
      (* Crash 2 *)
      rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign x; eassign x0; cancel.
           repeat rewrite ndesc_log_app, ndata_log_app.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_r; cancel.
      apply extend_crash_helper_full_synced; auto.
      apply Forall_append; eauto.
      apply addr_valid_padded; auto.
      apply ent_valid_addr_valid.
      apply Forall_entry_valid_combine; auto.
      apply Forall_entry_valid_combine; auto.
      unfold padded_log; rewrite padded_log_length.
      unfold roundup; rewrite divup_divup; auto.


      (* before writes *)
      (* Crash 8 *)
      unfold pimpl; intros mx Hx;
      destruct_lift Hx; cleanup.
      pred_apply; rewrite <- H1; cancel.
      solve_hashmap_subset.
      unfold pimpl; intros; simpl;
      repeat (eapply block_mem_subset_trans; eauto).
      xcrash.
      eassign dummy; eassign d'0; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      apply extend_crash_helper; auto.

      rewrite <- H1; cancel; eauto.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_l; cancel.
      apply extend_crash_helper; auto.
      solve_hashmap_subset.
      solve_blockmem_subset.

      rewrite <- H1; cancel; eauto.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      cancel.
      or_l; cancel.
      apply extend_crash_helper; auto.
      solve_hashmap_subset.
      solve_blockmem_subset.

      rewrite <- H1; cancel; eauto.
      solve_hashmap_subset.
      solve_blockmem_subset.
      xcrash.
      eassign cs'; eassign d'0; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      apply extend_crash_helper; auto.
      
      rewrite <- H1; cancel; eauto.
      solve_hashmap_subset.
      xcrash.
      eassign x; eassign x0; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      apply extend_crash_helper_synced; auto.

      rewrite <- H1; cancel; eauto.
      solve_hashmap_subset.
      xcrash.
      eassign x; eassign x0; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      rewrite  Desc.avail_rep_merge; auto.
      apply helper_loglen_desc_valid_extend in H18 as Hx; auto.
      unfold ndesc_log at 1 in Hx.
      rewrite map_length.
      rewrite Hx; eauto.

    (* false case *)
    - safestep.
      safestep.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.
      rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      solve_hashmap_subset.

      solve [unfold false_pred; cancel].
    (* crash for the false case *)
    - rewrite <- H1; cancel.
      solve_hashmap_subset.
      xcrash.
      eassign cs'; eassign d; cancel.
      repeat rewrite ndesc_log_combine_eq, ndata_log_combine_eq; auto.
      or_l; cancel.
      Unshelve.
      all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (extend _ _ _) _) => apply extend_ok : prog.

  
Definition recover_ok :
  forall xp cs pr,
    {< F l d,
     PERM:pr
     PRE:bm, hm,
          CacheDef.rep cs d bm *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET:cs'
          CacheDef.rep cs' d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    CRASH:bm'', hm_crash, exists cs',
          CacheDef.rep cs' d bm'' *
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
    eassign (addr_tags (ndesc_log l)).
    unfold addr_tags; rewrite repeat_length; auto.
    unfold padded_log; rewrite desc_padding_synced_piff.
    pred_apply; cancel.

    safestep.
    rewrite vals_nonzero_addrs.
    replace DataSig.items_per_val with 1 by (cbv; auto).
    unfold ndata_log; omega.
    rewrite tags_nonzero_addrs.
    replace DataSig.items_per_val with 1 by (cbv; auto).
    unfold ndata_log; omega.
    step.
    step.
    apply desc_padding_synced_piff.
    solve_hashmap_subset.
    unfold pimpl; intros; simpl;
    repeat (eapply block_mem_subset_trans; eauto).      
    pred_apply.
    
    all: rewrite <- H1; try cancel; unfold padded_log;
    solve [ apply desc_padding_synced_piff |
            solve_hashmap_subset |
            unfold pimpl; intros; simpl;
            repeat (eapply block_mem_subset_trans; eauto)].

    Unshelve.
    all: eauto; try easy; try solve [constructor].
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  
  Hint Extern 1 ({{_ | _}} Bind (recover _ _) _) => apply recover_ok : prog.
