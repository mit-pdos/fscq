Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Pred.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import AsyncDisk.
Require Import Psatz.
Require Import RecArrayUtils.
Require Import AsyncRecArray.
Require Export CacheSec.
Require Import MapUtils.

Import AddrMap.
Import Map MapFacts.
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


  (************* Log header *)
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

    Definition hdr_goodsize (hdr: hdr) := goodSize addrlen (fst hdr) /\ goodSize addrlen (snd hdr).
 
    Definition rep xp hdr :=
      (sep_star (AEQ:=addr_eq_dec) [[ hdr_goodsize hdr ]] 
         ((LAHdr xp) |-> (Public, hdr2val (mk_header hdr))))%pred.

Definition h_read xp cs :=
  Bind (h_read (LAHdr xp) cs)
       (fun csh =>
          let cs:= fst csh in
          let h:= snd csh in
          Bind (Unseal h)
               (fun v =>
                  Ret (cs, (# ((val2hdr v) :-> "ndesc"),
                            # ((val2hdr v) :-> "ndata"))))).

Definition h_write xp n cs :=
  Bind (Seal Public (hdr2val (mk_header n)))
       (fun h => Bind (h_write (LAHdr xp) h cs)
                   (fun cs => Ret cs)).

Lemma rep_none_upd_pimpl:
  forall cs d bm h tb,
    bm h  = None ->
    PermCacheDef.rep cs d bm =p=> PermCacheDef.rep cs d (upd bm h tb).
Proof.
  unfold PermCacheDef.rep, cachepred; intros; cancel.
  eapply MemPred.mem_pred_pimpl; intros.
  destruct (find a (HCSMap cs)); [| cancel];
  destruct p; destruct b;
  cancel;
  destruct (Nat.eq_dec h0 h); subst;
  try congruence; rewrite upd_ne; auto.
Qed.

Theorem h_write_ok :
  forall xp n cs,
    {< F d old bm',
     PERM: None
     PRE: fun bm =>
            PermCacheDef.rep cs d bm * [[ bm = bm' ]] *
            [[ hdr_goodsize n ]] *
            [[ (F * rep xp old)%pred d ]]
     POST: fun bm =>
        RET: cs'
        let new:= (Public, hdr2val (mk_header n)) in
        exists d', PermCacheDef.rep cs' d' bm *
        [[ exists h, bm = upd bm' h new ]] *
        [[ (F * rep xp n)%pred d' ]]
    >} h_write xp n cs.
    Proof.
      unfold h_write, rep.      
      hoare.
      erewrite rep_none_upd_pimpl; eauto.
      Existential 2:= F_. cancel.
      apply upd_eq; auto.
      cancel.
      pred_apply; cancel.
    Qed.      

Theorem h_read_ok :
  forall xp cs,
    {< F d n bm',
     PERM: None
     PRE: fun bm =>
            PermCacheDef.rep cs d bm * [[ bm = bm' ]] *
            [[ (F * rep xp n)%pred d ]]
     POST: fun bm => RET: csr
       let cs' := fst csr in
       let r := snd csr in
       PermCacheDef.rep cs' d bm *
       [[ exists h, bm = upd bm' h (Public, hdr2val (mk_header n)) ]] *
       [[ (F * rep xp n)%pred d ]] *
       [[ r = n ]]
    >} h_read xp cs.
    Proof.
      unfold h_read, rep.
      hoare.
      2: apply upd_eq; eauto.
      simpl; auto.
      subst; rewrite val2hdr2val; simpl.
      unfold mk_header, Rec.recget'; simpl.
      repeat rewrite wordToNat_natToWord_idempotent'; auto.
      destruct n; auto.
      all: unfold hdr_goodsize in *; intuition.
    Qed.