Require Import Arith.
Require Import Mem Pred.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import Errno.

Require Import GenSepAuto. 
Require Import ListPred.
Require Import Log.
Require Import Balloc.
Require Import FSLayout.
Require Import BlockPtr.


Import ListNotations.

Set Implicit Arguments.


Parameter encode_tag: tag -> word 16.
Parameter decode_tag: word 16 -> tag.
Parameter encode_decode_tag: forall t, decode_tag (encode_tag  t) = t.
Parameter encode_tag_inj: forall t t', encode_tag t = encode_tag t' -> t = t'.
Parameter encode_public: encode_tag Public = $0.


Module INODE.

  (************* on-disk representation of inode *)
  Definition attrtype : Rec.type := Rec.RecF ([
    ("bytes",  Rec.WordF 64) ;       (* file size in bytes *)
    ("uid",    Rec.WordF 32) ;        (* user id *)
    ("gid",    Rec.WordF 32) ;        (* group id *)
    ("dev",    Rec.WordF 64) ;        (* device major/minor *)
    ("mtime",  Rec.WordF 32) ;        (* last modify time *)
    ("atime",  Rec.WordF 32) ;        (* last access time *)
    ("ctime",  Rec.WordF 32) ;        (* create time *)
    ("itype",  Rec.WordF  8)          (* type code, 0 = regular file, 1 = directory, ... *)
   ]).

  Definition iattrtype : Rec.type := Rec.RecF ([
    ("attr", attrtype) ;
    ("owner",  Rec.WordF  16) ;
    ("unused", Rec.WordF 8)          
  ]).

  Definition NDirect := 7.

  Definition irectype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);     (* number of blocks *)
    ("attrs", iattrtype);           (* file attributes *)
    ("indptr", Rec.WordF addrlen);  (* indirect block pointer *)
    ("dindptr", Rec.WordF addrlen); (* doubly-indirect block pointer *)
    ("tindptr", Rec.WordF addrlen); (* triply-indirect block pointer *)
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) NDirect)]).

  (* RecArray for inodes records *)
  Module IRecSig <: RASig.

    Definition xparams := inode_xparams.
    Definition RAStart := IXStart.
    Definition RALen := IXLen.
    Definition xparams_ok (_ : xparams) := True.

    Definition itemtype := irectype.
    Definition items_per_val := valulen / (Rec.len itemtype).


    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; rewrite valulen_is; compute; auto.
    Qed.

  End IRecSig.

  Module IRec := LogRecArrayCache IRecSig.
  Hint Extern 0 (okToUnify (IRec.rep _ _) (IRec.rep _ _)) => constructor : okToUnify.


  Definition iattr := Rec.data iattrtype.
  Definition iattrin := Rec.data attrtype.
  Definition irec := IRec.Defs.item.
  Definition bnlist := list waddr.

  Module BPtrSig <: BlockPtrSig.

    Definition irec     := irec.
    Definition iattr    := iattr.
    Definition NDirect  := NDirect.

    Fact NDirect_bound : NDirect <= addrlen.
      compute; omega.
    Qed.

    Definition IRLen     (x : irec) := Eval compute_rec in # ( x :-> "len").
    Definition IRIndPtr  (x : irec) := Eval compute_rec in # ( x :-> "indptr").
    Definition IRDindPtr (x : irec) := Eval compute_rec in # ( x :-> "dindptr").
    Definition IRTindPtr (x : irec) := Eval compute_rec in # ( x :-> "tindptr").
    Definition IRBlocks  (x : irec) := Eval compute_rec in ( x :-> "blocks").
    Definition IRAttrs   (x : irec) := Eval compute_rec in ( x :-> "attrs").

    Definition upd_len (x : irec) v  := Eval compute_rec in (x :=> "len" := $ v).

    Definition upd_irec (x : irec) len ibptr dibptr tibptr dbns := Eval compute_rec in
      (x :=> "len" := $ len
         :=> "indptr" := $ ibptr
         :=> "dindptr" := $ dibptr
         :=> "tindptr" := $ tibptr
         :=> "blocks" := dbns).

    (* getter/setter lemmas *)
    Fact upd_len_get_len : forall ir n,
      goodSize addrlen n -> IRLen (upd_len ir n) = n.
    Proof.
      unfold IRLen, upd_len; intros; simpl.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_len_get_ind : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_dind : forall ir n, IRDindPtr (upd_len ir n) = IRDindPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_tind : forall ir n, IRTindPtr (upd_len ir n) = IRTindPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_blk : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_iattr : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_len : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen len -> IRLen (upd_irec ir len ibptr dibptr tibptr dbns) = len.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_ind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dibptr tibptr dbns) = ibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_dind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen dibptr -> IRDindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = dibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_tind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen tibptr -> IRTindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = tibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_blk : forall ir len ibptr dibptr tibptr dbns,
      IRBlocks (upd_irec ir len ibptr dibptr tibptr dbns) = dbns.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_iattr : forall ir len ibptr dibptr tibptr dbns,
      IRAttrs (upd_irec ir len ibptr dibptr tibptr dbns) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_eq_upd_len : forall ir len, goodSize addrlen len ->
      upd_len ir len = upd_irec ir len (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (IRBlocks ir).
    Proof.
      intros; simpl. unfold upd_len.
      unfold upd_irec, IRIndPtr, IRDindPtr, IRTindPtr, IRBlocks.
      repeat rewrite natToWord_wordToNat. simpl.
      repeat match goal with [|- context [fst ?x] ] => destruct x; simpl end.
      reflexivity.
    Qed.

    Fact get_len_goodSize : forall ir, goodSize addrlen (IRLen ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

    Fact get_ind_goodSize : forall ir, goodSize addrlen (IRIndPtr ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

    Fact get_dind_goodSize : forall ir, goodSize addrlen (IRDindPtr ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

    Fact get_tind_goodSize : forall ir, goodSize addrlen (IRTindPtr ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

  End BPtrSig.

  Module Ind := BlockPtr BPtrSig.

  Definition NBlocks := let NIndirect := Ind.IndSig.items_per_val in
    NDirect + NIndirect + NIndirect ^ 2 + NIndirect ^ 3.

  Definition items_per_val := IRecSig.items_per_val.


  (************* program *)


  Definition init lxp xp ms :=
    ms <- IRec.init lxp xp ms;;
    (* Need to build domainmem *)
    Ret ms.

  Definition getlen lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;;
    Ret ^(cache, ms, # (ir :-> "len" )).

  (* attribute getters *)

  Definition ABytes  (a : iattrin) := Eval cbn in ( a :-> "bytes" ).
  Definition AMTime  (a : iattrin) := Eval cbn in ( a :-> "mtime" ).
  Definition AType   (a : iattrin) := Eval cbn in ( a :-> "itype" ).
  Definition ADev    (a : iattrin) := Eval cbn in ( a :-> "dev" ).
  Definition AAttrs    (a : iattr) := Eval cbn in ( a :-> "attr" ).
  Definition AOwner    (a : iattr) := Eval cbn in ( a :-> "owner" ).
 (* Definition ADomid    (a : iattr) := Eval cbn in ( a :-> "domid" ). *)

  Definition getattrs lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;;
    Ret ^(cache, ms, (i :-> "attrs" :-> "attr")).

  Definition setattrs lxp xp inum (attr: iattrin) cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := (i :-> "attrs" :=> "attr" := attr)) cache ms;;
    Ret ^(cache, ms).

  (* For updattr : a convenient way for setting individule attribute *)

  Inductive iattrupd_arg :=
  | UBytes (v : word 64)
  | UMTime (v : word 32)
  | UType  (v : word  8)
  | UDev   (v : word 64)
  .

  Definition iattr_upd (e : iattrin) (a : iattrupd_arg) : iattrin := Eval compute_rec in
  match a with
  | UBytes v => (e :=> "bytes" := v)
  | UMTime v => (e :=> "mtime" := v)
  | UType  v => (e :=> "itype" := v)
  | UDev   v => (e :=> "dev"   := v)
  end.

  Definition updattr lxp xp inum a cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := (i :-> "attrs" :=> "attr" := (iattr_upd (i :-> "attrs" :-> "attr") a))) cache ms;;
    Ret ^(cache, ms).

  Definition getowner lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;;
    Ret ^(cache, ms, decode_tag (i :-> "attrs" :-> "owner")).

  Definition setowner lxp xp inum t cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := (i :-> "attrs" :=> "owner" := encode_tag t)) cache ms;;
    _ <- ChDom (S inum) t;;                                              
    Ret ^(cache, ms).
       
  Definition getbnum lxp xp inum off cache ms :=
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;;
    let^ (ms, r) <- Ind.get lxp ir off ms;;
    Ret ^(cache, ms, r).

  Definition getallbnum lxp xp inum cache ms :=
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;;
    let^ (ms, r) <- Ind.read lxp ir ms;;
    Ret ^(cache, ms, r).

  Definition shrink lxp bxp xp inum nr cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);;
    let^ (ms, ir') <- Ind.shrink lxp bxp ir nr (BALLOCC.upd_memstate lms ms);;
    let^ (cache, lms) <- IRec.put_array lxp xp inum ir' cache (BALLOCC.MSLog ms);;
    Ret ^(cache, (BALLOCC.upd_memstate lms ms)).

  (* reset combines shrink and setattr so that removing incurs one IRec.put_array call, instead of 2 *)
  Definition reset lxp bxp xp inum nr attr cache ms := Eval compute_rec in
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);;
    let^ (ms, (ir': irec)) <- Ind.shrink lxp bxp ir nr (BALLOCC.upd_memstate lms ms);;
    let^ (cache, lms) <- IRec.put_array lxp xp inum (ir' :=> "attrs" := (ir' :-> "attrs" :=> "attr" := attr)) cache (BALLOCC.MSLog ms);;
    Ret ^(cache, (BALLOCC.upd_memstate lms ms)).

  Definition grow lxp bxp xp inum bn cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);;
    let^ (ms, r) <- Ind.grow lxp bxp ir ($ bn) (BALLOCC.upd_memstate lms ms);;
    match r with
    | Err e => Ret ^(cache, ms, Err e)
    | OK ir' =>
        let^ (cache, lms) <- IRec.put_array lxp xp inum ir' cache (BALLOCC.MSLog ms);;
        Ret ^(cache, (BALLOCC.upd_memstate lms ms), OK tt)
    end.


  (************** rep invariant *)

  Record inode := mk_inode {
    IBlocks : bnlist;
    IAttr   : iattrin;
    IOwner   : tag;
  }.
  
  Definition iattr0 := @Rec.of_word attrtype $0.
  Definition inode0 := mk_inode nil iattr0 Public.
  Definition irec0 := IRec.Defs.item0.


  Definition inode_match bxp ino (ir : irec) := Eval compute_rec in
    let '(ino, IFs) := ino in
    ( [[ IAttr ino = (ir :-> "attrs" :-> "attr") ]] *
      [[ IOwner ino = decode_tag (ir :-> "attrs" :-> "owner") ]] *
      [[ Forall (fun a => BALLOCC.bn_valid bxp (# a)) (IBlocks ino) ]] *
      Ind.rep bxp IFs ir (IBlocks ino) )%pred.

  Definition rep bxp IFs xp (ilist : list inode) cache (dm: domainmem) := (
     exists reclist fsl, IRec.rep xp reclist cache *
     [[ forall i, i < length ilist ->
             dm (S i) = Some (IOwner (selN ilist i inode0)) ]] *
     [[ IFs <=p=> pred_fold_left fsl ]] * [[ length ilist = length fsl ]] *
     listmatch (inode_match bxp) (combine ilist fsl) reclist)%pred.

  (************** Basic lemmas *)

  Lemma rep_domainmem_subset : forall bxp xp IFs ilist cache dm dm',
    subset dm dm' ->
    rep bxp IFs xp ilist cache dm =p=> rep bxp IFs xp ilist cache dm'.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    cancel; eauto.                                                           
  Qed.

  Hint Resolve rep_domainmem_subset.
  
  Lemma rep_length_pimpl : forall bxp xp IFs ilist cache dm,
    rep bxp IFs xp ilist cache dm =p=> rep bxp IFs xp ilist cache dm *
    [[ length ilist = ((IRecSig.RALen xp) * IRecSig.items_per_val)%nat ]].
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite IRec.items_length_ok_pimpl.
    rewrite listmatch_length_pimpl.
    cancel.
    cbn in *.
    rewrite combine_length_eq in * by auto.
    congruence.
  Qed.

  Lemma irec_well_formed : forall Fm xp l i inum m cache,
    (Fm * IRec.rep xp l cache)%pred m
    -> i = selN l inum irec0
    -> Rec.well_formed i.
  Proof.
    intros; subst.
    eapply IRec.item_wellformed; eauto.
  Qed.

  Lemma direct_blocks_length: forall (i : irec),
    Rec.well_formed i
    -> length (i :-> "blocks") = NDirect.
  Proof.
    intros; simpl in H.
    destruct i; repeat destruct p.
    repeat destruct d0; repeat destruct p; intuition.
  Qed.

  Lemma irec_blocks_length: forall m xp l inum Fm cache,
    (Fm * IRec.rep xp l cache)%pred m ->
    length (selN l inum irec0 :-> "blocks") = NDirect.
  Proof.
    intros.
    apply direct_blocks_length.
    eapply irec_well_formed; eauto.
  Qed.

  Lemma irec_blocks_length': forall m xp l inum Fm len attrs ind dind tind blks u cache,
    (Fm * IRec.rep xp l cache)%pred m ->
    (len, (attrs, (ind, (dind, (tind, (blks, u)))))) = selN l inum irec0 ->
    length blks = NDirect.
  Proof.
    intros.
    eapply IRec.item_wellformed with (i := inum) in H.
    setoid_rewrite <- H0 in H.
    unfold Rec.well_formed in H; simpl in H; intuition.
  Qed.

  Theorem rep_bxp_switch : forall bxp bxp' xp IFs ilist cache dm,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    rep bxp IFs xp ilist cache dm <=p=> rep bxp' IFs xp ilist cache dm.
  Proof.
    intros. unfold rep.
    split.
    norml.
    norm.
    unfold stars; simpl.
    eassign reclist.
    eassign fsl.
    erewrite listmatch_piff_replace.
    eassign (inode_match bxp'); cancel.
    intros; unfold inode_match, BALLOCC.bn_valid.
    destruct x.
    rewrite Ind.rep_bxp_switch by (eassumption||symmetry; eassumption).
    try rewrite H in *.
    split; cancel.
    intuition.

    norml.
    norm.
    unfold stars; simpl.
    eassign reclist.
    eassign fsl.
    erewrite listmatch_piff_replace.
    eassign (inode_match bxp); cancel.
    intros; unfold inode_match, BALLOCC.bn_valid.
    destruct x.
    rewrite Ind.rep_bxp_switch by (eassumption||symmetry; eassumption).
    try rewrite H in *.
    split; cancel.
    intuition.
  Qed.

  
  Lemma rep_clear_cache: forall bxp IFs xp ilist cache dm,
    rep bxp IFs xp ilist cache dm =p=> rep bxp IFs xp ilist IRec.cache0 dm.
  Proof.
    unfold rep.
    cancel.
    rewrite IRec.rep_clear_cache.
    cancel.
    all: auto.
  Qed.

  Lemma rep_upd_attrs: forall bxp Fs ir iblocks (attr : iattr),
    Ind.rep bxp Fs ir iblocks <=p=> Ind.rep bxp Fs (ir :=> "attrs" := attr) iblocks.
  Proof.
    intros.
    cbn in *.
    split; apply Ind.rep_keep_blocks.
    all: repeat match goal with
    | [ |- context [fst ?p] ] => destruct p; cbn
    | [ |- context [snd ?p] ] => destruct p; cbn
    end.
    all: reflexivity.
  Qed.


  Lemma pred_fold_left_transform:
  forall AT AEQ V (l: list (@pred AT AEQ V)),
  pred_fold_left l <=p=> fold_left sep_star l emp.
Proof.
  intros.
  destruct l; simpl.
  split; cancel.
  rewrite stars_prepend'.
  rewrite stars_prepend' with (x:= (emp * p)%pred).
  split; cancel.
Qed.

Lemma pred_fold_left_selN:
  forall AT AEQ V (l: list (@pred AT AEQ V)) n def,
    n < length l ->
    pred_fold_left l <=p=> pred_fold_left (removeN l n) * (selN l n def).
Proof.
  induction l; simpl; intuition.
  destruct n.
  destruct l; simpl; eauto.
  split; cancel.
  rewrite stars_prepend'.
  rewrite stars_prepend' with (x:= p).
  split; cancel.
  rewrite removeN_head.
  simpl.
  rewrite stars_prepend'.
  rewrite <- pred_fold_left_transform.
  apply lt_S_n in H.
  erewrite IHl; eauto.
  rewrite stars_prepend'.
  rewrite <- pred_fold_left_transform.
  split; cancel.
Qed.

  (**************  Automation *)

  Fact resolve_selN_irec0 : forall l i d,
    d = irec0 -> selN l i d = selN l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Rewrite resolve_selN_irec0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.


  Ltac destruct_irec' x :=
    match type of x with
    | irec => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | iattr => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | iattrin => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | prod _ _ => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | _ => idtac
    end.

  Ltac destruct_irec x :=
    match x with
    | (?a, ?b) => (destruct_irec a || destruct_irec b)
    | fst ?a => destruct_irec a
    | snd ?a => destruct_irec a
    | _ => destruct_irec' x; simpl
    end.

  Ltac smash_rec_well_formed' :=
    match goal with
    | [ |- Rec.well_formed ?x ] => destruct_irec x
    end.

  Ltac smash_rec_well_formed :=
    subst; autorewrite with defaults;
    repeat smash_rec_well_formed';
    unfold Rec.well_formed; simpl;
    try rewrite Forall_forall; intuition.


  Ltac irec_wf :=
    smash_rec_well_formed;
    match goal with
      | [ H : ?p %pred ?mm |- length ?d = NDirect ] =>
      match p with
        | context [ IRec.rep ?xp ?ll ?cc ] => 
          eapply irec_blocks_length' with (m := mm) (l := ll) (cache := cc) (xp := xp); eauto;
          pred_apply; cancel
      end
    end.

  Arguments Rec.well_formed : simpl never.

  (********************** SPECs *)

  Lemma in_updN_strict:
      forall t (l : list t) (n : addr) (x xn : t),
        In x l ⟦ n := xn ⟧ -> In x (removeN l n) \/ x = xn.
    Proof.
      induction l; simpl in *; intros; intuition.
      destruct n; simpl in *.
      unfold removeN in *; simpl; intuition.
      intuition.
      apply IHl in H0.
      intuition.
    Qed.

    Lemma in_filter_true:
        forall A (f: A -> bool) l a,
          In a l ->
          f a = true ->
          In a (filter f l).
      Proof.
        induction l; simpl; intros; eauto.
        intuition; subst.
        rewrite H0.
        intuition.
        destruct (f a); eauto.
        apply in_cons; eauto.
      Qed.
    
    Lemma nodup_filter_updN_false:
      forall A (f: A -> bool) l i x,
        f x = false ->
        NoDup (filter f l) ->
        NoDup (filter f (updN l i x)).
    Proof.
      induction l; simpl; intros; eauto.
      destruct i; simpl.
      rewrite H.
      destruct (f a); intuition.
      inversion H0; subst; eauto.
      destruct (f a); intuition.
      inversion H0; subst; eauto.
      constructor.
      unfold not; intros; apply H3.
      apply filter_In in H1.
      destruct H1.
      apply in_updN in H1.
      intuition; subst; try congruence.
      eapply in_filter_true; eauto.
      eauto.
    Qed.

    Lemma de_morgan_or:
        forall P Q,
          ~(P \/ Q) ->
          ~P /\ ~Q.
      Proof.
        unfold not; intros; split; intros; eauto.
      Qed.

    Lemma nodup_filter_updN_notin:
      forall A (f: A -> bool) l i x,
        ~In x l ->
        NoDup (filter f l) ->
        NoDup (filter f (updN l i x)).
    Proof.
      induction l; simpl; intros; eauto.
      destruct i; simpl.     
      apply de_morgan_or in H; destruct H.
      destruct (f a); 
      [inversion H0; subst; eauto |];
      destruct (f x); eauto;
      constructor; eauto;
      unfold not; intros; apply H1;
      apply filter_In in H2; intuition.

      apply de_morgan_or in H; destruct H.
       destruct (f a); 
      [inversion H0; subst; eauto |]; eauto.
      constructor; eauto.
      unfold not; intros; apply H4.
      apply filter_In in H2; intuition.
      apply in_updN in H3; intuition; subst; try congruence.
      apply filter_In; intuition.
    Qed.
    
  Theorem setowner_ok :
    forall lxp bxp xp inum t cache ms pr,
    {~<W F Fm Fi Fs m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs)%pred sm ]] *
           [[ can_access pr (IOwner ino) ]]
    POST:bm', hm', RET:^(cache',ms) exists m' ilist' ino' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' hm') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs')%pred sm ]] *
           [[ ino' = mk_inode (IBlocks ino) (IAttr ino) t ]] *
           [[ hm' 0  = Some Public ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    W>~} setowner lxp xp inum t cache ms.
  Proof.
    unfold setowner, rep.
    safestep.
    denote listmatch as Hm;
    rewrite listmatch_length_pimpl in Hm.
    destruct_lift Hm.
    rewrite combine_length_eq in *; eauto.
    denote (length _ = length _) as Hlen;
    setoid_rewrite <- Hlen.
    eapply list2nmem_inbound; eauto.
    denote listmatch as Hm;
    rewrite listmatch_length_pimpl in Hm.
    destruct_lift Hm.
    rewrite combine_length_eq in *; [ |eauto].
    step.
    irec_wf.
    sepauto.

    assert(A: inum < length ilist). {
      eapply list2nmem_inbound; eauto.
    }

    step.
    repeat (eapply subset_extract_some; eauto).

    safestep.
    safestep.

    rewrite LOG.rep_blockmem_subset; eauto.
    3: eauto.
    2: eapply list2nmem_updN; eauto.
    pred_apply.
    rewrite listmatch_isolate with (i:= inum); eauto.
    cancel; eauto.
    setoid_rewrite listmatch_isolate with (i:= inum) at 2; eauto.
    rewrite removeN_combine.
    setoid_rewrite removeN_combine.
    do 2 rewrite removeN_updN.
    setoid_rewrite selN_combine at 2; auto.
    repeat rewrite selN_updN_eq; eauto.
    unfold inode_match; rewrite selN_combine; auto.
    erewrite <- list2nmem_sel with (x:= ino); eauto.
    cancel; eauto.
    rewrite encode_decode_tag; auto.
    simplen.
    simplen.
    simplen.

    destruct (addr_eq_dec inum i); subst.
    rewrite selN_updN_eq; eauto; simpl.
    eapply subset_extract_some; eauto.
    simpl; apply upd_eq; eauto.

    rewrite selN_updN_ne; eauto.
    eapply subset_extract_some; [|eauto].
    rewrite upd_ne; eauto.
    rewrite length_updN in *; eauto.
    simplen.
    simplen.

    eapply subset_extract_some; [|eauto].
    rewrite upd_ne; try omega.
    repeat (eapply subset_extract_some; eauto).

    cancel.
    rewrite <- H1; cancel.
    eauto.
    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: try exact addr; try exact nil; eauto.
    exact irec0.
    exact irec0.
  Qed.


  Lemma inode_match_init_ok : forall bxp n,
    emp =p=> listmatch (inode_match bxp) (repeat (inode0, emp) n) (repeat IRec.Defs.item0 n).
  Proof. Admitted. (* takes too long
    induction n; simpl; intros.
    unfold listmatch; cancel.
    rewrite IHn.
    rewrite listmatch_cons.
    cancel.
    unfold inode_match.
    rewrite Ind.rep_piff_direct by (cbn; omega).
    unfold Ind.rep_direct; cancel.
    rewrite Ind.indrep_0 by (compute; auto). cancel.
    repeat constructor.
    eapply list_same_repeat.
    setoid_rewrite <- encode_public; rewrite encode_decode; auto.
  Qed.
  *)
  
  Theorem init_ok :
    forall lxp bxp xp ms pr,
    {< F Fm Fs m0 sm m l,
    PERM:pr   
    PRE:bm, hm, 
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (IXStart xp) l) ]]] *
           [[ Fs sm ]] *
           [[ length l = (IXLen xp) /\ (IXStart xp) <> 0 ]]
    POST:bm', hm', RET:ms exists m' IFs,
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs xp (repeat inode0 ((IXLen xp) * IRecSig.items_per_val)) (IRec.cache0) hm') ]]] *
           [[ (Fs * IFs)%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} init lxp xp ms.
  Proof. Admitted. (*
    unfold init, rep.
    step.
    cbv; auto.
    step.
    step.

    unfold IRec.rep. cancel.
    eassign (repeat IRec.LRA.Defs.item0 (IRecSig.RALen xp * IRecSig.items_per_val)).
    cancel.
    erewrite combine_repeat.
    apply inode_match_init_ok.
    apply IRec.cache_rep_empty.
    destruct (lt_dec i (IXLen xp * IRecSig.items_per_val)).
    rewrite repeat_selN; eauto.
    rewrite selN_oob; eauto.
    rewrite repeat_length; omega.
    repeat rewrite repeat_length; auto.
    apply Ind.pred_fold_left_repeat_emp.
  Qed.
  *)
  
  Theorem getlen_ok :
    forall lxp bxp xp inum cache ms pr,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: Fi * inum |-> ino ]]]
    POST:bm', hm', RET:^(cache', ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache' hm') ]]] *
           [[ r = length (IBlocks ino) ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} getlen lxp xp inum cache ms.
  Proof. 
    unfold getlen, rep; pose proof irec0.
    safestep.
    sepauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H9.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; [ |eauto].
    step.
    step.
 
    subst.
    rewrite listmatch_isolate with (i:= inum) in H0 by simplen.
    unfold inode_match at 2 in H0.
    erewrite selN_combine in H0; auto.
    unfold Ind.rep in H0.
    destruct_lift H0.
    unfold BPtrSig.IRLen in *.
    erewrite list2nmem_sel with (x:= ino); eauto.
    Unshelve.
    all: eauto.
  Qed.


  Theorem getattrs_ok :
    forall lxp bxp xp inum cache ms pr,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:bm', hm', RET:^(cache',ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache' hm') ]]] *
           [[ r = IAttr ino ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} getattrs lxp xp inum cache ms.
  Proof. 
    unfold getattrs, rep.
    safestep.
    sepauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H9.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; [ |eauto].
    step.
    step.

    subst.
    rewrite H18.
    rewrite listmatch_isolate with (i:= inum) in H0 by simplen.
    unfold inode_match at 2 in H0.
    erewrite selN_combine in H0; auto.
    destruct_lift H0; auto.
    erewrite list2nmem_sel with (x:= ino); eauto.
    Unshelve.
    all: eauto.
  Qed.


  Theorem setattrs_ok :
    forall lxp bxp xp inum attr cache ms pr,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm, 
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:bm', hm', RET:^(cache',ms) exists m' ilist' ino',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs xp ilist' cache' hm') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (IBlocks ino) attr (IOwner ino)]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} setattrs lxp xp inum attr cache ms.
  Proof. 
    unfold setattrs, rep.
    safestep.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H9.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; [ |eauto].
    step.
    simpl.
    irec_wf.
    sepauto.

    safestep.
    safestep.

    cancel.
    erewrite listmatch_updN_selN; simplen.
    rewrite <- combine_updN.
    eauto.
    all: eauto.
    5: eapply list2nmem_updN; eauto.
    unfold inode_match; rewrite selN_combine; auto.
    erewrite <- list2nmem_sel with (x:= ino); eauto.
    cancel; eauto.

    destruct (addr_eq_dec inum i); subst.
    rewrite selN_updN_eq; eauto; simpl; eauto.
    repeat (eapply subset_extract_some; eauto).
    erewrite list2nmem_sel with (x:= ino); eauto.
    match goal with
    | [H: forall _, _ -> _ |- _ ] =>
      eapply H
    end.
    simplen.
    simplen.
    rewrite selN_updN_ne; eauto.
    repeat (eapply subset_extract_some; eauto).
    match goal with
    | [H: forall _, _ -> _ |- _ ] =>
      eapply H
    end.
    simplen.
    
    
    rewrite updN_selN_eq; auto.
    repeat rewrite length_updN; auto.
    cancel.
    rewrite <- H1; cancel.
    eauto.
    solve_blockmem_subset.
    rewrite <- H1; cancel; eauto.
    Unshelve. exact irec0.
    all: eauto.
  Qed.


  Theorem updattr_ok :
    forall lxp bxp xp inum kv cache ms pr,
    {< F Fm Fi Fs m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs)%pred sm ]]
    POST:bm', hm', RET:^(cache',ms) exists m' ilist' ino' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' hm') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs')%pred sm ]] *
           [[ ino' = mk_inode (IBlocks ino) (iattr_upd (IAttr ino) kv) (IOwner ino)]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} updattr lxp xp inum kv cache ms.
  Proof. 
    unfold updattr, rep.
    safestep.
    sepauto.
     rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H10.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; [ |eauto].

    safestep.
    filldef; abstract (destruct kv; simpl; subst; irec_wf).
    sepauto.
    eauto.

    safestep.
    safestep.

    erewrite listmatch_updN_selN; simplen.
    rewrite <- combine_updN.
    eauto.
    all: eauto.
    5: eapply list2nmem_updN; eauto.
    unfold inode_match; rewrite selN_combine; auto.
    erewrite <- list2nmem_sel with (x:= ino); eauto.
    cancel; eauto.
    cleanup; auto.

    destruct (addr_eq_dec inum i); subst.
    rewrite selN_updN_eq; eauto; simpl; eauto.
    repeat (eapply subset_extract_some; eauto).
    erewrite list2nmem_sel with (x:= ino); eauto.
    match goal with
    | [H: forall _, _ -> _ |- _ ] =>
      eapply H
    end.
    simplen.
    simplen.
    rewrite selN_updN_ne; eauto.
    repeat (eapply subset_extract_some; eauto).
    match goal with
    | [H: forall _, _ -> _ |- _ ] =>
      eapply H
    end.
    simplen.
    
    rewrite updN_selN_eq; auto.
    repeat rewrite length_updN; auto.
    cancel.
    rewrite <- H1; cancel.
    eauto.
    solve_blockmem_subset.
    rewrite <- H1; cancel; eauto.
    Unshelve. exact irec0.
    all: eauto.
  Qed.


  Theorem getbnum_ok :
    forall lxp bxp xp inum off cache ms pr,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[ off < length (IBlocks ino) ]] *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:bm', hm', RET:^(cache', ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache' hm') ]]] *
           [[ r = selN (IBlocks ino) off $0 ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} getbnum lxp xp inum off cache ms.
  Proof. 
    unfold getbnum, rep.
    safestep.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H10.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; [ |eauto].

    step.
    rewrite listmatch_isolate with (i := inum).
    unfold inode_match at 2.
    erewrite selN_combine; auto.
    erewrite <- list2nmem_sel with (x:= ino); eauto.
    cancel.
    seprewrite.
    rewrite combine_length_eq; auto.
    seprewrite.
    rewrite <- H10; eauto.

    step.
    step.

    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: eauto.
  Qed.


  Theorem getallbnum_ok :
    forall lxp bxp xp inum cache ms pr,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:bm', hm', RET:^(cache', ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache' hm') ]]] *
           [[ r = (IBlocks ino) ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} getallbnum lxp xp inum cache ms.
  Proof. 
    unfold getallbnum, rep.
    safestep.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H9.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; [ |eauto].

    step.
    rewrite listmatch_isolate with (i := inum).
    unfold inode_match at 2.
    erewrite selN_combine; auto.
    erewrite <- list2nmem_sel with (x:= ino); eauto.
    cancel.
    seprewrite.
    rewrite combine_length_eq; auto.
    seprewrite.
    rewrite <- H9; eauto.

    step.
    step.

    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: eauto.
  Qed.

 Theorem getowner_ok :
    forall lxp bxp xp inum cache ms pr,
    {< F Fm Fi m0 sm m IFs ilist ino,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:bm', hm', RET:^(cache',ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache' hm') ]]] *
           [[ r = IOwner ino ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} getowner lxp xp inum cache ms.
  Proof.
    unfold getowner, rep.
    safestep.
    sepauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H9.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H.
    rewrite combine_length_eq in *; [ |eauto].
    step.
    step.


    subst.
    rewrite listmatch_isolate with (i:= inum) in H0 by simplen.
    unfold inode_match at 2 in H0.
    erewrite selN_combine in H0; auto.
    destruct_lift H0; auto.
    erewrite list2nmem_sel with (x:= ino); eauto.
    Unshelve.
    all: eauto.
  Qed.

  Theorem shrink_ok :
    forall lxp bxp xp inum nr cache ms pr, 
    {< F Fm Fi Fs m0 sm m IFs ilist ino freelist,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(cache', ms) exists m' ilist' ino' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' hm' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) (IAttr ino) (IOwner ino)]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} shrink lxp bxp xp inum nr cache ms.
  Proof.
    unfold shrink, rep.
    safestep.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H11.
    eapply list2nmem_inbound; eauto.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; [ |eauto].
   
    seprewrite.
    safestep.
    rewrite listmatch_isolate with (i := inum).
    unfold inode_match at 2.
    erewrite selN_combine; auto.
    cancel.
    rewrite combine_length_eq; auto.
    seprewrite.
    rewrite <- H11; eauto.
    sepauto.

    
    rewrite H14; rewrite pred_fold_left_selN; [| rewrite <- H13; eauto].
    eassign (emp(AT:=addr)(AEQ:=addr_eq_dec)(V:=bool)).
    eassign (pred_fold_left (removeN dummy0 inum) * Fs)%pred.
    cancel.
    eauto.

    step.
    subst; unfold BPtrSig.upd_irec, BPtrSig.IRLen. simpl.
    smash_rec_well_formed.
    unfold Ind.rep in *. rewrite BPtrSig.upd_irec_get_blk in *.
    destruct_lift H20. auto.
    sepauto.

    safestep.
    safestep.
    6: eauto.
    5: eapply list2nmem_updN; eauto.
    rewrite listmatch_isolate with (i := inum) in H.
    unfold inode_match, Ind.rep in H; 
    erewrite selN_combine in H; eauto.
    destruct_lift H; eauto. 
    cancel.
    rewrite combine_updN.
    rewrite listmatch_updN_removeN.
    unfold inode_match at 3; simpl.

    unfold cuttail, BPtrSig.upd_len, BPtrSig.IRLen; simpl.
    replace (length (IBlocks ilist ⟦ inum ⟧)) with (# (fst (selN dummy inum IRec.LRA.Defs.item0))).
    cancel.
    eauto.
    eauto.
    eauto.
    apply forall_firstn; auto.
    cleanup; unfold BPtrSig.IRLen; auto.
    rewrite combine_length_eq; auto.
    rewrite <- H11; eauto.
    rewrite combine_length_eq; auto.
    rewrite <- H11; eauto.

    rewrite length_updN in *.
    destruct (addr_eq_dec inum i); subst.
    rewrite selN_updN_eq; eauto; simpl.
    eapply subset_extract_some; eauto.

    rewrite selN_updN_ne; eauto.
    eapply subset_extract_some; eauto.

    erewrite pred_fold_left_selN with (l:= updN dummy0 inum IFs').
    rewrite selN_updN_eq.
    rewrite removeN_updN; eauto.
    apply sep_star_comm.
    rewrite <- H13; eauto.
    rewrite length_updN, <- H13; eauto.
    repeat rewrite length_updN; auto.
    eauto.
    
    all: rewrite <- H1; cancel; eauto.

    Unshelve. exact IRec.Defs.item0. all: eauto.
  Qed.

  Theorem reset_ok : 
    forall lxp bxp xp inum nr attr cache ms pr,
    {< F Fm Fi Fs m0 sm m IFs ilist ino freelist,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(cache', ms) exists m' ilist' ino' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' hm' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ ilist' = updN ilist inum ino' ]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) attr (IOwner ino)]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} reset lxp bxp xp inum nr attr cache ms.
  Proof.
    unfold reset, rep.
    safestep.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H11.
    eapply list2nmem_inbound; eauto.

    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; [ |eauto].

    seprewrite.
    safestep.
    rewrite listmatch_isolate with (i := inum).
    unfold inode_match at 2.
    erewrite selN_combine; auto.
    cancel.
    rewrite combine_length_eq; auto.
    seprewrite; auto.
    rewrite <- H11; eauto.
    sepauto.

    rewrite H14; rewrite pred_fold_left_selN; [| rewrite <- H13; eauto].
    eassign (emp(AT:=addr)(AEQ:=addr_eq_dec)(V:=bool)).
    eassign (pred_fold_left (removeN dummy0 inum) * Fs)%pred.
    cancel.
    eauto.

    seprewrite.
    safestep.
    subst; unfold BPtrSig.upd_irec, BPtrSig.IRLen. simpl.
    smash_rec_well_formed.
    unfold Ind.rep in *. rewrite BPtrSig.upd_irec_get_blk in *.
    destruct_lift H20. auto.
    sepauto.
    eauto.

    safestep.
    safestep.

    6: eauto.
    6: eauto.
    5: eapply list2nmem_updN; eauto.
    auto.
    rewrite listmatch_isolate with (i := inum) in H.
    unfold inode_match, Ind.rep in H; 
    erewrite selN_combine in H; eauto.
    destruct_lift H; eauto. 
    cancel.
    rewrite combine_updN.
    rewrite listmatch_updN_removeN.
    unfold inode_match at 3; simpl.
    rewrite rep_upd_attrs. cbn.

    unfold cuttail, BPtrSig.upd_len, BPtrSig.IRLen; simpl.
    replace (length (IBlocks ilist ⟦ inum ⟧)) with (# (fst (selN dummy inum IRec.LRA.Defs.item0))).
    cancel.
    eauto.
    eauto.
    apply forall_firstn; eauto.
    cleanup; unfold BPtrSig.IRLen; auto.
    rewrite combine_length_eq; auto.
    rewrite <- H11; eauto.
    rewrite combine_length_eq; auto.
    rewrite <- H11; eauto.

    rewrite length_updN in *.
    destruct (addr_eq_dec inum i); subst.
    rewrite selN_updN_eq; eauto; simpl.
    eapply subset_extract_some; eauto.
    rewrite selN_updN_ne; eauto.
    eapply subset_extract_some; eauto.

    erewrite pred_fold_left_selN with (l:= updN dummy0 inum IFs').
    rewrite selN_updN_eq.
    rewrite removeN_updN; eauto.
    apply sep_star_comm.
    rewrite <- H13; eauto.
    rewrite length_updN, <- H13; eauto.
    repeat rewrite length_updN; auto.
    eauto.

    all: rewrite <- H1; cancel; eauto.

    Unshelve. exact IRec.Defs.item0. all: eauto.
  Qed.

  Lemma grow_wellformed :
    forall (a : BPtrSig.irec) inum reclist cache F1 F2 F3 F4 m xp,
    ((((F1 * IRec.rep xp reclist cache) * F2) * F3) * F4)%pred m ->
    length (BPtrSig.IRBlocks a) = length (BPtrSig.IRBlocks (selN reclist inum irec0)) ->
    inum < length reclist ->
    Rec.well_formed a.
  Proof.
    unfold IRec.rep, IRec.LRA.rep, IRec.LRA.items_valid; intros.
    destruct_lift H.
    denote Forall as Hx.
    apply Forall_selN with (i := inum) (def := irec0) in Hx; auto.
    apply direct_blocks_length in Hx.
    setoid_rewrite <- H0 in Hx.
    cbv in Hx; cbv in a.
    smash_rec_well_formed.
  Qed.

  Theorem grow_ok : 
    forall lxp bxp xp inum bn cache ms pr,
    {< F Fm Fi Fs m0 sm m IFs ilist ino freelist,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[ length (IBlocks ino) < NBlocks ]] *
           [[ BALLOCC.bn_valid bxp bn ]] *
           [[[ m ::: (Fm * rep bxp IFs xp ilist cache hm * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(cache', ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' \/
           [[ r = OK tt ]] * exists ilist' ino' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' xp ilist' cache' hm' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ ino' = mk_inode ((IBlocks ino) ++ [$ bn]) (IAttr ino) (IOwner ino)]] *
           [[ incl freelist' freelist ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} grow lxp bxp xp inum bn cache ms.
  Proof.
    unfold grow, rep.
    safestep.
    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; eauto.
    setoid_rewrite <- H13.
    eapply list2nmem_inbound; eauto.

    rewrite listmatch_length_pimpl in *.
    destruct_lift H5.
    rewrite combine_length_eq in *; [ |eauto].

    seprewrite.
    safestep.
    sepauto.
    rewrite listmatch_isolate with (i := inum).
    unfold inode_match at 2.
    erewrite selN_combine; auto.
    cancel.
    rewrite combine_length_eq; auto.
    seprewrite; auto.
    rewrite <- H13; eauto.

    rewrite H16; rewrite pred_fold_left_selN; [| rewrite <- H15; eauto].
    eassign (emp(AT:=addr)(AEQ:=addr_eq_dec)(V:=bool)).
    eassign (pred_fold_left (removeN dummy0 inum) * Fs)%pred.
    cancel.
    eauto.

    seprewrite.
    safestep.
    eapply grow_wellformed with (m:=list2nmem m); eauto.
    pred_apply; cancel.
    eassign Fm.
    eassign (listmatch (inode_match bxp) (combine ilist dummy0) dummy).
    eassign (BALLOCC.rep bxp freelist ms).
    cancel.
    eassign xp; eassign a; cancel.
    sepauto.

    safestep.
    safestep.

    or_r; cancel.
    5: eapply list2nmem_updN; eauto.
    3: eassign (updN dummy0 inum a4)%pred; 
       erewrite pred_fold_left_selN with (l:= updN dummy0 inum a4); 
       [|rewrite length_updN; rewrite <- H15; eauto];
       rewrite selN_updN_eq; eauto;
       rewrite removeN_updN; rewrite sep_star_comm; eauto.
    3: repeat rewrite length_updN; auto.
    rewrite combine_updN.
    rewrite listmatch_updN_removeN.
    unfold inode_match at 3; simpl.
    unfold BPtrSig.IRAttrs in H25.
    rewrite listmatch_isolate with (i := inum) in H.
    unfold inode_match, Ind.rep in H; 
    erewrite selN_combine in H; eauto.
    destruct_lift H; eauto. 
    cancel.

    rewrite H25; eauto.
    rewrite H25 in *; eauto.
    apply Forall_app; auto.
    eapply BALLOCC.bn_valid_roundtrip; eauto.
    rewrite combine_length_eq; auto.
    rewrite <- H13; eauto.
    rewrite combine_length_eq; auto.
    rewrite <- H13; eauto.

    rewrite length_updN in *.
    destruct (addr_eq_dec inum i); subst.
    rewrite selN_updN_eq; eauto; simpl.
    eapply subset_extract_some; eauto.
    rewrite selN_updN_ne; eauto.
    eapply subset_extract_some; eauto.
    solve_blockmem_subset.

    all: try (rewrite <- H1; cancel; eauto).

    step.

    Unshelve. all: eauto. exact emp.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (getlen _ _ _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (getattrs _ _ _ _ _) _) => apply getattrs_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (setattrs _ _ _ _ _ _) _) => apply setattrs_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (updattr _ _ _ _ _ _) _) => apply updattr_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (getbnum _ _ _ _ _ _) _) => apply getbnum_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (getallbnum _ _ _ _ _) _) => apply getallbnum_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (grow _ _ _ _ _ _ _) _) => apply grow_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (shrink _ _ _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (reset _ _ _ _ _ _ _ _) _) => apply reset_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (getowner _ _ _ _ _) _) => apply getowner_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (setowner _ _ _ _ _ _) _) => apply setowner_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ _ _ _) (rep _ _ _ _ _ _)) => constructor : okToUnify.


  Lemma inode_rep_bn_valid_piff : forall bxp IFs xp l c dm,
    rep bxp IFs xp l c dm <=p=> rep bxp IFs xp l c dm *
      [[ forall inum, inum < length l ->
         Forall (fun a => BALLOCC.bn_valid bxp (# a) ) (IBlocks (selN l inum inode0)) ]].
  Proof.
    intros; split;
    unfold pimpl; intros; pred_apply;
    unfold rep in H; destruct_lift H; cancel.
    extract at inum.
    unfold inode_match in H.
    erewrite selN_combine in H; eauto.
    destruct_lifts; eauto.
    Unshelve. exact emp.
  Qed.

  Lemma inode_rep_bn_nonzero_pimpl : forall bxp IFs xp l c dm,
    rep bxp IFs xp l c dm =p=> rep bxp IFs xp l c dm *
      [[ forall inum off, inum < length l ->
         off < length (IBlocks (selN l inum inode0)) ->
         # (selN (IBlocks (selN l inum inode0)) off $0) <> 0 ]].
  Proof.
    intros.
    setoid_rewrite inode_rep_bn_valid_piff at 1; cancel.
    specialize (H1 _ H).
    rewrite Forall_forall in H1.
    eapply H1; eauto.
    apply in_selN; eauto.
  Qed.

  Lemma crash_xform_inode_match : forall xp Fs a,
    crash_xform (inode_match xp Fs a) <=p=> inode_match xp Fs a.
  Proof.
    unfold inode_match; split.
    xform_norm.
    rewrite Ind.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Ind.xform_rep; cancel.
  Qed.

End INODE.