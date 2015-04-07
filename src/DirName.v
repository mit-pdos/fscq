Require Import Word.
Require Import Ascii.
Require Import String.
Require Import Dir.
Require Import Omega.
Require Import Prog.
Require Import BasicProg.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.
Require Import Log.
Require Import BFile.
Require Import GenSep.
Require Import GenSepN.
Require Import ListPred.
Require Import MemMatch.
Require Import FunctionalExtensionality.
Require List.

Set Implicit Arguments.

Definition ifw {len} (b : bool) (bitpos : word len) : word len :=
  if b then wbit _ bitpos else $0.

Definition ascii2byte (a : ascii) : word 8 :=
  match a with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
    ifw a1 $0 ^+
    ifw a2 $1 ^+
    ifw a3 $2 ^+
    ifw a4 $3 ^+
    ifw a5 $4 ^+
    ifw a6 $5 ^+
    ifw a7 $6 ^+
    ifw a8 $7
  end.

Definition wbitset {len} (bitpos : word len) (w : word len) : bool :=
  if weq (wand w (wbit _ bitpos)) $0 then false else true.

Definition byte2ascii (b : word 8) : ascii :=
  Ascii (wbitset $0 b)
        (wbitset $1 b)
        (wbitset $2 b)
        (wbitset $3 b)
        (wbitset $4 b)
        (wbitset $5 b)
        (wbitset $6 b)
        (wbitset $7 b).

Theorem ascii2byte2ascii : forall a,
  byte2ascii (ascii2byte a) = a.
Proof.
  destruct a.
  destruct b; destruct b0; destruct b1; destruct b2;
  destruct b3; destruct b4; destruct b5; destruct b6; reflexivity.
Qed.

Theorem byte2ascii2byte : forall b,
  ascii2byte (byte2ascii b) = b.
Proof.
  intros.
  shatter_word b.
  destruct x; destruct x0; destruct x1; destruct x2;
  destruct x3; destruct x4; destruct x5; destruct x6; reflexivity.
Qed.

Fixpoint name2padstring (nbytes : nat) (name : word (nbytes * 8)) : string.
  destruct nbytes.
  refine EmptyString.
  refine (String (byte2ascii (@split1 8 (nbytes * 8) name))
                 (name2padstring nbytes (@split2 8 (nbytes * 8) name))).
Defined.

Fixpoint padstring2name (nbytes : nat) (s : string) : word (nbytes * 8).
  destruct nbytes.
  refine ($0).
  destruct s.
  refine ($0).
  refine (combine (ascii2byte a) (padstring2name nbytes s)).
Defined.

Opaque ascii2byte byte2ascii split1 split2.

Theorem name2padstring2name : forall nbytes (name : word (nbytes * 8)),
  padstring2name nbytes (name2padstring nbytes name) = name.
Proof.
  induction nbytes; simpl; intros.
  rewrite word0. reflexivity.
  rewrite byte2ascii2byte. rewrite IHnbytes. rewrite combine_split. reflexivity.
Qed.

Theorem padstring2name2padstring : forall nbytes (s : string),
  length s = nbytes -> name2padstring nbytes (padstring2name nbytes s) = s.
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; congruence.
  destruct s; simpl in *; try congruence.
  rewrite split1_combine.
  rewrite split2_combine.
  rewrite IHnbytes by congruence.
  rewrite ascii2byte2ascii.
  reflexivity.
Qed.

Theorem name2padstring_length : forall nbytes name,
  length (name2padstring nbytes name) = nbytes.
Proof.
  induction nbytes; simpl; eauto.
Qed.

Fixpoint string_pad nbytes (s : string) :=
  match nbytes with
  | O => EmptyString
  | S nbytes' =>
    match s with
    | EmptyString => String zero (string_pad nbytes' EmptyString)
    | String a s' => String a (string_pad nbytes' s')
    end
  end.

Fixpoint string_unpad (s : string) :=
  match s with
  | EmptyString => EmptyString
  | String a s' =>
    if ascii_dec a zero then EmptyString else String a (string_unpad s')
  end.

Theorem string_pad_length : forall nbytes s,
  length (string_pad nbytes s) = nbytes.
Proof.
  induction nbytes; simpl.
  reflexivity.
  destruct s; simpl; eauto.
Qed.

Inductive nozero : string -> Prop :=
  | NoZeroEmpty : nozero EmptyString
  | NoZeroCons : forall a s, a <> zero -> nozero s -> nozero (String a s).

Theorem string_pad_unpad : forall nbytes s,
  length s <= nbytes -> nozero s -> string_unpad (string_pad nbytes s) = s.
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; try congruence; omega.
  destruct s; simpl in *; try congruence.
  inversion H0.
  destruct (ascii_dec a zero); try congruence.
  rewrite IHnbytes; eauto.
  omega.
Qed.

Inductive zerostring : string -> Prop :=
  | ZeroEmpty : zerostring EmptyString
  | ZeroCons : forall s, zerostring s -> zerostring (String zero s).

Inductive wellformedpadstring : string -> Prop :=
  | WFSzero : forall s, zerostring s -> wellformedpadstring s
  | WFScons : forall s c, wellformedpadstring s -> c <> zero
                       -> wellformedpadstring (String c s).

Theorem pad_zero_string : forall s, 
  wellformedpadstring (String zero s)
  -> s = string_pad (length s) EmptyString.
Proof.
  intros.
  inversion H; clear H; try congruence.
  clear H1 s0.
  inversion H0; clear H0; subst.
  induction s; simpl.
  reflexivity.
  inversion H1; subst.
  f_equal.
  apply IHs; auto.
Qed.

Theorem string_unpad_pad : forall s nbytes,
  length s = nbytes
  -> wellformedpadstring s
  -> string_pad nbytes (string_unpad s) = s.
Proof.
  induction s; intros; subst; simpl in *.
  reflexivity.
  destruct (ascii_dec a zero); subst.
  - f_equal.
    rewrite <- pad_zero_string; auto.
  - inversion H0.
    inversion H; congruence.
    rewrite IHs; auto.
Qed.

Definition string2name nbytes s := padstring2name nbytes (string_pad nbytes s).
Definition name2string nbytes name := string_unpad (name2padstring nbytes name).

Theorem string2name2string : forall nbytes s,
  length s <= nbytes
  -> nozero s
  -> name2string nbytes (string2name nbytes s) = s.
Proof.
  unfold string2name, name2string.
  intros.
  rewrite padstring2name2padstring by apply string_pad_length.
  rewrite string_pad_unpad; eauto.
Qed.

Theorem name2string2name : forall nbytes name,
  wellformedpadstring (name2padstring nbytes name)
  -> string2name nbytes (name2string nbytes name) = name.
Proof.
  unfold string2name, name2string.
  intros.
  rewrite string_unpad_pad; auto.
  rewrite name2padstring2name; auto.
  apply name2padstring_length.
Qed.

Lemma zerostring_pad_empty : forall n,
  zerostring (string_pad n EmptyString).
Proof.
  induction n; simpl; intros; constructor; auto.
Qed.

Lemma stringpad_wellformed : forall s nbytes,
  length s <= nbytes
  -> nozero s
  -> wellformedpadstring (string_pad nbytes s).
Proof.
  induction s; destruct nbytes eqn:Hn; simpl; intros.
  repeat constructor.
  repeat constructor.
  apply zerostring_pad_empty.
  repeat constructor.
  apply WFScons.
  apply IHs.
  omega.
  inversion H0; auto.
  inversion H0; auto.
Qed.

Lemma wellformedpadstring_inv : forall c s,
  wellformedpadstring (String c s)
  -> c <> zero
  -> wellformedpadstring s.
Proof.
  intros.
  inversion H; auto.
  exfalso; apply H0.
  inversion H1; auto.
Qed.

Lemma wellformed_nozero : forall nbytes s,
  wellformedpadstring (name2padstring nbytes s)
  -> nozero (string_unpad (name2padstring nbytes s)).
Proof.
  induction nbytes; intros.
  constructor.
  simpl.
  destruct (ascii_dec (byte2ascii (split1 8 (nbytes * 8) s)) zero) eqn:Heq.
  constructor.
  apply NoZeroCons; auto.
  apply IHnbytes.
  simpl in H.
  eapply wellformedpadstring_inv; eauto.
Qed.

Lemma string_unpad_length : forall s,
  length (string_unpad s) <= length s.
Proof.
  induction s; simpl; firstorder.
  destruct (ascii_dec a zero); simpl; omega.
Qed.

Lemma name2padstring_unpad_length : forall nbytes s,
  length (string_unpad (name2padstring nbytes s)) <= nbytes.
Proof.
  intros.
  erewrite <- name2padstring_length with (name := s).
  apply string_unpad_length.
Qed.


Module SDIR.

  Definition namelen := Dir.filename_len / 8.

  Definition wname := filename.
  Definition sname := string.

  Inductive wname_valid : wname -> Prop :=
    | WNameValid : forall w, 
        wellformedpadstring (name2padstring namelen w) -> wname_valid w.

  Inductive sname_valid : sname -> Prop :=
    | SNameValid : forall s, 
        length s <= namelen -> nozero s -> sname_valid s
    .

  Definition sname2wname := string2name namelen.
  Definition wname2sname := name2string namelen.

  Lemma wname_valid_sname_valid : forall x,
    wname_valid x -> sname_valid (wname2sname x).
  Proof.
    intros; inversion H.
    constructor.
    apply name2padstring_unpad_length.
    apply wellformed_nozero; auto.
  Qed.

  Lemma sname_valid_wname_valid : forall x,
    sname_valid x -> wname_valid (sname2wname x).
  Proof.
    intros; inversion H.
    constructor.
    unfold sname2wname, string2name.
    rewrite padstring2name2padstring.
    apply stringpad_wellformed; auto.
    apply string_pad_length.
  Qed.

  Theorem dirname_cond_inverse :
    cond_inverse wname2sname wname_valid sname_valid sname2wname.
  Proof.
    split; [split | split ].
    apply wname_valid_sname_valid; auto.
    apply name2string2name.
    inversion H; auto.
    apply sname_valid_wname_valid; auto.
    inversion H.
    apply string2name2string; auto.
  Qed.

  Theorem dirname_cond_inverse' :
    cond_inverse sname2wname sname_valid wname_valid wname2sname.
  Proof.
    apply cond_inverse_sym.
    apply dirname_cond_inverse.
  Qed.

  Theorem wname2sname_bijective :
    cond_bijective wname2sname wname_valid sname_valid.
  Proof.
    eapply cond_inv2bij.
    apply dirname_cond_inverse.
  Qed.

  Theorem sname2wname_bijective :
    cond_bijective sname2wname sname_valid wname_valid.
  Proof.
    eapply cond_inv2bij.
    apply dirname_cond_inverse'.
  Qed.

  Local Hint Resolve dirname_cond_inverse.
  Local Hint Resolve dirname_cond_inverse'.
  Local Hint Resolve wname2sname_bijective.
  Local Hint Resolve sname2wname_bijective.


  Fixpoint is_nozero (s : string) : bool :=
    match s with
    | EmptyString => true
    | String c s => if (ascii_dec c zero) then false else (is_nozero s)
    end.

  Theorem is_nozero_nozero : forall s,
    is_nozero s = true <-> nozero s.
  Proof.
    induction s.
    intuition; constructor.

    simpl.
    destruct (ascii_dec a zero); split; intros.
    inversion H.
    inversion H.
    exfalso; auto.
    constructor; auto.
    apply IHs; auto.
    inversion H.
    apply IHs; auto.
  Qed.

  Definition is_valid_sname s : bool :=
    andb (is_nozero s) (if (le_dec (String.length s) namelen) then true else false).

  Theorem is_valid_sname_valid : forall s,
    is_valid_sname s = true <-> sname_valid s.
  Proof.
    unfold is_valid_sname; intros.
    rewrite Bool.andb_true_iff.

    split; intros.
    destruct H.
    constructor.
    destruct (le_dec (length s) namelen); simpl; try congruence.
    apply is_nozero_nozero; auto.

    inversion H; split.
    apply is_nozero_nozero; auto.
    destruct (le_dec (length s) namelen); simpl; try congruence.
  Qed.

  Fixpoint is_zerostring (s : string) : bool :=
    match s with
    | EmptyString => true
    | String a s' => if (ascii_dec a zero) then (is_zerostring s') else false
    end.

  Fixpoint is_valid_wname (s : string) : bool :=
    match s with
    | EmptyString => true
    | String a s =>
        if (ascii_dec a zero) then is_zerostring s
        else is_valid_wname s
    end.

  Lemma is_zerostring_zerostring : forall s,
    is_zerostring s = true <-> zerostring s.
  Proof.
    induction s; simpl; intros; auto.
    split; try constructor; auto.
    destruct (ascii_dec a zero); subst; simpl; split; intros.
    constructor; apply IHs; auto.
    inversion H; apply IHs; auto.
    inversion H.
    inversion H; exfalso.
    apply n; auto.
  Qed.

  Lemma is_valid_wname_valid' : forall w,
    is_valid_wname(name2padstring namelen w) = true
    <-> wellformedpadstring (name2padstring namelen w).
  Proof.
    generalize namelen.
    induction n; intros; simpl.
    split; repeat constructor.

    destruct (ascii_dec (byte2ascii (split1 8 (n * 8) w)) zero) eqn:Heq;
      simpl; split; try rewrite Heq; try rewrite e; intros; auto.
    repeat constructor.
    apply is_zerostring_zerostring; auto.
    inversion H; inversion H0; try congruence.
    apply is_zerostring_zerostring; auto.
    apply WFScons; auto.
    apply IHn; auto.
    apply IHn.
    eapply wellformedpadstring_inv; eauto.
  Qed.

  Lemma is_valid_wname_valid : forall w,
    is_valid_wname (name2padstring namelen w) = true
    <-> wname_valid w.
  Proof.
    split; intros.
    constructor; apply is_valid_wname_valid'; auto.
    inversion H; apply is_valid_wname_valid'; auto.
  Qed.

  Lemma wname_valid_dec : forall w,
    wname_valid w \/ ~ wname_valid w.
  Proof.
    intros.
    destruct (is_valid_wname (name2padstring namelen w)) eqn:Heq.
    left; apply is_valid_wname_valid; auto.
    right; intro; contradict Heq.
    apply is_valid_wname_valid in H; congruence.
  Qed.

  Lemma sname_valid_dec : forall s,
    sname_valid s \/ ~ sname_valid s.
  Proof.
    intros.
    destruct (is_valid_sname s) eqn:Heq.
    left; apply is_valid_sname_valid; auto.
    right; intro; contradict Heq.
    apply is_valid_sname_valid in H; congruence.
  Qed.

  Local Hint Resolve wname_valid_dec.
  Local Hint Resolve sname_valid_dec.

  Ltac resolve_valid_preds :=
    match goal with
    | [ H: is_valid_wname _ = true |- _ ] => apply is_valid_wname_valid in H
    | [ H: is_valid_sname _ = true |- _ ] => apply is_valid_sname_valid in H
    | [ H: is_valid_wname _ = true -> False |- _ ] =>
         rewrite is_valid_wname_valid in H
    | [ H: is_valid_sname _ = true -> False |- _ ] =>
         rewrite is_valid_sname_valid in H
    end.

  Definition dslookup T lxp bxp ixp dnum name mscs rx : prog T :=
    If (Bool.bool_dec (is_valid_sname name) true) {
      let^ (mscs, r) <- DIR.dlookup lxp bxp ixp dnum (sname2wname name) mscs;
      rx ^(mscs, r)
    } else {
      rx ^(mscs, None)
    }.

  Definition dsunlink T lxp bxp ixp dnum name mscs rx : prog T :=
    If (Bool.bool_dec (is_valid_sname name) true) {
      let^ (mscs, r) <- DIR.dunlink lxp bxp ixp dnum (sname2wname name) mscs;
      rx ^(mscs, r)
    } else {
      rx ^(mscs, false)
    }.

  Definition dslink T lxp bxp ixp dnum name inum isdir mscs rx : prog T :=
    If (Bool.bool_dec (is_valid_sname name) true) {
      let^ (mscs, r) <- DIR.dlink lxp bxp ixp dnum (sname2wname name) inum isdir mscs;
      rx ^(mscs, r)
    } else {
      rx ^(mscs, false)
    }.

  Definition dslist_trans (di : DIR.dlistent) :=
    (wname2sname (fst di), snd di).

  Definition dslist T lxp bxp ixp dnum mscs rx : prog T :=
    let^ (mscs, r) <- DIR.dlist lxp bxp ixp dnum mscs;
    rx ^(mscs, List.map dslist_trans r).

  Definition rep f (dsmap : @mem string string_dec (addr * bool)) : Prop :=
    exists dmap, DIR.rep f dmap
    /\ (forall w, indomain w dmap -> wname_valid w)
    /\ (forall s, indomain s dsmap -> sname_valid s)
    /\ mem_atrans wname2sname dmap dsmap wname_valid.

  Definition rep_macro F1 F2 m bxp ixp (inum : addr) dsmap : Prop :=
    exists flist f,
    (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) /\
    (F2 * #inum |-> f)%pred (list2nmem flist) /\
    rep f dsmap.

  Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 -> rep f m2 -> m1 = m2.
  Proof.
    unfold rep, mem_atrans; intros.
    repeat deex.
    pose proof (DIR.rep_mem_eq H1 H3); subst.
    apply functional_extensionality; intro s.
    destruct (sname_valid_dec s).

    replace s with (wname2sname (sname2wname s)).
    rewrite <- H7. rewrite <- H4. auto.
    eapply cond_inv_domain_right with (f' := sname2wname); eauto.
    eapply cond_inv_domain_right with (f' := sname2wname); eauto.
    eapply cond_inv_rewrite_right; eauto.

    assert (notindomain s m1).
    destruct (indomain_dec s m1); eauto.
    apply H5 in i; congruence.
    assert (notindomain s m2).
    destruct (indomain_dec s m2); eauto.
    apply H2 in i; congruence.
    congruence.
  Qed.

  Local Hint Unfold rep rep_macro DIR.rep_macro: hoare_unfold.

  Theorem dslookup_ok : forall lxp bxp ixp dnum name mscs,
    {< F F1 A mbase m dsmap,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ rep_macro F1 A m bxp ixp dnum dsmap ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           ((exists inum isdir DF,
             [[ r = Some (inum, isdir) /\ (DF * name |-> (inum, isdir))%pred dsmap ]]) \/
            ([[ r = None /\ notindomain name dsmap ]]))
    CRASH  LOG.would_recover_old lxp F mbase
    >} dslookup lxp bxp ixp dnum name mscs.
  Proof.
    unfold dslookup.
    hoare.

    apply pimpl_or_r; left; cancel.
    resolve_valid_preds.
    unfold pimpl; intros.
    eapply mem_atrans_inv_ptsto; eauto.

    apply pimpl_or_r; right; cancel.
    resolve_valid_preds.
    eapply mem_atrans_inv_notindomain; eauto.

    apply pimpl_or_r; right; cancel.
    apply notindomain_not_indomain; intro.
    resolve_valid_preds; auto.
  Qed.


  Definition dslistent := (string * (addr * bool))%type.
  Definition dslmatch (de: dslistent) : @pred _ (string_dec) _ :=
    fst de |-> snd de.

  Lemma helper_atrans_dslist : forall l m1 m2
    (LP : listpred DIR.dlmatch l m1)
    (MT  : mem_atrans wname2sname m1 m2 wname_valid)
    (OK  : forall w, indomain w m1 -> wname_valid w)
    (OK2 : forall s, indomain s m2 -> sname_valid s),
    listpred dslmatch (List.map dslist_trans l) m2.
  Proof.
    induction l; simpl; intros.
    eapply mem_atrans_emp; eauto.

    unfold dslmatch at 1, dslist_trans at 1; simpl.
    apply mem_except_ptsto; auto.
    eapply mem_atrans_indomain; eauto.
    eapply sep_star_ptsto_indomain; eauto.
    eapply ptsto_valid; eauto.

    apply sep_star_ptsto_indomain in LP as Hx.
    eapply ptsto_mem_except in LP.
    eapply IHl; eauto.
    apply OK in Hx.
    eapply mem_atrans_mem_except; eauto.

    intros; apply OK.
    eapply indomain_mem_except_indomain; eauto.
    intros; apply OK2.
    eapply indomain_mem_except_indomain; eauto.
  Qed.


  Theorem dslist_ok : forall lxp bxp ixp dnum mscs,
    {< F F1 A mbase m dsmap,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ rep_macro F1 A m bxp ixp dnum dsmap ]]
    POST RET:^(mscs,res)
             LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ listpred dslmatch res dsmap ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} dslist lxp bxp ixp dnum mscs.
  Proof.
    unfold dslist.
    hoare.
    eapply helper_atrans_dslist; eauto.
  Qed.


  Theorem dsunlink_ok : forall lxp bxp ixp dnum name mscs,
    {< F F1 A mbase m dsmap,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ rep_macro F1 A m bxp ixp dnum dsmap ]]
    POST RET:^(mscs,r) exists m' dsmap',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ rep_macro F1 A m' bxp ixp dnum dsmap' ]] *
             [[ dsmap' = mem_except dsmap name ]] *
             [[ notindomain name dsmap' ]] *
             [[ r = true -> indomain name dsmap ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} dsunlink lxp bxp ixp dnum name mscs.
  Proof.
    unfold dsunlink.
    hoare; resolve_valid_preds.

    exists x2, x3; repeat split; eauto.
    eexists; split; eauto.
    split; [ | split ]; [ intros ? Hx | intros ? Hx | ].
    apply indomain_mem_except_indomain in Hx; auto.
    apply indomain_mem_except_indomain in Hx; auto.
    eapply mem_ainv_mem_except; eauto.
    apply mem_except_notindomain.
    eapply mem_atrans_inv_indomain; eauto.

    rewrite <- notindomain_mem_eq.
    exists x, x0; repeat split; eauto.
    apply notindomain_not_indomain; eauto.
    apply mem_except_notindomain.
  Qed.


  Theorem dslink_ok : forall lxp bxp ixp dnum name inum isdir mscs,
    {< F F1 A mbase m dsmap,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ rep_macro F1 A m bxp ixp dnum dsmap ]]
    POST RET:^(mscs,r)
            exists m',
            ([[ r = false ]] * LOG.rep lxp F (ActiveTxn mbase m') mscs)
        \/  ([[ r = true ]] * exists dsmap' DF,
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ rep_macro F1 A m' bxp ixp dnum dsmap' ]] *
             [[ dsmap' = Prog.upd dsmap name (inum, isdir) ]] *
             [[ (DF * name |-> (inum, isdir))%pred dsmap' ]] *
             [[ (DF dsmap /\ notindomain name dsmap) ]])
    CRASH    LOG.would_recover_old lxp F mbase
    >} dslink lxp bxp ixp dnum name inum isdir mscs.
  Proof.
    unfold dslink.
    hoare.

    apply pimpl_or_r; right; resolve_valid_preds; cancel.
    exists x2, x3; repeat split; eauto.
    eexists; split; eauto.
    split; [ | split ]; [ intros ? Hx | intros ? Hx | ].

    destruct (weq w (sname2wname name)); subst.
    eapply cond_inv_domain_right with (PA := wname_valid); eauto.
    apply indomain_upd_ne in Hx; auto.
    destruct (string_dec s name); subst; auto.
    apply indomain_upd_ne in Hx; auto.

    eapply mem_ainv_mem_upd; eauto.
    apply any_sep_star_ptsto.
    apply upd_eq; auto.
    unfold any; auto.
    eapply mem_atrans_inv_notindomain; eauto.
  Qed.




  Hint Extern 1 ({{_}} progseq (dslookup _ _ _ _ _ _) _) => apply dslookup_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsunlink _ _ _ _ _ _) _) => apply dsunlink_ok : prog.
  Hint Extern 1 ({{_}} progseq (dslink _ _ _ _ _ _ _ _) _) => apply dslink_ok : prog.
  Hint Extern 1 ({{_}} progseq (dslist _ _ _ _ _) _) => apply dslist_ok : prog.


  Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.
  Proof.
    unfold rep.
    exists empty_mem.
    intuition.
    apply DIR.bfile0_empty.
    inversion H; discriminate.
    inversion H; discriminate.
    firstorder.
  Qed.


End SDIR.
