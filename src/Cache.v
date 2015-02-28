Require Import List.
Require Import Prog.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.

Module Map := FMapAVL.Make(Addr_as_OT).

Import ListNotations.
Set Implicit Arguments.

Record cachestate := {
  CSMap : Map.t valu;
  CSCount : addr;  (* current number of items, for efficient capacity checks *)
  CSMaxCount : addr
}.

Module BUFCACHE.

  Definition rep (cs : cachestate) (m : @mem addr (@weq addrlen) valuset) :=
    (diskIs m *
     [[ Map.cardinal (CSMap cs) = # (CSCount cs) ]] *
     [[ (CSCount cs <= CSMaxCount cs)%word ]] *
     [[ CSMaxCount cs <> $0 ]] *
     [[ forall a v, Map.MapsTo a v (CSMap cs) -> exists old, m a = Some (v, old) ]])%pred.

  Definition trim T (cs : cachestate) rx : prog T :=
    If (wlt_dec (CSCount cs) (CSMaxCount cs)) {
      rx cs
    } else {
      match (Map.elements (CSMap cs)) with
      | nil => rx cs
      | (a,v) :: tl => rx (Build_cachestate (Map.remove a (CSMap cs)) (CSCount cs ^- $1) (CSMaxCount cs))
      end
    }.

  Definition read T a (cs : cachestate) rx : prog T :=
    cs <- trim cs;
    match Map.find a (CSMap cs) with
    | Some v => rx (cs, v)
    | None =>
      v <- Read a;
      rx (Build_cachestate (Map.add a v (CSMap cs)) (CSCount cs ^+ $1) (CSMaxCount cs), v)
    end.

  Definition write T a v (cs : cachestate) rx : prog T :=
    cs <- trim cs;
    Write a v;;
    match Map.find a (CSMap cs) with
    | Some _ =>
      rx (Build_cachestate (Map.add a v (CSMap cs)) (CSCount cs) (CSMaxCount cs))
    | None =>
      rx (Build_cachestate (Map.add a v (CSMap cs)) (CSCount cs ^+ $1) (CSMaxCount cs))
    end.

  Definition sync T a (cs : cachestate) rx : prog T :=
    Sync a;;
    rx cs.

  Definition init T (cachesize : addr) (rx : cachestate -> prog T) : prog T :=
    If (weq cachesize $0) {
      rx (Build_cachestate (Map.empty valu) $0 $1)
    } else {
      rx (Build_cachestate (Map.empty valu) $0 cachesize)
    }.

  Definition read_array T a i cs rx : prog T :=
    r <- read (a ^+ i ^* $1) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a ^+ i ^* $1) v cs;
    rx cs.

  Definition sync_array T a i cs rx : prog T :=
    cs <- sync (a ^+ i ^* $1) cs;
    rx cs.

  Lemma mapsto_add : forall a v v' (m : Map.t valu),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
  Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; auto).
    congruence.
  Qed.

  Lemma map_remove_cardinal : forall V (m : Map.t V) k, Map.In k m ->
    Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
  Proof.
    admit.
  Qed.

  Lemma map_add_cardinal : forall V (m : Map.t V) k v, ~ Map.In k m ->
    Map.cardinal (Map.add k v m) = Map.cardinal m + 1.
  Proof.
    admit.
  Qed.

  Lemma map_elements_hd_in : forall V (m : Map.t V) k w l,
    Map.elements m = (k, w) :: l ->
    Map.In k m.
  Proof.
    intros.
    eexists; apply Map.elements_2.
    rewrite H.
    apply InA_cons_hd.
    constructor; eauto.
  Qed.

  Hint Resolve Map.remove_3.
  Hint Resolve Map.add_3.
  Hint Resolve mapsto_add.

  Ltac unfold_rep := unfold rep.

  Theorem trim_ok : forall cs,
    {< d,
    PRE      rep cs d
    POST:cs' rep cs' d
    CRASH    exists cs', rep cs' d
    >} trim cs.
  Proof.
    unfold trim, rep; hoare.
    destruct cs as [cmap cnum].
    case_eq (Map.elements cmap); hoare.

    rewrite map_remove_cardinal by (eapply map_elements_hd_in; eauto).
    rewrite H6.
    destruct xp; simpl in *.

    rewrite wminus_Alt. rewrite wminus_Alt2. unfold wordBinN.
    erewrite wordToNat_natToWord_bound with (bound:=cnum).
    reflexivity.
    omega.
    intro; apply H8; clear H8.
    apply lt_wlt.
    apply wlt_lt in H0.
    simpl in *.
    case_eq (#MaxCacheBlocks0); intros; try omega.
    rewrite <- H1 in MaxCacheBlocksOK0.
    rewrite natToWord_wordToNat in MaxCacheBlocksOK0.
    congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (trim _) _) => apply trim_ok : prog.

  Theorem read_ok : forall cs a,
    {< d F v,
    PRE          rep cs d * [[ (F * a |~> v)%pred d ]]
    POST:(cs',r) rep cs' d * [[ r = v ]]
    CRASH        exists cs', rep cs' d
    >} read a cs.
  Proof.
    unfold read.
    hoare_unfold unfold_rep.

    apply sep_star_comm in H3.
    apply ptsto_valid in H3 as H'.
    destruct (Map.find a (fst r_)) eqn:Hfind; hoare.

    apply Map.find_2 in Hfind. apply H9 in Hfind. rewrite H' in Hfind. deex; congruence.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.

    admit.

    destruct (weq a a0); subst.
    apply mapsto_add in H; subst; eauto.
    edestruct H9. eauto. eexists; eauto.

    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.

  Theorem write_ok : forall cs a v,
    {< d F v0,
    PRE      rep cs d * [[ (F * a |-> v0)%pred d ]]
    POST:cs' exists d',
             rep cs' d' * [[ (F * a |-> (v, valuset_list v0))%pred d' ]]
    CRASH    exists cs', rep cs' d \/
             exists d', rep cs' d' * [[ (F * a |-> (v, valuset_list v0))%pred d' ]]
    >} write a v cs.
  Proof.
    unfold write.
    hoare_unfold unfold_rep.

    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    destruct (Map.find a (fst r_)); hoare.

    rewrite <- diskIs_combine_upd with (m:=m); try pred_apply; cancel.
    admit.
    destruct (weq a a0); subst.
    apply mapsto_add in H; subst.
    rewrite upd_eq by auto. eauto.
    apply Map.add_3 in H; auto.
    rewrite upd_ne by auto. auto.

    apply sep_star_comm; apply sep_star_comm in H3.
    eapply ptsto_upd; pred_apply; cancel.

    rewrite <- diskIs_combine_upd with (m:=m); cancel.
    admit.

    destruct (weq a a0); subst.
    apply mapsto_add in H; subst.
    rewrite upd_eq by auto. eauto.
    apply Map.add_3 in H; auto.
    rewrite upd_ne by auto. auto.

    apply sep_star_comm; apply sep_star_comm in H3.
    eapply ptsto_upd; pred_apply; cancel.

    cancel.
    instantiate (a2 := r_).
    apply pimpl_or_r. left. cancel.
    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.

    apply pimpl_or_r. left. cancel.
    eauto.
    eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.

  Theorem sync_ok : forall a cs,
    {< d F v,
    PRE      rep cs d * [[ (F * a |-> v)%pred d ]]
    POST:cs' exists d', rep cs' d' * [[ (F * a |-> (fst v, nil))%pred d' ]]
    CRASH    exists cs', rep cs' d \/
             exists d', rep cs' d' * [[ (F * a |-> (fst v, nil))%pred d' ]]
    >} sync a cs.
  Proof.
    unfold sync, rep.
    step.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    eapply pimpl_ok2; eauto with prog.
    intros; norm.
    instantiate (a := Prog.upd m a (w, [])); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=m); cancel.
    intuition.
    apply H5 in H; deex.
    destruct (weq a a0); subst.
    apply sep_star_comm in H3; apply ptsto_valid in H3.
    rewrite H3 in H. inversion H. subst.
    rewrite upd_eq by auto. eexists. eauto.
    rewrite upd_ne by auto. eexists. eauto.
    apply sep_star_comm. eapply ptsto_upd. apply sep_star_comm. eauto.
    cancel.
    apply pimpl_or_r; left.
    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.
    eauto.
    eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

  Theorem init_ok : forall cachesize,
    {< F,
    PRE      F
    POST:cs  exists d, rep cs d * [[ F d ]]
    CRASH    F
    >} init cachesize.
  Proof.
    unfold init, rep.
    step.

    eapply pimpl_ok2; eauto.
    simpl; intros.

    (* XXX is there a way to avoid this whole hack? *)
    match goal with
    | [ |- _ =p=> _ * ?E * [[ _ = _ ]] * [[ _ = _ ]] ] =>
      remember (E)
    end.
    norm; cancel'; intuition.
    unfold stars; subst; simpl; rewrite star_emp_pimpl.
    unfold pimpl; intros; exists m.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    congruence.
    intros.
    contradict H0; apply Map.empty_1.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _) _) => apply init_ok : prog.

  Theorem read_array_ok : forall a i cs,
    {< d F vs,
    PRE          rep cs d * [[ (F * array a vs $1)%pred d ]] * [[ #i < length vs ]]
    POST:(cs',v) rep cs' d * [[ v = fst (sel vs i ($0, nil)) ]]
    CRASH        exists cs', rep cs' d
    >} read_array a i cs.
  Proof.
    unfold read_array.
    hoare.
    rewrite isolate_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _) _) => apply read_array_ok : prog.

  Theorem write_array_ok : forall a i v cs,
    {< d F vs,
    PRE      rep cs d * [[ (F * array a vs $1)%pred d ]] * [[ #i < length vs ]]
    POST:cs' exists d', rep cs' d' *
             [[ (F * array a (upd_prepend vs i v) $1)%pred d' ]]
    CRASH    exists cs', rep cs' d \/
             exists d', rep cs' d' * [[ (F * array a (upd_prepend vs i v) $1)%pred d' ]]
    >} write_array a i v cs.
  Proof.
    unfold write_array, upd_prepend.
    hoare.

    pred_apply.
    rewrite isolate_fwd with (i:=i) by auto.
    cancel.

    rewrite <- isolate_bwd_upd by auto.
    cancel.

    apply pimpl_or_r; right; cancel.
    rewrite <- isolate_bwd_upd by auto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _) _) => apply write_array_ok : prog.

  Theorem sync_array_ok : forall a i cs,
    {< d F vs,
    PRE      rep cs d * [[ (F * array a vs $1)%pred d ]] * [[ #i < length vs ]]
    POST:cs' exists d', rep cs' d' *
             [[ (F * array a (upd_sync vs i ($0, nil)) $1)%pred d' ]]
    CRASH    exists cs', rep cs' d \/
             exists d', rep cs' d' * [[ (F * array a (upd_sync vs i ($0, nil)) $1)%pred d' ]]
    >} sync_array a i cs.
  Proof.
    unfold sync_array, upd_sync.
    hoare.

    pred_apply.
    rewrite isolate_fwd with (i:=i) by auto.
    cancel.

    rewrite <- isolate_bwd_upd by auto.
    cancel.

    apply pimpl_or_r; right; cancel.
    rewrite <- isolate_bwd_upd by auto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync_array _ _ _) _) => apply sync_array_ok : prog.

  Lemma crash_xform_diskIs: forall (m: @mem addr (@weq addrlen) valuset),
    crash_xform (diskIs m) =p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
  Proof.
    unfold crash_xform, pimpl, diskIs.
    intros.
    destruct H; intuition; subst.
    exists m0.
    unfold_sep_star.
    exists (fun a => None).
    exists m0.
    intuition.
    unfold mem_disjoint; intuition.
    repeat deex; discriminate.
    unfold lift_empty; intuition.
  Qed.

  Lemma crash_xform_rep: forall cs m,
    crash_xform (rep cs m) =p=> exists m' cs', [[ possible_crash m m' ]] * rep cs' m'.
  Proof.
    unfold rep.
    intros.
    repeat rewrite crash_xform_sep_star_dist.
    rewrite crash_xform_diskIs.
    repeat rewrite crash_xform_lift_empty.
    cancel.
    instantiate (a0 := (Map.empty valu, $0)).
    auto.
    inversion H.
  Qed.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.
End BUFCACHE.

Global Opaque BUFCACHE.init.
