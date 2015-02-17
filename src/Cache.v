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

Module Map := FMapAVL.Make(Addr_as_OT).

Import ListNotations.
Set Implicit Arguments.

Definition cachestate := Map.t valu.

Record xparams := {
  MaxCacheBlocks : addr
}.

Module BUFCACHE.

  Definition rep (cs : cachestate) (m : @mem addr (@weq addrlen) valuset) :=
    (diskIs m * [[ forall a v, Map.MapsTo a v cs -> exists old, m a = Some (v, old) ]])%pred.

  Definition trim T xp (cs : cachestate) rx : prog T :=
    If (wlt_dec $ (Map.cardinal cs) (MaxCacheBlocks xp)) {
      rx cs
    } else {
      match (Map.elements cs) with
      | nil => rx cs
      | (a,v) :: tl => rx (Map.remove a cs)
      end
    }.

  Definition read T xp a (cs : cachestate) rx : prog T :=
    cs <- trim xp cs;
    match Map.find a cs with
    | Some v => rx (cs, v)
    | None =>
      v <- Read a;
      rx (Map.add a v cs, v)
    end.

  Definition write T xp a v (cs : cachestate) rx : prog T :=
    cs <- trim xp cs;
    Write a v;;
    rx (Map.add a v cs).

  Definition init T (xp : xparams) rx : prog T :=
    rx (Map.empty valu).

  Lemma mapsto_add : forall a v v' (m : cachestate),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
  Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; auto).
    congruence.
  Qed.

  Hint Resolve Map.remove_3.
  Hint Resolve Map.add_3.
  Hint Resolve mapsto_add.

  Ltac unfold_rep := unfold rep.

  Theorem trim_ok : forall xp cs,
    {< d,
    PRE      rep cs d
    POST:cs' rep cs' d
    CRASH    exists cs', rep cs' d
    >} trim xp cs.
  Proof.
    unfold trim, rep; hoare.
    destruct (Map.elements cs); hoare.
    destruct p0; hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (trim _ _) _) => apply trim_ok : prog.

  Theorem read_ok : forall xp cs a,
    {< d F v,
    PRE      rep cs d * [[ (F * a |~> v)%pred d ]]
    POST:csv rep (fst csv) d * [[ snd csv = v ]]
    CRASH    exists cs', rep cs' d
    >} read xp a cs.
  Proof.
    unfold read.
    hoare_unfold unfold_rep.

    apply sep_star_comm in H.
    apply ptsto_valid in H as H'.
    destruct (Map.find a r_) eqn:Hfind; hoare.

    apply Map.find_2 in Hfind. apply H8 in Hfind. rewrite H' in Hfind. deex; congruence.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.

    destruct (weq a a0); subst.
    apply mapsto_add in H0; subst; eauto.
    edestruct H8. eauto. eexists; eauto.

    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.

  Theorem write_ok : forall xp cs a v,
    {< d F v0,
    PRE      rep cs d * [[ (F * a |~> v0)%pred d ]]
    POST:cs' exists d',
             rep cs' d' * [[ (F * a |~> v)%pred d' ]]
    CRASH    exists cs', rep cs' d \/
             exists d', rep cs' d' * [[ (F * a |~> v)%pred d' ]]
    >} write xp a v cs.
  Proof.
    unfold write.
    hoare_unfold unfold_rep.

    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    rewrite <- diskIs_combine_upd with (m:=m); try pred_apply; cancel.
    destruct (weq a a0); subst.
    apply mapsto_add in H0; subst.
    rewrite upd_eq by auto. eauto.
    apply Map.add_3 in H0; auto.
    rewrite upd_ne by auto. auto.

    assert ((p * a |-> (v, valuset_list (w, l)))%pred (Prog.upd m a (v, valuset_list (w, l)))).
    apply sep_star_comm; apply sep_star_comm in H.
    eapply ptsto_upd; pred_apply; cancel.
    pred_apply; cancel.

    cancel.
    instantiate (a2 := r_).
    apply pimpl_or_r. left. cancel.
    rewrite <- diskIs_combine_same with (m:=m); try pred_apply; cancel.

    apply pimpl_or_r. left. cancel.
    eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.

  Theorem init_ok : forall xp,
    {< F,
    PRE      F
    POST:cs  exists d, rep cs d * [[ F d ]]
    CRASH    F \/ exists cs' d, rep cs' d * [[ F d ]]
    >} init xp.
  Proof.
    unfold init, rep.
    step.
    2: cancel.

    eapply pimpl_ok2; eauto.
    simpl; intros.

    (* XXX is there a way to avoid this whole hack? *)
    remember (exists d : @mem addr _ valuset,
       diskIs d *
       [[forall (a : Map.key) (v : valu),
         Map.MapsTo a v r_ -> exists old : list valu, d a = Some (v, old)]] * 
       [[p d]])%pred.
    norm; cancel'; intuition.
    unfold stars; subst; simpl; rewrite star_emp_pimpl.
    unfold pimpl; intros; exists m.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    congruence.
    intros.
    contradict H0; apply Map.empty_1.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _) _) => apply init_ok : prog.

End BUFCACHE.

Global Opaque BUFCACHE.init.
