Require Import List.
Require Import Prog.
Require Import FMapList.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred.
Require Import Hoare.
Require Import GenSep.
Require Import SepAuto.
Require Import BasicProg.

Module Map := FMapList.Make(Addr_as_OT).

Import ListNotations.
Set Implicit Arguments.

Definition cachestate := Map.t valu.
Definition cs_empty := Map.empty valu.

Record xparams := {
  MaxCacheBlocks : addr
}.

Module BUFCACHE.

  Definition rep (cs : cachestate) (l : list valuset) :=
    (array $0 l $1 * [[ forall a v, Map.MapsTo a v cs -> fst (sel l a ($0, nil)) = v ]])%pred.

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
      v <- ArrayRead $0 a $1;
      rx (Map.add a v cs, v)
    end.

  Definition write T xp a v (cs : cachestate) rx : prog T :=
    cs <- trim xp cs;
    ArrayWrite $0 a $1 v;;
    rx (Map.add a v cs).

  Lemma mapsto_add : forall a v v' (m : cachestate),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
  Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; auto).
    congruence.
  Qed.

  Hint Resolve list2mem_ptsto_bounds.
  Hint Resolve Map.remove_3.
  Hint Resolve Map.add_3.
  Hint Resolve list2mem_upd.
  Hint Resolve mapsto_add.

  Ltac unfold_rep := unfold rep.

  Theorem trim_ok : forall xp cs,
    {< l,
    PRE      rep cs l
    POST:cs' rep cs' l
    CRASH    rep cs l
    >} trim xp cs.
  Proof.
    unfold trim, rep; hoare.
    destruct (Map.elements cs); hoare.
    destruct p0; hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (trim _ _) _) => apply trim_ok : prog.

  Theorem read_ok : forall xp cs a,
    {< l F v,
    PRE      rep cs l * [[ (F * a |~> v)%pred (list2mem l) ]]
    POST:csv rep (fst csv) l * [[ snd csv = v ]]
    CRASH    rep cs l
    >} read xp a cs.
  Proof.
    unfold read.
    hoare_unfold unfold_rep.

    apply list2mem_sel with (def:=($0,nil)) in H as H'.
    destruct (Map.find a r_) eqn:Hfind; hoare.

    apply Map.find_2 in Hfind. apply H8 in Hfind. rewrite <- H' in Hfind. firstorder.
    destruct (weq a a0); subst; eauto.

    (* Some kind of Coq bug??  [rewrite <- H'] should work.. *)
    assert (w = fst (w, l)); auto.
    rewrite H0.
    rewrite H'.
    reflexivity.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.

  Theorem write_ok : forall xp cs a v,
    {< l F v0,
    PRE      rep cs l * [[ (F * a |~> v0)%pred (list2mem l) ]]
    POST:cs' exists l',
             rep cs' l' * [[ (F * a |~> v)%pred (list2mem l') ]]
    CRASH    rep cs l \/
             exists cs' l',
             rep cs' l' * [[ (F * a |~> v)%pred (list2mem l') ]]
    >} write xp a v cs.
  Proof.
    unfold write.
    hoare_unfold unfold_rep.

    destruct (weq a a0); subst.
    autorewrite_fast; eauto.
    rewrite sel_upd_ne; eauto.

    apply pimpl_or_r. right. cancel; eauto.
    instantiate (a:=(Map.add a v cs)).
    destruct (weq a a0); subst.
    autorewrite_fast; eauto.
    rewrite sel_upd_ne; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.

End BUFCACHE.
