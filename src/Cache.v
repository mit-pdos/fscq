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

Module Map := FMapList.Make(Addr_as_OT).

Import ListNotations.
Set Implicit Arguments.

Definition cachestate := Map.t valu.
Definition cs_empty := Map.empty valu.

Module BUFCACHE.

  Definition rep (cs : cachestate) (l : list valu) :=
    (array $0 l $1 * [[ forall a v, Map.MapsTo a v cs -> sel l a $0 = v ]])%pred.

  Definition trim T (cs : cachestate) rx : prog T :=
    rx cs.

  Definition read T a (cs : cachestate) rx : prog T :=
    cs <- trim cs;
    match Map.find a cs with
    | Some v => rx (cs, v)
    | None =>
      v <- ArrayRead $0 a $1;
      rx (Map.add a v cs, v)
    end.

  Definition write T a v (cs : cachestate) rx : prog T :=
    cs <- trim cs;
    ArrayWrite $0 a $1 v;;
    rx (Map.add a v cs).

  Hint Resolve list2mem_ptsto_bounds.
  Ltac unfold_rep := unfold rep.

  Theorem trim_ok : forall cs,
    {< l,
    PRE      rep cs l
    POST:cs' rep cs' l
    CRASH    rep cs l
    >} trim cs.
  Proof.
    unfold trim; hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (trim _) _) => apply trim_ok : prog.

  Theorem read_ok : forall cs a,
    {< l F v,
    PRE      rep cs l * [[ (F * a |-> v)%pred (list2mem l) ]]
    POST:csv rep (fst csv) l * [[ snd csv = v ]]
    CRASH    rep cs l
    >} read a cs.
  Proof.
    unfold read.
    hoare_unfold unfold_rep.

    destruct (Map.find a r_) eqn:Hfind; hoare.

    apply Map.find_2 in Hfind. apply H8 in Hfind.
    apply list2mem_sel with (def:=$0) in H. congruence.

    destruct (weq a a0); subst.
    apply Map.find_1 in H0.
    erewrite Map.find_1 in H0 by (apply Map.add_1; auto).
    inversion H0; subst. reflexivity.
    apply Map.add_3 in H0; eauto.

    apply list2mem_sel with (def:=$0) in H.
    congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.

  Theorem write_ok : forall cs a v,
    {< l F v0,
    PRE      rep cs l * [[ (F * a |-> v0)%pred (list2mem l) ]]
    POST:cs' exists l',
             rep cs' l' * [[ (F * a |-> v)%pred (list2mem l') ]]
    CRASH    rep cs l \/
             exists cs' l',
             rep cs' l' * [[ (F * a |-> v)%pred (list2mem l') ]]
    >} write a v cs.
  Proof.
    unfold write.
    hoare_unfold unfold_rep.

    destruct (weq a a0); subst.
    autorewrite_fast; eauto.
    apply Map.find_1 in H0. erewrite Map.find_1 in H0 by (apply Map.add_1; eauto).
    congruence.
    apply Map.add_3 in H0; eauto.
    rewrite sel_upd_ne; eauto.

    eapply list2mem_upd; eauto.

    apply pimpl_or_r. right. cancel.
    instantiate (a:=(Map.add a v cs)).
    destruct (weq a a0); subst.
    autorewrite_fast; eauto.
    apply Map.find_1 in H0. erewrite Map.find_1 in H0 by (apply Map.add_1; eauto).
    congruence.
    apply Map.add_3 in H0; eauto.
    rewrite sel_upd_ne; eauto.
    eapply list2mem_upd; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.

End BUFCACHE.
