Require Import EventCSL.
Require Import EventCSLauto.
Require Import Automation.
Require Import Locking.
Require Import MemCache.
Require Import ConcurrentCache.
Require Import Star.
Require Import Rec.
Import PeanoNat.
Require Import Array.
Require Import Omega.
Import List.
Import List.ListNotations.

Open Scope list.

Set Implicit Arguments.

Section Attributes.

Definition iattrtype : Rec.type := Rec.RecF ([
  ("size",   Rec.WordF addrlen)  (* file size in bytes *)
]).

Definition iarec  := Rec.data iattrtype.
Definition iarec0 : iarec := Rec.of_word $0.

Record iattr := {
  ISize : addr
}.

Definition pack_attr ia := Eval compute in
  iarec0 :=> "size" := ISize ia.

Definition unpack_attr (ia: iarec) := Eval compute in
  Build_iattr (ia :-> "size").

Theorem pack_unpack : forall a,
  pack_attr (unpack_attr a) = a.
Proof.
  destruct a, u; auto.
Qed.

Theorem unpack_pack : forall a,
  unpack_attr (pack_attr a) = a.
Proof.
  destruct a; auto.
Qed.

End Attributes.

Section Inodes.

Definition nr_direct := Eval cbn in (valulen-128)/64.

Definition inodetype : Rec.type := Rec.RecF ([
  ("len", Rec.WordF addrlen);
  ("attr", iattrtype);
  ("blocks", Rec.ArrayF (Rec.WordF addrlen) nr_direct)
]).

Remark inodetype_len : Rec.len inodetype = valulen.
Proof. reflexivity. Qed.

Definition irec := Rec.data inodetype.
Definition irec0 : irec := Rec.of_word $0.

Record inode := {
  IBlocks : list addr;
  IAttr : iattr
}.

Definition pad A (l:list A) (a:A) n :=
  l ++ repeat a (n - length l).

Lemma pad_length : forall A l (a:A) n,
  length l <= n ->
  length (pad l a n) = n.
Proof.
  intros.
  unfold pad.
  rewrite app_length.
  rewrite repeat_length.
  omega.
Qed.

Lemma firstn_pad : forall A l (a:A) n,
  firstn (length l) (pad l a n) = l.
Proof.
  intros.
  unfold pad.
  auto using firstn_app.
Qed.

Definition inode_to_rec (i:inode) : Rec.data inodetype :=
  irec0 :=> "len" := $ (length (IBlocks i))
        :=> "attr" := pack_attr (IAttr i)
        :=> "blocks" := pad (IBlocks i) $0 nr_direct.

Definition rec_to_inode (i:Rec.data inodetype) : inode :=
  let len := # (i :-> "len") in
    let blocks := i :-> "blocks" in
    let attr := unpack_attr (i :-> "attr") in
    Build_inode (firstn len blocks) attr.

Lemma inode_to_rec_well_formed : forall i,
  length (IBlocks i) <= nr_direct ->
  Rec.well_formed (inode_to_rec i).
Proof.
  intros.
  cbn; intuition.
  apply pad_length; auto.
  apply Forall_forall; auto.
Qed.

Theorem inode_roundtrip : forall i,
  length (IBlocks i) <= nr_direct ->
  rec_to_inode (inode_to_rec i) = i.
Proof.
  intros.
  unfold rec_to_inode, inode_to_rec; cbn.
  destruct i.
  rewrite unpack_pack.
  f_equal.
  cbn [IBlocks] in *.
  rewrite wordToNat_natToWord_idempotent'.
  apply firstn_pad.
  eapply goodSize_trans; eauto.
  unfold goodSize, addrlen, nr_direct.
  assert (62 < pow2 6).
  cbn; eauto.
  pose proof (@pow2_inc 6 64).
  omega.
Qed.

Definition marshal_inode (i:inode) : valu :=
  Rec.to_word (inode_to_rec i).

Definition unmarshal_inode (v:valu) : inode.
Proof.
  rewrite <- inodetype_len in v.
  exact (rec_to_inode (Rec.of_word v)).
Defined.

Theorem marshal_unmarshal : forall i,
  length (IBlocks i) <= nr_direct ->
  unmarshal_inode (marshal_inode i) = i.
Proof.
  unfold unmarshal_inode, marshal_inode; intros.
  eq_rect_simpl.
  rewrite Rec.of_to_id.
  apply inode_roundtrip; auto.
  apply inode_to_rec_well_formed; auto.
Qed.

Fixpoint array_pred V (l:list V) off : @pred addr (@weq addrlen) (const V) :=
  match l with
  | nil => emp
  | a :: l' => off |-> a * array_pred l' (off ^+ $1)
  end.

End Inodes.

Module Type InodeVars (Sem:Semantics).
  Import Sem.
  Parameter memVars : variables Mcontents
    [ nat -> BusyFlag:Type ].

  Parameter stateVars : variables Scontents
    [ list inode:Type;
      nat -> BusyFlagOwner:Type ].
End InodeVars.

Module InodeTransitions (Sem:Semantics)
  (CVars:CacheVars Sem)
  (IVars:InodeVars Sem).

  Module CacheTransitions := CacheTransitionSystem Sem CVars.
  Definition GDisk := CacheTransitions.GDisk.

  Import Sem.
  Import IVars.

  Definition InodeLocks := get HFirst memVars.

  Definition Inodes := get HFirst stateVars.
  Definition InodeLocked := get (HNext HFirst) stateVars.

  Definition get_m_lock inum (m: M Mcontents) : BusyFlag :=
    get InodeLocks m inum.

  Definition get_s_lock inum (s: S Scontents) : BusyFlagOwner :=
    get InodeLocked s inum.

  Definition get_inode inum (s: S Scontents) : option inode :=
    nth_error (get Inodes s) inum.

  Definition inodeR (tid:ID) : Relation Scontents :=
    fun s s' =>
      forall inum,
        lock_protocol (get_s_lock inum) tid s s' /\
        lock_protects (get_s_lock inum) (get_inode inum) tid s s'.

  Definition inodeI : Invariant Mcontents Scontents :=
    fun m s _ =>
      forall inum,
        ghost_lock_invariant (get_m_lock inum m) (get_s_lock inum s) /\
        (exists F,
        (F * array_pred (map
            (fun i => (marshal_inode i, None))
          (get Inodes s)) $0))%pred
          (get GDisk s).

End InodeTransitions.

Module Type InodeSemantics (Sem : Semantics)
  (CVars : CacheVars Sem)
  (IVars : InodeVars Sem).

  Import Sem.
  Import IVars.

  Module ITrans := InodeTransitions Sem CVars IVars.
  Import ITrans.

  Axiom inode_relation_holds : forall tid,
    rimpl (R tid) (inodeR tid).

  Axiom twoblock_relation_preserved : forall tid s s' s'',
    R tid s s' ->
    modified stateVars s' s'' ->
    inodeR tid s' s'' ->
    R tid s s''.

  Axiom inode_invariant_holds : forall d m s,
    Inv d m s ->
    inodeI d m s.

  Axiom inode_invariant_preserved : forall d m s d' m' s',
    Inv m s d ->
    inodeI m' s' d' ->
    m' = m ->
    modified stateVars s s' ->
    Inv m' s' d'.

End InodeSemantics.

Module Inode (Sem:Semantics)
  (CVars:CacheVars Sem)
  (CSem:CacheSemantics Sem CVars)
  (IVars:InodeVars Sem)
  (ISem:InodeSemantics Sem CVars IVars).
  Import Sem.
  Module CacheM := Cache Sem CVars CSem.
  Import CacheM.
  Import CSem.Transitions.
  Import ISem.
  Import ITrans.

  Implicit Type inum:nat. (* an inode number *)
  Implicit Type ino:irec.

  Definition iget {T} inum rx : prog Mcontents Scontents T :=
    inode_val <- locked_async_disk_read ($ inum);
    rx (@Rec.of_word inodetype inode_val).

  Definition iput {T} inum ino rx : prog Mcontents Scontents T :=
    locked_disk_write ($ inum) (Rec.to_word ino);;
    rx tt.

  Definition igrow {T} inum blk rx : prog Mcontents Scontents T :=
    ino <- iget inum;
    let len := ino :-> "len" in
    let blocks := ino :-> "blocks" in
    iput inum (ino :=> "len" := len ^+ $1
                   :=> "blocks" := blocks ++ [blk]);;
    rx tt.

  Definition ishrink {T} inum rx : prog Mcontents Scontents T :=
    ino <- iget inum;
    let len := ino :-> "len" in
    let blk := nth_error (ino :-> "blocks") (# len) in
    iput inum (ino :=> "len" := len ^- $1);;
    rx tt.

End Inode.