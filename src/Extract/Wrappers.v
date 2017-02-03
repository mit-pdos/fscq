Require Import Cache FSLayout MemLog GroupLog Log BFile.
Require Import GoSemantics GoHoare GoTactics1.
Require Import List.

Import Go.
Import ListNotations.

Instance addrmap_default_value : forall T {H: GoWrapper T}, DefaultValue (Map.t T).
  intros.
  apply Build_DefaultValue with (zeroval := Map.empty _).
  unfold default_value, default_value', wrap, wrap'.
  simpl. repeat f_equal.
  apply MapUtils.addrmap_equal_eq.
  apply MapUtils.AddrMap.map_empty.
  eauto with map.
Defined.

Instance WrapByTransforming_cachestate : WrapByTransforming cachestate.
  refine {|
    transform := fun cs => (CSMap cs, CSMaxCount cs, CSEvict cs);
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.

Instance cachestate_default_value : DefaultValue cachestate := {| zeroval :=
  {| CSMap := Go.Map.empty _; CSMaxCount := 0; CSEvict := tt |} |}.
  unfold wrap, wrap', GoWrapper_transform, default_value. simpl.
  repeat f_equal.
  apply MapUtils.addrmap_equal_eq.
  apply MapUtils.AddrMap.map_empty.
  auto with map.
Defined.

Instance GoWrapper_GLog_mstate : GoWrapper GLog.mstate.
  refine {|
    wrap_type := Go.Struct [
      @wrap_type LogReplay.valumap _;
      @wrap_type DiskSet.txnlist _;
      @wrap_type MLog.mstate _
    ];
    wrap' := fun ms =>
      (wrap' (GLog.MSVMap ms),
      (wrap' (GLog.MSTxns ms),
      (wrap' (GLog.MSMLog ms), tt)))
  |}.

  intros. repeat find_inversion_safe.
  destruct a1, a2; f_equal; eapply wrap_inj; eauto.
Defined.

Instance GLog_mstate_default_value : DefaultValue GLog.mstate.
  refine {|
    zeroval := {|
      GLog.MSVMap := zeroval;
      GLog.MSTxns := zeroval;
      GLog.MSMLog := zeroval
    |}
  |}.

  pose proof (@default_zero LogReplay.valumap _ _).

  repeat find_apply_lem_hyp default_zero'.
  unfold wrap; simpl in *.
  repeat find_rewrite. reflexivity.
Defined.

Instance GoWrapper_LOG_mstate : GoWrapper LOG.mstate.
  refine {|
    wrap_type := Go.Struct [
      @wrap_type LogReplay.valumap _;
      @wrap_type GLog.mstate _
    ];
    wrap' := fun ms =>
      (wrap' (LOG.MSTxn ms),
      (wrap' (LOG.MSGLog ms), tt))
  |}.

  intros. repeat find_inversion_safe.
  destruct a1, a2; f_equal; eapply wrap_inj; eauto.
Defined.

Instance LOG_mstate_default_value : DefaultValue LOG.mstate.
  refine {|
    zeroval := {|
      LOG.MSTxn := zeroval;
      LOG.MSGLog := zeroval
    |}
  |}.

  pose proof (@default_zero LogReplay.valumap _ _).
  pose proof (@default_zero GLog.mstate _ _).

  repeat find_apply_lem_hyp default_zero'.
  unfold wrap; simpl in *.
  repeat find_rewrite. reflexivity.
Defined.

Instance GoWrapper_LOG_memstate : GoWrapper LOG.memstate.
  typeclasses eauto.
Defined.

Instance GoWrapper_log_xparams : GoWrapper log_xparams.
  refine {|
    wrap_type := Go.Struct [ Num; Num; Num; Num; Num; Num ];
    wrap' := fun xp => (DataStart xp, (LogHeader xp, (LogDescriptor xp, (LogDescLen xp, (LogData xp, (LogLen xp, tt))))))
  |}.
  intros. repeat find_inversion_safe.
  destruct a1, a2; f_equal; eapply wrap_inj; eauto.
Defined.

Instance log_xparams_default_value : DefaultValue log_xparams := {| zeroval := Build_log_xparams 0 0 0 0 0 0 |}.
  auto.
Defined.

Instance GoWrapper_inode_xparams : GoWrapper inode_xparams.
  refine {|
    wrap_type := Go.Struct [ Num; Num ];
    wrap' := fun xp => (IXStart xp, (IXLen xp, tt))
  |}.
  intros. repeat find_inversion_safe.
  destruct a1, a2; f_equal; eapply wrap_inj; eauto.
Defined.

Instance inode_xparams_default_value : DefaultValue inode_xparams := {| zeroval := Build_inode_xparams 0 0 |}.
  auto.
Defined.

Instance GoWrapper_balloc_xparams : GoWrapper balloc_xparams.
  refine {|
    wrap_type := Go.Struct [ Num; Num ];
    wrap' := fun xp => (BmapStart xp, (BmapNBlocks xp, tt))
  |}.
  intros. repeat find_inversion_safe.
  destruct a1, a2; f_equal; eapply wrap_inj; eauto.
Defined.

Instance balloc_xparams_default_value : DefaultValue balloc_xparams := {| zeroval := Build_balloc_xparams 0 0 |}.
  auto.
Defined.

Instance GoWrapper_fs_xparams : GoWrapper fs_xparams.
  refine {|
    wrap_type := Go.Struct [
      @wrap_type log_xparams _;
      @wrap_type inode_xparams _;
      @wrap_type balloc_xparams _;
      @wrap_type balloc_xparams _;
      @wrap_type balloc_xparams _;
      Num;
      Num
    ];
    wrap' := fun xp =>
      (wrap' (FSXPLog xp),
      (wrap' (FSXPInode xp),
      (wrap' (FSXPBlockAlloc1 xp),
      (wrap' (FSXPBlockAlloc2 xp),
      (wrap' (FSXPInodeAlloc xp),
      (wrap' (FSXPRootInum xp),
      (wrap' (FSXPMaxBlock xp), tt)))))))
  |}.

  intros. repeat find_inversion_safe.
  destruct a1, a2; f_equal; eapply wrap_inj; eauto.
Defined.

Instance fs_xparams_default_value : DefaultValue fs_xparams :=
  {| zeroval := Build_fs_xparams zeroval zeroval zeroval zeroval zeroval zeroval zeroval |}.
  auto.
Defined.

Instance GoWrapper_errno : GoWrapper Errno.Errno.
Proof.
  refine {| wrap' := fun e => match e with
                              | Errno.ELOGOVERFLOW => 1
                              | Errno.ENOTDIR => 2
                              | Errno.EISDIR => 3
                              | Errno.ENOENT => 4
                              | Errno.EFBIG => 5
                              | Errno.ENAMETOOLONG => 6
                              | Errno.EEXIST => 7
                              | Errno.ENOSPCBLOCK => 8
                              | Errno.ENOSPCINODE => 9
                              | Errno.ENOTEMPTY => 10
                              | Errno.EINVAL => 11
                              end;
            wrap_type := Go.Num |}.
  destruct a1, a2; try congruence.
Defined.

Instance GoWrapper_errno_res {A} {WA : GoWrapper A} : GoWrapper (Errno.res A).
Proof.
  refine {| wrap' := fun o => match o with
                              | Errno.Err x => (false, (Go.default_value' _, wrap' x))
                              | Errno.OK x => (true, (wrap' x, Go.default_value' _)) end;
            wrap_type := Go.Pair Go.Bool (Go.Pair (@wrap_type _ WA) (@wrap_type Errno.Errno _)) |}.
  intros a b H.
  destruct a, b; invc H; GoWrapper_t.
Defined.
