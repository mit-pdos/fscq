Require Import Cache FSLayout MemLog GroupLog Log BFile.
Require Import GoSemantics GoHoare GoTactics1.
Require Import List.

Import Go.
Import ListNotations.

Ltac Transform_t := abstract (intros;
  repeat match goal with
  | [ |- ?a = ?b ] => congruence
  | [ |- ?a = ?b ] => destruct a, b; simpl in *
  end).

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
  Transform_t.
Defined.

Instance cachestate_default_value : DefaultValue cachestate := {| zeroval :=
  {| CSMap := Go.Map.empty _; CSMaxCount := 0; CSEvict := tt |} |}.
  unfold wrap, wrap', GoWrapper_transform, default_value. simpl.
  repeat f_equal.
  eauto using MapUtils.addrmap_equal_eq, MapUtils.AddrMap.map_empty with map.
Defined.

Instance GoWrapper_GLog_mstate : WrapByTransforming GLog.mstate.
  refine {|
    transform := fun ms =>
      (GLog.MSVMap ms,
      GLog.MSTxns ms,
      GLog.MSMLog ms)
  |}.
  Transform_t.
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

Instance GoWrapper_LOG_mstate : WrapByTransforming LOG.mstate.
  refine {|
    transform := fun ms =>
      (LOG.MSTxn ms,
      LOG.MSGLog ms)
  |}.
  Transform_t.
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

Instance WrapByTransforming_log_xparams : WrapByTransforming log_xparams.
  refine {|
    transform := fun xp => (DataStart xp, LogHeader xp, LogDescriptor xp, LogDescLen xp, LogData xp, LogLen xp)
  |}.
  Transform_t.
Defined.

Instance log_xparams_default_value : DefaultValue log_xparams := {| zeroval := Build_log_xparams 0 0 0 0 0 0 |}.
  auto.
Defined.

Instance GoWrapper_inode_xparams : WrapByTransforming inode_xparams.
  refine {|
    transform := fun xp => (IXStart xp, IXLen xp)
  |}.
  Transform_t.
Defined.

Instance inode_xparams_default_value : DefaultValue inode_xparams := {| zeroval := Build_inode_xparams 0 0 |}.
  auto.
Defined.

Instance GoWrapper_balloc_xparams : WrapByTransforming balloc_xparams.
  refine {|
    transform := fun xp => (BmapStart xp, BmapNBlocks xp)
  |}.
  Transform_t.
Defined.

Instance balloc_xparams_default_value : DefaultValue balloc_xparams := {| zeroval := Build_balloc_xparams 0 0 |}.
  auto.
Defined.

Instance GoWrapper_fs_xparams : WrapByTransforming fs_xparams.
  refine {|
    transform := fun xp =>
      (FSXPInode xp,
      FSXPBlockAlloc1 xp,
      FSXPBlockAlloc2 xp,
      FSXPInodeAlloc xp,
      FSXPRootInum xp,
      FSXPMaxBlock xp,
      FSXPLog xp)
  |}.
  Transform_t.
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
