Require Import Cache FSLayout.
Require Import GoSemantics GoHoare GoTactics1.

Import Go.

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

Instance addrmap_default_value : forall T {H: GoWrapper T}, DefaultValue (Map.t T).
  intros.
  apply Build_DefaultValue with (zeroval := Map.empty _).
  unfold default_value, default_value', wrap, wrap'.
  simpl. repeat f_equal.
  apply MapUtils.addrmap_equal_eq.
  apply MapUtils.AddrMap.map_empty.
  eauto with map.
Defined.

Instance WrapByTransforming_log_xparams : WrapByTransforming log_xparams.
  refine {|
    transform := fun xp => (DataStart xp, LogHeader xp, LogDescriptor xp, LogDescLen xp, LogData xp, LogLen xp)
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.

Instance log_xparams_default_value : DefaultValue log_xparams := {| zeroval := Build_log_xparams 0 0 0 0 0 0 |}.
  auto.
Defined.

Instance WrapByTransforming_inode_xparams : WrapByTransforming inode_xparams.
  refine {|
    transform := fun xp => (IXStart xp, IXLen xp)
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.

Instance inode_xparams_default_value : DefaultValue inode_xparams := {| zeroval := Build_inode_xparams 0 0 |}.
  auto.
Defined.

Instance WrapByTransforming_balloc_xparams : WrapByTransforming balloc_xparams.
  refine {|
    transform := fun xp => (BmapStart xp, BmapNBlocks xp)
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.

Instance balloc_xparams_default_value : DefaultValue balloc_xparams := {| zeroval := Build_balloc_xparams 0 0 |}.
  auto.
Defined.

Instance WrapByTransforming_fs_xparams : WrapByTransforming fs_xparams.
  refine {|
    transform := fun xp => (FSXPLog xp, FSXPInode xp, FSXPBlockAlloc1 xp, FSXPBlockAlloc2 xp,
                            FSXPInodeAlloc xp, FSXPRootInum xp, FSXPMaxBlock xp)
  |}.
  simpl; intros. repeat find_inversion_safe. destruct t1, t2; f_equal; auto.
Defined.
