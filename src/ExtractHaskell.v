Require Import ExtrHaskellPrelude.
Require Import ExtrHaskellMap.
Require Import AsyncFS.
Require Import StringUtils.
Require PermDirName.

Extraction Language Haskell.

(* Optimize away some noop-like wrappers. *)
Extraction Inline PermProg.pair_args_helper.

(* Uncomment the next line to enable eventlog-based profiling *)
(* Extract Inlined Constant PermProg.progseq => "Profile.progseq __FILE__ __LINE__". *)

Extract Inlined Constant PermProg.perm => "Prelude.Int".
Extract Inlined Constant PermProg.perm_dec =>
"(\x y -> if x Prelude.== y then Prelude.True else Prelude.False )".
Extract Inlined Constant PermProg.can_access =>
"(\x y -> case y of
          Public -> Prelude.True
          Private n -> if x Prelude.== n then Prelude.True else Prelude.False)".
Extract Inlined Constant PermProg.handle => "Word.Coq_word".
Extract Inlined Constant PermAsyncDisk.owner => "Prelude.Int".
Extract Inlined Constant PermAsyncDisk.dummy_owner => "0".
Extract Inlined Constant PermAsyncDisk.owner_dec =>
"(\x y -> if x Prelude.== y then Prelude.True else Prelude.False )".
Extract Inlined Constant PermInode.encode_tag => "Interpreter.encode_tag".
Extract Inlined Constant PermInode.decode_tag => "Interpreter.decode_tag".

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant PermCacheDef.eviction_state  => "Evict.EvictionState".
Extract Inlined Constant PermCacheDef.eviction_init   => "Evict.eviction_init".
Extract Inlined Constant PermCacheDef.eviction_update => "Evict.eviction_update".
Extract Inlined Constant PermCacheDef.eviction_choose => "Evict.eviction_choose".

Extract Inlined Constant PermLog.should_flushall => "Prelude.False".

Extract Inlined Constant StringUtils.String_as_OT.string_compare =>
  "(\x y -> if x Prelude.== y then Prelude.EQ else
            if x Prelude.< y then Prelude.LT else Prelude.GT)".

Extract Inlined Constant PermDirName.ascii2byte => "Word.ascii2byte".

Cd "../codegen".
Recursive Extraction Library PermDirName.
Recursive Extraction Library AsyncFS.
