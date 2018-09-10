Require Import ExtrHaskellPrelude.
Require Import ExtrHaskellMap.
Require Import AsyncFS.
Require Import StringUtils.
Require DirName.

Extraction Language Haskell.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.pair_args_helper.

(* Uncomment the next line to enable eventlog-based profiling *)
(* Extract Inlined Constant Prog.progseq => "Profile.progseq __FILE__ __LINE__". *)

Extract Inlined Constant Prog.perm => "Prelude.Int".
Extract Inlined Constant Prog.perm_dec =>
"(\x y -> if x Prelude.== y then Prelude.True else Prelude.False )".
Extract Inlined Constant Prog.can_access =>
"(\x y -> case y of
          Public -> Prelude.True
          Private n -> if x Prelude.== n then Prelude.True else Prelude.False)".
Extract Inlined Constant Blockmem.handle => "Word.Coq_word".
Extract Inlined Constant AsyncDisk.owner => "Prelude.Int".
Extract Inlined Constant AsyncDisk.dummy_owner => "0".
Extract Inlined Constant AsyncDisk.owner_dec =>
"(\x y -> if x Prelude.== y then Prelude.True else Prelude.False )".
Extract Inlined Constant Inode.encode_tag => "Interpreter.encode_tag".
Extract Inlined Constant Inode.decode_tag => "Interpreter.decode_tag".

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant CacheDef.eviction_state  => "Evict.EvictionState".
Extract Inlined Constant CacheDef.eviction_init   => "Evict.eviction_init".
Extract Inlined Constant CacheDef.eviction_update => "Evict.eviction_update".
Extract Inlined Constant CacheDef.eviction_choose => "Evict.eviction_choose".

Extract Inlined Constant Log.should_flushall => "Prelude.False".

Extract Inlined Constant StringUtils.String_as_OT.string_compare =>
  "(\x y -> if x Prelude.== y then Prelude.EQ else
            if x Prelude.< y then Prelude.LT else Prelude.GT)".

Extract Inlined Constant DirName.ascii2byte => "Word.ascii2byte".

Cd "../codegen".
Recursive Extraction Library DirName.
Recursive Extraction Library AsyncFS.
