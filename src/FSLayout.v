Require Import Prog.
Require Import Word.

Record cache_xparams := {
  MaxCacheBlocks : addr;
  MaxCacheBlocksOK : MaxCacheBlocks <> $0
}.

Record memlog_xparams := {
  LogCache : cache_xparams;

  (* The actual data region is everything that's not described here *)
  LogHeader : addr; (* Store the header here *)
  LogCommit : addr; (* Store true to apply after crash. *)

  LogDescriptor : addr; (* Start of descriptor region in log *)
  LogData : addr; (* Start of data region in log *)
  LogLen : addr  (* Maximum number of entries in log; length but still use addr type *)
}.

Record balloc_xparams := {
  BmapStart : addr;
  BmapNBlocks : addr
}.

Record inode_xparams := {
  IXStart : addr;
  IXLen : addr
}.

Record fs_xparams := {
  FSXPMemLog : memlog_xparams;
  FSXPInode : inode_xparams;
  FSXPInodeAlloc : balloc_xparams;
  FSXPBlockAlloc : balloc_xparams;
  FSXPMaxBlock : addr
}.