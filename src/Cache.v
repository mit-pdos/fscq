Require Import ReadCache.
Require Import WritebackCache.

Module BUFCACHE := WritebackCache.WBCache.

Definition cachestate := WritebackCache.wbcachestate.
