Require Import ReadCache.
Require Import ReadCacheX.
Require Import WritebackCache.

Module BUFCACHE := ReadCacheX.RCacheX.

Definition cachestate := ReadCache.cachestate.
