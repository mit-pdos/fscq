Require Import Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import DirCache.
Require Import GenSepN.
Require Import ListPred.
Require Import Inode.
Require Import List ListUtils.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.
Require Import SuperBlock.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import BFile.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Require Import DirTreeNames.
Require Import AsyncFS.

Set Implicit Arguments.
Import DirTree.
Import DIRTREE.
Import AFS.
Import ListNotations.

Notation MSLL := BFILE.MSLL.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSDBlocks := BFILE.MSDBlocks.


(** Safety **)

(** 
(** this axioms may simplify tree equivalence after execution proofs *)
Axiom one_tag_per_user:
  forall pr t t',
    t <> Public ->
    t' <> Public ->
    can_access pr t ->
    can_access pr t' ->
    t = t'.

Axiom one_user_per_tag:
  forall pr pr' t,
    t <> Public ->
    can_access pr t ->
    can_access pr' t ->
    pr = pr'.
 *)

Inductive fbasic : Type -> Type :=
| file_get_attr_f :
    INODE.IRec.Cache.key ->
    fbasic (Rec.data (Rec.field_type
            (Rec.FE [("owner", Rec.WordF 8);
                     ("unused", Rec.WordF 16)]
                    "attr" INODE.attrtype)))

| file_set_attr_f :
    INODE.IRec.Cache.key ->
    INODE.iattrin ->
    fbasic (res unit)

| file_get_sz_f :
    INODE.IRec.Cache.key ->
    fbasic (word 64)

| file_set_sz_f :
    INODE.IRec.Cache.key ->
    word 64 ->
    fbasic (res unit)
                         
| read_fblock_f :
    INODE.IRec.Cache.key ->
    addr ->
    fbasic (res block)

| update_fblock_d_f :
    INODE.IRec.Cache.key ->
    addr ->
    block ->
    fbasic (res unit)
           
| file_truncate_f :
    INODE.IRec.Cache.key ->
    addr ->
    fbasic (res unit)

| file_sync_f :
    INODE.IRec.Cache.key ->
    fbasic (res unit)

| readdir_f :
    INODE.IRec.Cache.key ->
    fbasic (list (String.string * (addr * bool)))

| mkdir_f :
    BFcache.key ->
    Dcache.key ->
    fbasic (res addr)

| mksock_f :
    BFcache.key ->
    Dcache.key ->
    tag ->
    fbasic (res INODE.IRec.Cache.key)

| create_f :
    BFcache.key ->
    Dcache.key ->
    tag ->
    fbasic (res addr)
           
| delete_f :
    BFcache.key ->
    Dcache.key ->
    fbasic (res unit)

| lookup_f :
    addr ->
    list String.string ->
    fbasic (res (BFcache.key * bool))
           
| rename_f :
    addr ->
    list String.string ->
    Dcache.key ->
    list String.string ->
    Dcache.key ->
    fbasic (res unit)

| tree_sync_f :
    fbasic (res unit)

| tree_sync_noop_f :
    fbasic (res unit).

Inductive fprog : Type -> Type :=
| FBasic : forall T, fbasic T -> fprog T
| FBind: forall T T', fbasic T  -> (T -> fprog T') -> fprog T'.

Inductive exec_fbasic:
  forall T, perm -> tagged_disk ->
       block_mem -> hashmap -> fs_xparams -> BFILE.memstate ->
       fbasic T ->  @result T -> BFILE.memstate -> trace -> Prop :=
| FExecRead    :
    forall pr d bm hm tr' fsxp inum off (ams ams': BFILE.memstate)
      (r: res block) d' bm' hm',
      exec pr d bm hm (read_fblock fsxp inum off ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (read_fblock_f inum off)
                  (Finished d' bm' hm' r) ams' tr'
                  
| FExecSetAttr    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      attr (r: res unit) d' bm' hm',
      exec pr d bm hm (file_set_attr fsxp inum attr ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (file_set_attr_f inum attr)
                  (Finished d' bm' hm' r) ams' tr'

| FExecGetAttr    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      r d' bm' hm',
      exec pr d bm hm (file_get_attr fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (file_get_attr_f inum)
                  (Finished d' bm' hm' r) ams' tr'

| FExecSetSz    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      sz (r: res unit) d' bm' hm',
      exec pr d bm hm (file_set_sz fsxp inum sz ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (file_set_sz_f inum sz)
                  (Finished d' bm' hm' r) ams' tr'

| FExecGetSz    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      r d' bm' hm',
      exec pr d bm hm (file_get_sz fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (file_get_sz_f inum)
            (Finished d' bm' hm' r) ams' tr'
                   
| FExecWrite   :
    forall pr d bm hm d' bm' hm' tr' fsxp
      inum off v (ams ams': BFILE.memstate) (ok: res unit),
      exec pr d bm hm (update_fblock_d fsxp inum off v ams)
           (Finished d' bm' hm' ^(ams', ok)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (update_fblock_d_f inum off v)
                  (Finished d' bm' hm' ok) ams' tr'

| FExecTruncate    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      sz (r: res unit) d' bm' hm',
      exec pr d bm hm (file_truncate fsxp inum sz ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (file_truncate_f inum sz)
                  (Finished d' bm' hm' r) ams' tr'

| FExecFileSync    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      (r: res unit) d' bm' hm',
      exec pr d bm hm (file_sync fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (file_sync_f inum)
                  (Finished d' bm' hm' r) ams' tr'

| FExecReaddir    :
    forall pr d bm hm tr' fsxp inum (ams ams': BFILE.memstate)
      (r: list (String.string * (addr * bool))) d' bm' hm',
      exec pr d bm hm (readdir fsxp inum ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (readdir_f inum)
                  (Finished d' bm' hm' r) ams' tr'

| FExecCreate    :
    forall pr d bm hm tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res addr) name tag d' bm' hm',
      exec pr d bm hm (create fsxp dnum name tag ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (create_f dnum name tag)
                  (Finished d' bm' hm' r) ams' tr'

| FExecDelete    :
    forall pr d bm hm tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res unit) name d' bm' hm',
      exec pr d bm hm (delete fsxp dnum name ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (delete_f dnum name)
                  (Finished d' bm' hm' r) ams' tr'

| FExecLookup    :
    forall pr d bm hm tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res (BFcache.key * bool)) fnlist d' bm' hm',
      exec pr d bm hm (lookup fsxp dnum fnlist ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (lookup_f dnum fnlist)
                  (Finished d' bm' hm' r) ams' tr'

| FExecRename    :
    forall pr d bm hm tr' fsxp dnum (ams ams': BFILE.memstate)
      (r: res unit) srcpath srcname dstpath dstname d' bm' hm',
      exec pr d bm hm (rename fsxp dnum srcpath srcname dstpath dstname ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (rename_f dnum srcpath srcname dstpath dstname)
                  (Finished d' bm' hm' r) ams' tr'

| FExecTreeSync    :
    forall pr d bm hm tr' fsxp (ams ams': BFILE.memstate)
      (r: res unit) d' bm' hm',
      exec pr d bm hm (tree_sync fsxp ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (tree_sync_f)
                  (Finished d' bm' hm' r) ams' tr'

| FExecTreeSyncNoop    :
    forall pr d bm hm tr' fsxp (ams ams': BFILE.memstate)
      (r: res unit) d' bm' hm',
      exec pr d bm hm (tree_sync_noop fsxp ams)
           (Finished d' bm' hm' ^(ams', r)) tr' ->
      exec_fbasic pr d bm hm fsxp ams (tree_sync_noop_f)
                  (Finished d' bm' hm' r) ams' tr'.


Inductive fexec:
  forall T, perm -> tagged_disk ->
       block_mem -> hashmap -> fs_xparams -> BFILE.memstate ->
       fprog T ->  @result T -> BFILE.memstate -> trace -> Prop :=
| FExecBasic    :
    forall T (p :fbasic T) pr fsxp d bm hm tr' (ams ams': BFILE.memstate)
     out,
      exec_fbasic pr d bm hm fsxp ams p out ams' tr' ->
      fexec pr d bm hm fsxp ams (FBasic p) out ams' tr'
                   
| FExecBind :
    forall T T' pr (p1 : fbasic T) (p2: T -> fprog T') fsxp d bm hm d'
      bm' hm' v r tr' tr'' ams ams' ams'',
               exec_fbasic pr d bm hm fsxp ams p1 (Finished d' bm' hm' v) ams' tr' ->
               fexec pr d' bm' hm' fsxp ams' (p2 v) r ams'' tr'' ->
               fexec pr d bm hm fsxp ams (FBind p1 p2) r ams'' (tr''++tr')

| FCrashBind : forall T T' pr (p1 : fbasic T) (p2: T -> fprog T') fsxp d d' bm bm' hm hm' tr' ams ams',
                exec_fbasic pr d bm hm fsxp ams p1 (Crashed d' bm' hm') ams' tr' ->
                fexec pr d bm hm fsxp ams (FBind p1 p2) (Crashed d' bm' hm') ams' tr'

| FFailedBind : forall T T' pr (p1 : fbasic T) (p2: T -> fprog T') fsxp d d' bm bm' hm hm' tr' ams ams',
                exec_fbasic pr d bm hm fsxp ams p1 (Failed d' bm' hm') ams' tr' ->
                fexec pr d bm hm fsxp ams (FBind p1 p2) (Failed d' bm' hm') ams' tr'.