Require Import CCL.
Require Import OptimisticCache WriteBuffer.
Require Import OptimisticTranslator OptimisticFS.

Require AsyncFS.
(* imports for DirTreeRep.rep *)
Import FSLayout DirTreeDef Inode.INODE.
(* import memstate *)
Import BFile.BFILE.

Record FSParams St :=
  { fs_cache : CacheParams St;
    fsmem: var (Mem St) memstate;
    fstree: var (Abstraction St) dirtree; }.

Section ConcurrentFS.

  Context {St:StateTypes}.
  Variable FP:FSParams St.
  (* no guarantee since we won't prove any specs in this file *)

  Definition get_fsmem := get_var (fsmem FP).
  Definition set_fsmem := set_var (fsmem FP).
  Definition upd_fstree s update := set_var (fstree FP) s (update (get_var (fstree FP) s)).

  Definition guard {T} (r: Result T) : {exists v, r=Success v} + {r=Failed}.
    destruct r; eauto.
  Defined.

  Definition retry_syscall T
             (p: memstate -> @cprog St (Result (T * memstate) * WriteBuffer))
             (update: TID -> dirtree -> dirtree)
    : cprog (Result T) :=
    retry guard (m <- Get;
                   do '(r, wb) <- p (get_fsmem m);
                   match r with
                   | Success (r, ms') =>
                     _ <- CacheCommit (fs_cache FP) wb;
                       m <- Get;
                       _ <- Assgn (set_fsmem m ms');
                       _ <- GhostUpdate (fun tid s => upd_fstree s (update tid));
                       Ret (Success r)
                   | Failed =>
                     _ <- CacheAbort (fs_cache FP) wb;
                       _ <- Yield;
                       Ret Failed
                   end).

End ConcurrentFS.