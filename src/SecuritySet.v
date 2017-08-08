Require Export Ensembles.
Require Export Prog ProgMonad.
Require Export Pred.
Require Export Omega.
Require Export SepAuto.
Require Export Word.
Require Export FunctionalExtensionality.
Require Export List.
Require Export AsyncDisk.
Require Export ListUtils.
Require Export BasicProg.
Require Export Array.
Require Export Bytes.
Require Export Mem.
Require Export GenSepN.

Set Implicit Arguments.


Inductive prog_secure_set: forall T AT, prog T -> Ensemble AT -> Prop :=
| ReadSec : forall a, prog_secure_set (Read a) (Singleton _ a)
| WriteSec : forall a v, prog_secure_set (Write a v) (Singleton _ a)
| BindSec : forall AT T T' (p1: prog T) (p2: T -> prog T') (s1 s2: Ensemble AT) ,
                    prog_secure_set p1 s1
                    -> (forall m m' vm vm' hm hm' x, exec m vm hm p1 (Finished m' vm' hm' x)
                              -> prog_secure_set (p2 x) s2)
                    -> prog_secure_set (x <- p1; p2 x) (Union _ s1 s2)
| InclSec : forall AT T (p: prog T) (s1 s2: Ensemble AT),
                    prog_secure_set p s1
                    -> Included _ s1 s2
                    -> prog_secure_set p s2
| RetSec : forall  AT T (r: T), prog_secure_set (Ret r) (Empty_set AT)
| SyncSec : forall AT, prog_secure_set Sync  (Empty_set AT)
| TrimSec : forall a, prog_secure_set (Trim a) (Singleton _ a)
| VarAllocSec : forall AT (T : Type) (v : T), prog_secure_set (VarAlloc v)  (Empty_set AT) 
| VarDeleteSec: forall AT (i : vartype), prog_secure_set (VarDelete i)  (Empty_set AT) 
| VarGetSec : forall  AT (i : vartype) (T : Type), prog_secure_set (@VarGet i T)  (Empty_set AT)
| VarSetSec: forall AT (i : vartype) (T : Type) (v : T), prog_secure_set (VarSet i v)  (Empty_set AT)
| AlertModifiedSec : forall AT, prog_secure_set (AlertModified)  (Empty_set AT)
| DebugSec : forall AT (s: String.string) (n: nat), prog_secure_set (Debug s n)  (Empty_set AT)
| RdtscSec : forall AT, prog_secure_set (Rdtsc)  (Empty_set AT)
| HashSec : forall AT (sz: nat) (buf: word sz), prog_secure_set (Hash buf)  (Empty_set AT)
| Hash2Sec : forall AT (sz1 sz2: nat) (buf1 : word sz1) (buf2 : word sz2), prog_secure_set (Hash2 buf1 buf2)  (Empty_set AT).

Hint Constructors prog_secure_set.