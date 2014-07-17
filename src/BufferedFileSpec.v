Require Import Arith.
Require Import CpdtTactics.
Require Import Storage.
Require Import FileSpec.

Inductive bfprog :=
  | BFCommon {R:Type} (o:fileop R) (rx:R -> bfprog)
  | BFSync (i:inodenum) (rx:bfprog)
  | BFHalt.

Record bfstate := BFSt {
  BFSProg: bfprog;
  BFSPersistData: inodenum -> FileSpec.file;
  BFSEphemData: inodenum -> FileSpec.file
}.

Inductive bfstep: bfstate -> bfstate -> Prop :=
  | BFsmCommon: forall R op pd d d' (r:R) rx
    (OS: fop_step (FileOpR op r) d d'),
    bfstep (BFSt (BFCommon op rx) pd d)
           (BFSt (rx r) pd d')
  | BFsmSync: forall inum rx pd d
    (P: d inum = pd inum),
    bfstep (BFSt (BFSync inum rx) pd d)
           (BFSt rx pd d)
  | BFsmFlush: forall prog inum pd pd' d
    (P: pd' = setidx eq_nat_dec pd inum (d inum)),
    bfstep (BFSt prog pd d)
           (BFSt prog pd' d)
  | BFsmHalt: forall pd d,
    bfstep (BFSt BFHalt pd d)
           (BFSt BFHalt pd d).
