Require Import Arith.
Require Import CpdtTactics.
Require Import Storage.
Require Import FileSpec.

Inductive bfprog :=
  | BFRead (i:inodenum) (o:blockoffset) (rx:block -> bfprog)
  | BFWrite (i:inodenum) (o:blockoffset) (b:block) (rx:bfprog)
  | BFAlloc (rx:inodenum -> bfprog)
  | BFFree (i:inodenum) (rx:bfprog)
  | BFTrunc (i:inodenum) (len:blockoffset) (rx:bfprog)
  | BFSync (i:inodenum) (rx:bfprog)
  | BFHalt.

Record bfstate := BFSt {
  BFSProg: bfprog;
  BFSPersistData: inodenum -> FileSpec.file;
  BFSEphemData: inodenum -> FileSpec.file
}.

Inductive bfstep: bfstate -> bfstate -> Prop :=
  | BFsmRead: forall inum off frx bfrx pd d bdata,
    fstep (FSt (FRead inum off frx) d)
          (FSt (frx bdata) d) ->
    bfstep (BFSt (BFRead inum off bfrx) pd d)
           (BFSt (bfrx bdata) pd d)
  | BFsmWrite: forall inum off frx bfrx pd d d' bdata,
    fstep (FSt (FWrite inum off bdata frx) d)
          (FSt frx d') ->
    bfstep (BFSt (BFWrite inum off bdata bfrx) pd d)
           (BFSt bfrx pd d)
  | BFsmAlloc: forall inum frx bfrx pd d d',
    fstep (FSt (FAlloc frx) d)
          (FSt (frx inum) d') ->
    bfstep (BFSt (BFAlloc bfrx) pd d)
           (BFSt (bfrx inum) pd d')
  | BFsmFree: forall inum frx bfrx pd d d',
    fstep (FSt (FFree inum frx) d)
          (FSt frx d') ->
    bfstep (BFSt (BFFree inum bfrx) pd d)
           (BFSt bfrx pd d')
  | BFsmTrunc: forall inum len frx bfrx pd d d',
    fstep (FSt (FTrunc inum len frx) d)
          (FSt frx d') ->
    bfstep (BFSt (BFTrunc inum len bfrx) pd d)
           (BFSt bfrx pd d')
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
