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
  | BFsmRead: forall inum off pd d d' bdata,
    (forall frx,
     fstep (FSt (FRead inum off frx) d)
           (FSt (frx bdata) d')) ->
    (forall bfrx,
     bfstep (BFSt (BFRead inum off bfrx) pd d)
            (BFSt (bfrx bdata) pd d'))
  | BFsmWrite: forall inum off pd d d' bdata,
    (forall frx,
     fstep (FSt (FWrite inum off bdata frx) d)
           (FSt frx d')) ->
    (forall bfrx,
     bfstep (BFSt (BFWrite inum off bdata bfrx) pd d)
            (BFSt bfrx pd d))
  | BFsmAlloc: forall inum pd d d',
    (forall frx,
     fstep (FSt (FAlloc frx) d)
           (FSt (frx inum) d')) ->
    (forall bfrx,
     bfstep (BFSt (BFAlloc bfrx) pd d)
            (BFSt (bfrx inum) pd d'))
  | BFsmFree: forall inum pd d d',
    (forall frx,
     fstep (FSt (FFree inum frx) d)
           (FSt frx d')) ->
    (forall bfrx,
     bfstep (BFSt (BFFree inum bfrx) pd d)
            (BFSt bfrx pd d'))
  | BFsmTrunc: forall inum len pd d d',
    (forall frx,
     fstep (FSt (FTrunc inum len frx) d)
           (FSt frx d')) ->
    (forall bfrx,
     bfstep (BFSt (BFTrunc inum len bfrx) pd d)
            (BFSt bfrx pd d'))
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
