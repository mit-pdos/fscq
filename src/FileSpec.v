Require Import Arith.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.

Definition inodenum := nat.
Definition blockoffset := nat.

Inductive fileop : Type -> Type :=
  | FRead (i:inodenum) (o:blockoffset): fileop block
  | FWrite (i:inodenum) (o:blockoffset) (b:block): fileop unit
  | FAlloc: fileop (option inodenum)
  | FFree (i:inodenum): fileop unit
  | FTrunc (i:inodenum) (len:blockoffset): fileop unit.

Inductive fprog :=
  | FCommon {R:Type} (o:fileop R) (rx:R->fprog)
  | FHalt.

Record file := File {
  FIsFree: bool;
  FLen: blockoffset;
  FData: { o: blockoffset | o < FLen } -> block
}.

Definition fstatedata := inodenum -> file.

Record fstate := FSt {
  FSProg: fprog;
  FSData: fstatedata
}.

Definition setidx {K: Type} {V: Type}
                  (eq: forall (a b:K), {a=b}+{a<>b})
                  (db: K->V) (k: K) (v: V) :=
  fun x: K => if eq x k then v else db x.

Definition setidxsig {K: Type} {V: Type} {KP: K->Prop}
                     (eq: forall (a b:K), {a=b}+{a<>b})
                     (db: (sig KP) -> V) (k: K) (v: V) :=
  fun x: (sig KP) => if eq (proj1_sig x) k then v else db x.

Ltac crush_inv_sig := intros; inv_sig; crush.

Program Definition nodata: { o: blockoffset | o < 0 } -> block.
  crush_inv_sig.
Qed.

Program Definition shrinkdata {oldlen: blockoffset}
                              {len: blockoffset}
                              (SHRINK: len <= oldlen)
                              (olddata: {o : blockoffset | o < oldlen} -> block) :=
  fun x: {o: blockoffset | o < len} => olddata (exist _ (proj1_sig x) _).
Next Obligation.
  crush.
Qed.

Program Definition growzerodata {oldlen: blockoffset}
                                {len: blockoffset}
                                (GROW: len > oldlen)
                                (olddata: {o: blockoffset | o < oldlen} -> block) :=
  fun x: {o: blockoffset | o < len} =>
    if lt_dec (proj1_sig x) oldlen then olddata x else 0.

Inductive fileop_and_result :=
  | FileOpR {R:Type} (o:fileop R) (r:R).

Inductive fop_step: fileop_and_result -> fstatedata -> fstatedata -> Prop :=
  | FsmRead: forall inum off d bdata f
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (OLEN: off < FLen f)
    (BD: bdata = FData f (exist _ off OLEN)),
    fop_step (FileOpR (FRead inum off) bdata) d d
  | FsmWrite: forall inum off bdata d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (OLEN: off < FLen (d inum))
    (F': f' = File (FIsFree f) (FLen f) (setidxsig eq_nat_dec (FData f) off bdata))
    (D': d' = setidx eq_nat_dec d inum f'),
    fop_step (FileOpR (FWrite inum off bdata) tt) d d'
  | FsmAllocOK: forall inum f f' d d'
    (F: f = d inum)
    (FREE: FIsFree f = true)
    (F': f' = File false 0 nodata)
    (D': d' = setidx eq_nat_dec d inum f'),
    fop_step (FileOpR FAlloc (Some inum)) d d'
  | FsmAllocNone: forall d
    (ALLUSED: forall inum, FIsFree (d inum) = false),
    fop_step (FileOpR FAlloc None) d d
  | FsmFree: forall inum d d' f f' len fdata
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (F': f' = File true len fdata)
    (D': d' = setidx eq_nat_dec d inum f'),
    fop_step (FileOpR (FFree inum) tt) d d'
  | FsmTruncShrink: forall inum len d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (SHRINK: len <= FLen f)
    (F': f' = File false len (shrinkdata SHRINK (FData f)))
    (D': d' = setidx eq_nat_dec d inum f'),
    fop_step (FileOpR (FTrunc inum len) tt) d d'
  | FsmTruncGrow: forall inum len d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (GROW: len > FLen f)
    (F': f' = File false len (growzerodata GROW (FData f)))
    (D': d' = setidx eq_nat_dec d inum f'),
    fop_step (FileOpR (FTrunc inum len) tt) d d'.

Inductive fstep: fstate -> fstate -> Prop :=
  | FsmCommon: forall R op d d' (r:R) rx
    (OS: fop_step (FileOpR op r) d d'),
    fstep (FSt (FCommon op rx) d)
          (FSt (rx r) d')
  | FsmHalt: forall d,
    fstep (FSt FHalt d)
          (FSt FHalt d).
