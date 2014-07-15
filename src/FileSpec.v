Require Import Arith.
Require Import CpdtTactics.
Require Import Storage.

Definition inodenum := nat.
Definition blockoffset := nat.

Inductive fprog :=
  | FRead (i:inodenum) (o:blockoffset) (rx:block -> fprog)
  | FWrite (i:inodenum) (o:blockoffset) (b:block) (rx:fprog)
  | FAlloc (rx:inodenum -> fprog)
  | FFree (i:inodenum) (rx:fprog)
  | FTrunc (i:inodenum) (len:blockoffset) (rx:fprog)
  | FHalt.

Record file := File {
  FIsFree: bool;
  FLen: blockoffset;
  FData: { o: blockoffset | o < FLen } -> block
}.

Record fstate := FSt {
  FSProg: fprog;
  FSData: inodenum -> file
}.

Definition setidx {K: Type} {V: Type}
                  (eq: forall (a b:K), {a=b}+{a<>b})
                  (db: K->V) (k: K) (v: V) :=
  fun x: K => if eq x k then v else db x.

Definition setidxsig {K: Type} {V: Type} {KP: K->Prop}
                     (eq: forall (a b:K), {a=b}+{a<>b})
                     (db: (sig KP) -> V) (k: K) (v: V) :=
  fun x: (sig KP) => if eq (proj1_sig x) k then v else db x.

Ltac inv_sig :=
  match goal with
  | [ H: sig _ |- _ ] => inversion H
  end.

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

Inductive fstep: fstate -> fstate -> Prop :=
  | FsmRead: forall inum off rx d bdata f
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (OLEN: off < FLen f)
    (BD: bdata = FData f (exist _ off OLEN)),
    fstep (FSt (FRead inum off rx) d)
          (FSt (rx bdata) d)
  | FsmWrite: forall inum off rx bdata d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (OLEN: off < FLen (d inum))
    (F': f' = File (FIsFree f) (FLen f) (setidxsig eq_nat_dec (FData f) off bdata))
    (D': d' = setidx eq_nat_dec d inum f'),
    fstep (FSt (FWrite inum off bdata rx) d)
          (FSt rx d')
  | FsmAlloc: forall rx inum f f' d d'
    (F: f = d inum)
    (FREE: FIsFree f = true)
    (F': f' = File false 0 nodata)
    (D': d' = setidx eq_nat_dec d inum f'),
    fstep (FSt (FAlloc rx) d)
          (FSt (rx inum) d')
  | FsmFree: forall inum rx d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (F': f' = File true 0 nodata)
    (D': d' = setidx eq_nat_dec d inum f'),
    fstep (FSt (FFree inum rx) d)
          (FSt rx d')
  | FsmTruncShrink: forall inum len rx d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (SHRINK: len <= FLen f)
    (F': f' = File false len (shrinkdata SHRINK (FData f)))
    (D': d' = setidx eq_nat_dec d inum f'),
    fstep (FSt (FTrunc inum len rx) d)
          (FSt rx d')
  | FsmTruncGrow: forall inum len rx d d' f f'
    (F: f = d inum)
    (NOTFREE: FIsFree f = false)
    (GROW: len > FLen f)
    (F': f' = File false len (growzerodata GROW (FData f)))
    (D': d' = setidx eq_nat_dec d inum f'),
    fstep (FSt (FTrunc inum len rx) d)
          (FSt rx d')
  | FsmHalt: forall d,
    fstep (FSt FHalt d)
          (FSt FHalt d).