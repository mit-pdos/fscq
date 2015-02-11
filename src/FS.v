Require Import Prog.
Require Import MemLog.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred.
Require Import Dir.

Definition file_len T lxp ixp inum rx : prog T :=
  ms <- MEMLOG.begin lxp;
  len <- BFILE.bflen lxp ixp inum ms;
  _ <- MEMLOG.commit lxp ms;
  rx (len ^* $512).

Definition read_block T lxp ixp inum off rx : prog T :=
  ms <- MEMLOG.begin lxp;
  b <- BFILE.bfread lxp ixp inum off ms;
  _ <- MEMLOG.commit lxp ms;
  rx b.

Definition write_block T lxp bxp ixp inum off v rx : prog T :=
  ms <- MEMLOG.begin lxp;
  curlen <- BFILE.bflen lxp ixp inum ms;
  If (wlt_dec off curlen) {
    ms <- BFILE.bfwrite lxp ixp inum off v ms;
    ok <- MEMLOG.commit lxp ms;
    rx ok
  } else {
    ms <- For n < off ^- curlen ^+ $1
      Loopvar ms <- ms
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        r <- BFILE.bfgrow lxp bxp ixp inum ms;
        let (ok, ms) := r in
        If (bool_dec ok false) {
          MEMLOG.abort lxp ms;;
          rx false
        } else {
          lrx ms
        }
    Rof;

    ms <- BFILE.bfwrite lxp ixp inum off v ms;
    ok <- MEMLOG.commit lxp ms;
    rx ok
  }.

Definition readdir T lxp ixp dnum rx : prog T :=
  ms <- MEMLOG.begin lxp;
  files <- DIR.dlist lxp ixp dnum ms;
  _ <- MEMLOG.commit lxp ms;
  rx files.
