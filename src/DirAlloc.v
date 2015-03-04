Require Import DirName.
Require Import Balloc.
Require Import Prog.
Require Import BasicProg.
Require Import Bool.
Require Import Word.

Set Implicit Arguments.

Module DIRALLOC.

  Definition dacreate T lxp ibxp dbxp ixp dnum name mscs rx : prog T :=
    let2 (mscs, oi) <- BALLOC.alloc_gen lxp ibxp mscs;
    match oi with
    | None => rx (mscs, None)
    | Some inum =>
      let2 (mscs, ok) <- SDIR.dslink lxp dbxp ixp dnum name inum $0 mscs;
      match ok with
      | true => rx (mscs, Some inum)
      | false => rx (mscs, None)
      end
    end.

  Definition dadelete T lxp ibxp dbxp ixp dnum name mscs rx : prog T :=
    let2 (mscs, oi) <- SDIR.dslookup lxp dbxp ixp dnum name mscs;
    match oi with
    | None => rx (mscs, false)
    | Some (inum, isdir) =>
      let2 (mscs, ok) <- SDIR.dsunlink lxp dbxp ixp dnum name mscs;
      If (bool_dec ok true) {
        mscs <- BALLOC.free_gen lxp ibxp inum mscs;
        rx (mscs, true)
      } else {
        rx (mscs, false)
      }
    end.

  (* XXX what should the rep invariant look like? *)

End DIRALLOC.
