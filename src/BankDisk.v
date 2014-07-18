Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import Bank.
Require Import Trans.
Require Import Disk.

Fixpoint compile_ad (p:aproc) : dprog :=
  match p with
    | AHalt => DHalt
    | ASetAcct a v rx => DWrite a v ;; compile_ad rx
    | AGetAcct a rx => v <- DRead a; compile_ad (rx v)
    | ATransfer src dst v rx => r <- DRead src ; DWrite src (r-v) ;;
                   r1 <- DRead dst ; DWrite dst (r1+v) ;; compile_ad rx
  end.

Definition compile_at (p:aproc) : tprog2 :=
  Trans.T2DProg (compile_ad p) ;; T2Commit ;; T2Halt.
