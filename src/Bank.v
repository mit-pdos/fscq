Require Import List.
Require Import Arith.
Import ListNotations.
Require Import Storage.
Require Import CpdtTactics.

Section App.

(* app language *)

Inductive aproc :=
  | ACommit
  | ASetAcct (a:nat) (v:nat) (rx: aproc)
  | AGetAcct (a:nat) (rx: nat->aproc)
  | ATransfer (src:nat) (dst:nat) (v:nat) (rx: aproc)
  .

Fixpoint aexec (p:aproc) (s:storage) : storage :=
  match p with
    | ACommit => s
    | ASetAcct a v rx => aexec rx (st_write s a v)
    | AGetAcct a rx => aexec (rx (st_read s a)) s
    | ATransfer n m v rx => aexec rx (st_write (st_write s m ((st_read s m) + v)) n ((st_read s n) -v))
  end.

Definition initial := 100.

Definition transfer (src:nat) (dst:nat) (v:nat): value * value :=
  let s := aexec (ASetAcct src initial (ASetAcct dst initial (ATransfer src dst 10 (ACommit)))) st_init in
   (st_read s src, st_read s dst).

(* A simple example to argue that A language is correct *)
Example legal_transfer1:
  forall k1 k2,
    transfer 0 1 10 = (k1, k2) -> k1 = initial - 10 /\ k2 = initial + 10.
Proof.
  intros; inversion H.
  crush.
Qed.


(* For small-step simulation in refinement proof of app language to trans language *)

(* XXX not used *)

Record astate := ASt {
  ASProg: aproc;
  ASDisk: storage;
  ASCommit: bool   (* at beginning of instruction: false; at end of instruction: true *)
}.

Inductive asmstep : astate -> astate -> Prop :=
  | AsmCommit: forall d c,
    asmstep (ASt ACommit d c) (ASt ACommit d true)
  | AsmSetAcct: forall d a v rx,
    asmstep (ASt (ASetAcct a v rx) d false)
            (ASt rx (st_write d a v) true)
  | AsmGetAcct: forall d a rx,
    asmstep (ASt (AGetAcct a rx) d false)
            (ASt (rx (st_read d a)) d true)
  | AsmTransfer: forall d m n v rx,
    asmstep (ASt (ATransfer m n v rx) d false)
            (ASt rx (st_write (st_write d m ((st_read d m) - v)) n 
                    (st_read (st_write d m (st_read d m - v)) n + v)) true)

    (* must write 3 times, otherwise when m=n the value on disk will
       depend on arguments' evaluation order *).
  

End App.

