Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlString.

Require Import Coq.Program.Basics.

Require Import PeanoNat.
Require Import ZArith.

(* Avoid conflicts with existing Ocaml module names. *)
Extraction Blacklist String List Nat Array Bytes.

Extraction Language Ocaml.

Require Import Go.
Import Go.

Example swap_example : stmt :=
  (Declare Num (fun a =>
   Declare Num (fun b =>
   Declare DiskBlock (fun va =>
   Declare DiskBlock (fun vb =>
     (a <~ Const Num 1;
     b <~ Const Num 2;
     DiskRead va (Var a);
     DiskRead vb (Var b);
     DiskWrite (Var a) (Var vb);
     DiskWrite (Var b) (Var va))
   )))))%go.

(* Corresponding Go:
  {
    var a Num
    {
      var b Num
      {
        var va *DiskBlock
        {
          var vb *DiskBlock
          a = 1
          b = 2
          DiskRead(va, a)
          DiskRead(vb, b)
          DiskWrite(a, vb)
          DiskWrite(b, va)
        }
      }
    }
  }
*)

Cd "coq2go".
Separate Extraction Go.
Extraction swap_example.
