Require Import Go.
Import Go.

Example swap_example : stmt :=
  (Declare Num (fun a =>
   Declare Num (fun b =>
   Declare DiskBlock (fun va =>
   Declare DiskBlock (fun vb =>
     (a <~ Const 1;
     b <~ Const 2;
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