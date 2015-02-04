(** Extraction to Haskell: assume Prelude imported *)

Require Import Coq.Program.Basics.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inlined Constant Bool.bool_dec => "(Prelude.==)".

Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extract Inductive unit => "()" [ "()" ].
Extract Inlined Constant id => "(Prelude.id)".

Extract Inductive list => "([])" [ "([])" "(:)" ].
Extract Inlined Constant app => "(Prelude.++)".
(* NB: length returns nat *)

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".

Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sum => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb => "(Prelude.||)".
Extract Inlined Constant negb => "Prelude.not".

(* Integer isn't quite right, because it can go negative, and
 * subtraction does not saturate at zero.  But good enough for
 * now, since we use it only for minor things like word sizes.
 *)
Extract Inductive nat => "Prelude.Integer" [ "0" "Prelude.succ" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Inlined Constant Nat.add => "(Prelude.+)".
Extract Inlined Constant Nat.mul => "(Prelude.*)".
Extract Inlined Constant Compare_dec.lt_dec => "(Prelude.<)".

Extract Inductive ascii => "Prelude.Char"
  [ "(\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr (
      (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+
      (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+
      (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+
      (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+
      (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+
      (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+
      (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+
      (if b7 then Data.Bits.shiftL 1 7 else 0)))" ]
  "(\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))".
Extract Inlined Constant Ascii.ascii_dec => "(Prelude.==)".

Extract Inductive string => "Prelude.String"
  [ "[]" "(\hd tl -> [hd] Prelude.++ tl)" ]
  "(\fE fS s -> case s of {
    [] -> fE ();
    (c:cs) -> fS c cs
   } )".
Extract Inlined Constant String.string_dec => "(Prelude.==)".
