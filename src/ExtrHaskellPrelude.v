(** Extraction to Haskell: assume Prelude imported *)

Require Import Coq.Program.Basics.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
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
