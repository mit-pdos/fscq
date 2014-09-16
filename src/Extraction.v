Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import Log.

Extract Constant Prog.donetoken => "unit".

Cd "codegen".
Recursive Extraction Library Log.
