Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import HoareLogicCont.

Extraction Blacklist List String Int.
Extract Constant HoareLogicCont.donetoken => "unit".

Cd "codegen".
Recursive Extraction Library HoareLogicCont.
