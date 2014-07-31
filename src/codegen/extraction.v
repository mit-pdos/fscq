Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import HoareLogicN.

Extraction Blacklist List String Int.

Cd "codegen".
Recursive Extraction Library HoareLogicN.
