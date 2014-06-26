Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import DiskLog.
Require Import MemLog.
Require Import Trans.
Require Import Bank.
Require Import Storage.

Extraction Blacklist List String Int.

Cd "codegen".
Extraction Library DiskLog.
Extraction Library MemLog.
Extraction Library Trans.
Extraction Library Bank.
Extraction Library Storage.
Extraction Library Datatypes.
Extraction Library Peano.
Extraction Library Peano_dec.

