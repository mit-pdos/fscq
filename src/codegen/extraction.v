Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import Disk.
Require Import DiskLog.
Require Import MemLog.
Require Import Trans.
Require Import Trans2.
Require Import Bank.
Require Import Storage.
Require Import Util.

Extraction Blacklist List String Int.

Cd "codegen".
Extraction Library Disk.
Extraction Library DiskLog.
Extraction Library MemLog.
Extraction Library Trans.
Extraction Library Trans2.
Extraction Library Bank.
Extraction Library Storage.
Extraction Library Util.
Extraction Library Datatypes.
Extraction Library Peano.
Extraction Library Peano_dec.

