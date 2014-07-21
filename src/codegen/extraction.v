Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import Disk.
Require Import DiskLog.
Require Import MemLog.
Require Import Trans.
Require Import Trans2.
Require Import Storage.
Require Import Util.
Require Import FileSpec.
Require Import FsLayout.
Require Import Balloc.
Require Import File.

Extraction Blacklist List String Int.

Cd "codegen".
Extraction Library Disk.
Extraction Library DiskLog.
Extraction Library MemLog.
Extraction Library Trans.
Extraction Library Trans2.
Extraction Library Storage.
Extraction Library Util.
Extraction Library FileSpec.
Extraction Library FsLayout.
Extraction Library Balloc.
Extraction Library File.

Extraction Library Datatypes.
Extraction Library Peano.
Extraction Library Peano_dec.
Extraction Library Compare_dec.
Extraction Library NPeano.
Extraction Library Bool.
Extraction Library Div2.

