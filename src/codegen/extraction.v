Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Monad.
Require Import Fs4.

Extraction Blacklist List String Int.

Extract Constant state => "string".
Extract Constant IS => """""".

Extract Constant read_storage => "Fsstub._read_disk".
Extract Constant write_storage => "Fsstub._write_disk".

Cd "codegen".
Extraction Library Monad.
Extraction Library Fs4.

