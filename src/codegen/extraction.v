Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Fs4.

Extraction Blacklist List String Int.

Extract Constant state => "string".
Extract Constant IS => """""".

Extract Constant read_disk => "Fsstub._read_disk".
Extract Constant write_disk => "Fsstub._write_disk".

Cd "codegen".
Extraction Library Fs4.

