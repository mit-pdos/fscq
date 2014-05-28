Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Monad.
Require Import Fs4.

Extraction Blacklist List String Int.

Extract Constant state => "string".
Extract Constant IS => """""".

Extract Constant st_init => "Fsstub._init_disk".
Extract Constant st_read => "Fsstub._read_disk".
Extract Constant st_write => "Fsstub._write_disk".

Cd "codegen".
Extraction Library Monad.
Extraction Library Fs4.
Extraction Library Datatypes.

