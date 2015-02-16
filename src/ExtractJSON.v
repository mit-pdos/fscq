Require Import FS.
Require Import Testprog.

Extraction Language JSON.

(* Optimize away [progseq]. *)
Extraction Inline Prog.progseq.

Cd "json".
Recursive Extraction Library FS.
Recursive Extraction Library Testprog.
