Require Import StringMap.
Require Import String.
Open Scope string_scope.

Require Import Go.
Require Import GoExamples.

Definition go_functions : StringMap.t Go.stmt.
  apply StringMap.add. exact "hello".
  apply swap_example.
  apply StringMap.empty.
Defined.
