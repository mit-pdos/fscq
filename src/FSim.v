Require Import Closures.

Definition forward_simulation {StateA StateB:Type} (SA:StateA->StateA->Prop) (SB:StateB->StateB->Prop) :=
  exists (MATCH:StateA->StateB->Prop),
  forall A1 A2, SA A1 A2 -> 
  forall B1, MATCH A1 B1 ->
  exists B2, star SB B1 B2 /\ MATCH A2 B2.
