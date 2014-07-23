Require Import Closures.

(*
 * XXX
 * We should have more complete definitions of forward and backward
 * simulation, including initial and final states, and a progress
 * condition for backward simulation.  Compcert's definitions:
 *
 *    http://compcert.inria.fr/doc/html/Smallstep.html
 *
 * XXX
 * Do we need the order part of compcert's fsim/bsim?
 *
 * XXX
 * We should copy over a proof of backward simulation from forward
 * simulation and determinism.
 *)

Definition forward_simulation {StateA StateB:Type} (SA:StateA->StateA->Prop) (SB:StateB->StateB->Prop) :=
  exists (MATCH:StateA->StateB->Prop),
  forall A1 A2, SA A1 A2 -> 
  forall B1, MATCH A1 B1 ->
  exists B2, star SB B1 B2 /\ MATCH A2 B2.

Section backward_simulation.

Parameter StateA: Type.
Parameter StateB: Type.
Parameter StepA: StateA -> StateA -> Prop.
Parameter StepB: StateB -> StateB -> Prop.
Parameter Match: StateA -> StateB -> Prop.

Definition bsim_simulation :=
  forall B1 B2, StepB B1 B2 ->
  forall A1, Match A1 B1 ->
  exists A2, Match A2 B2 /\ plus StepA A1 A2.

End backward_simulation.

