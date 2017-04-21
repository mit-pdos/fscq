Require Import OptimisticTranslator.
Require Prog.
Require CCLProg.

Import Prog.
Require Import BasicProg.
Require Import Bool.

Definition add_tuple (nums: nat * nat * nat) (b:bool) : prog nat :=
  If (bool_dec b true) {
       n1 <- Ret (fst (fst nums));
       n2 <- Ret (snd (fst nums));
       n3 <- Ret (snd nums);
       Ret (n1+n2+n3)
     } else {
    v <- Read 0;
    Ret 1
  }.

Definition add_tuple_concur (nums: nat * nat * nat) (b:bool) :=
  translate (add_tuple nums b) CCLProg.Locked empty_cache.
