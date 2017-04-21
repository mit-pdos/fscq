Require Import OptimisticTranslator.
Require Prog.
Require CCLProg.

Import Prog.

Definition add_tuple (nums: nat * nat * nat) : prog nat :=
  n1 <- Ret (fst (fst nums));
    n2 <- Ret (snd (fst nums));
    n3 <- Ret (snd nums);
    Ret (n1+n2+n3).

Definition add_tuple_concur (nums: nat * nat * nat) :=
  translate (add_tuple nums) CCLProg.Locked empty_cache.

Import CCLProg.

Definition add_tuple_concur_raw (nums: nat * nat * nat) : cprog _ :=
  n1 <- CCLProg.Ret (fst (fst nums));
    n2 <- CCLProg.Ret (snd (fst nums));
    n3 <- CCLProg.Ret (snd nums);
    Ret (n1+n2+n3, empty_cache).
