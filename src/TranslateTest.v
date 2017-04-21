Require Import OptimisticTranslator OptimisticCache.
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
  translate' (add_tuple nums b) CCLProg.Locked (caches empty_cache empty_cache).

Import CCLProg.

Definition add_tuple_concur_raw (nums: nat * nat * nat) (b:bool) : cprog _ :=
  match b with
  | true => 
       n1 <- Ret (fst (fst nums));
       n2 <- Ret (snd (fst nums));
       n3 <- Ret (snd nums);
       Ret (n1+n2+n3)
  | false => 
    _ <- CacheRead (caches empty_cache empty_cache) 0 CCLProg.Locked;
    Ret 1
  end.
