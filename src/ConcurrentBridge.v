Require Import CoopConcur.
Require Import ConcurrentCache.
Require Prog.

Definition valu_conv : valu -> word Prog.Valulen.valulen.
Proof.
  intro v.
  rewrite Prog.Valulen.valulen_is.
  exact v.
Defined.

Definition valu_conv' : word Prog.Valulen.valulen -> valu.
Proof.
  intro v.
  rewrite Prog.Valulen.valulen_is in v.
  exact v.
Defined.

Fixpoint compiler {T} (error_rx: prog Sigma) (p: Prog.prog T)  : prog Sigma :=
  match p with
  | Prog.Done v => Done
  | Prog.Read a rx => opt_v <- cache_maybe_read a;
                       match opt_v with
                       | Some v => compiler error_rx (rx (valu_conv v))
                       | None => v <- cache_fill a;
                                  error_rx
                       end
  | Prog.Write a v rx => ok <- cache_write a (valu_conv' v);
                          if ok then
                            compiler error_rx (rx tt)
                          else
                            _ <- Yield a;
                          error_rx
  | Prog.Sync a rx => _ <- cache_writeback a;
                       (* current concurrent disk model has no
                       asynchrony, but otherwise would need to issue
                       our own Sync here *)
                       compiler error_rx (rx tt)
  | Prog.Trim a rx => compiler error_rx (rx tt)
  end.