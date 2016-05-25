Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Import List.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.
Require Import WriteBuffer.

Section ConcurrentCache.

  Definition Sigma := defState [Cache; WriteBuffer] [Cache; WriteBuffer; DISK; Disk].

  Section Variables.

    Tactic Notation "var" constr(n) constr(f) :=
      let t := constr:(ltac:(hmember n (f Sigma))) in
      let t' := eval cbn in t in
          exact (t': var (f Sigma) _).

    Tactic Notation "mvar" constr(n) := var n mem_types.
    Tactic Notation "absvar" constr(n) := var n abstraction_types.

    (* memory variables *)
    Definition mCache := ltac:(mvar 0).
    Definition mWriteBuffer := ltac:(mvar 1).

    (* abstraction ("virtual") variables *)
    Definition vCache := ltac:(absvar 0).
    Definition vWriteBuffer := ltac:(absvar 1).
    (* the linearized disk, which evolves at each syscall *)
    Definition vDisk0 := ltac:(absvar 2).
    (* the disk from the perspective of the current syscall *)
    Definition vdisk := ltac:(absvar 3).

  End Variables.

  Definition no_wb_reader_conflict c wb :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Definition cacheI : Invariant Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      get mWriteBuffer m = get vWriteBuffer s /\
      cache_rep d (get vCache s) (get vDisk0 s) /\
      wb_rep (get vDisk0 s) (get vWriteBuffer s) (get vdisk s) /\
      no_wb_reader_conflict (get vCache s) (get vWriteBuffer s).

  (* not sure whether to say this about vDisk0, vDisk, or both *)
  Definition cacheR (tid:TID) : Relation Sigma :=
    fun s s' =>
      let vd := get vDisk0 s in
      let vd' := get vDisk0 s' in
      same_domain vd vd' /\
      (* a locking-like protocol, but true for any provable program
      due to the program semantics themselves *)
      (forall a v tid', vd a = Some (v, Some tid') ->
                   tid <> tid' ->
                   vd' a = Some (v, Some tid')).

  Hint Resolve same_domain_refl same_domain_trans.
  Hint Resolve lock_protocol_refl.

  Theorem cacheR_trans_closed : forall tid s s',
      star (cacheR tid) s s' ->
      cacheR tid s s'.
  Proof.
    intro tid.
    apply trans_closed; unfold cacheR; intuition eauto.
  Qed.

  Definition delta : Protocol Sigma :=
    defProtocol cacheI cacheR cacheR_trans_closed.

  (* abstraction helpers *)

  Definition modify_cache (up: Cache -> Cache) rx : prog Sigma :=
    c <- Get mCache;
      _ <- Assgn mCache (up c);
      _ <- var_update vCache up;
      rx tt.

  Definition modify_wb (up: WriteBuffer -> WriteBuffer) rx : prog Sigma :=
    wb <- Get mWriteBuffer;
      _ <- Assgn mWriteBuffer (up wb);
      _ <- var_update vWriteBuffer up;
      rx tt.

  (** safe read: returns None upon cache miss  *)
  Definition cache_maybe_read a rx : prog Sigma :=
    c <- Get mWriteBuffer;
      match wb_val c a with
      | Some v => rx (Some v)
      | None =>
        c <- Get mCache;
          rx (cache_val c a)
      end.

  Definition AsyncRead a rx : prog Sigma :=
    tid <- GetTID;
      _ <- StartRead_upd a;
      (* note that no updates to Disk are needed since the readers are
    hidden *)
      _ <- var_update vDisk0
        (fun vd => add_reader vd a tid);
      _ <- Yield a;
      v <- FinishRead_upd a;
      _ <- var_update vDisk0
        (fun vd => remove_reader vd a);
      rx v.

  Definition cache_fill a rx : prog Sigma :=
      (* invalidating + adding a reader makes the address locked,
      expressed via a reader locking protocol and restrictions on
      readers in cache_rep *)
    _ <- modify_cache (fun c => cache_invalidate c a);
      v <- AsyncRead a;
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      rx v.

  (** buffer a new write: fails (returns false) if the write overlaps
  with the address being read filled *)
  Definition cache_write a v rx : prog Sigma :=
    c <- Get mCache;
      match cache_get c a with
      | Invalid => rx false
      | _ =>
        _ <- modify_wb (fun wb => wb_write wb a v);
          _ <- var_update vdisk
            (fun vd => upd vd a v);
          rx true
      end.

  (** low level operation to move one value to the mCache *)
  Definition wb_evict a v rx : prog Sigma :=
    _ <- modify_cache (fun c => cache_add c a (Dirty v));
      _ <- var_update vDisk0
        (fun vd => upd vd a (v, None));
      rx tt.

  (** commit all the buffered writes into the global cache

    safety is provided by the invariant no_wb_reader_conflict enforced
    by cache_write's checks *)
  Definition cache_commit rx : prog Sigma :=
    c <- Get mCache;
      wb <- Get mWriteBuffer;
      (* need to wb_evict everything in wb_entries wb; requires list
      For loop *)
      _ <- Assgn mWriteBuffer emptyWriteBuffer;
      rx tt.

  (** abort all buffered writes, restoring vDisk0 *)
  Definition cache_abort rx : prog Sigma :=
    _ <- Assgn mWriteBuffer emptyWriteBuffer;
      _ <- GhostUpdate (fun s =>
                         let vd' := hide_readers (get vDisk0 s) in
                         set vdisk vd' s);
      rx tt.

  (* start of automation *)

  Lemma unfold_invariant : forall d m s,
      invariant delta d m s ->
      ltac:(let t := eval cbn in (invariant delta d m s) in
                let t := eval unfold cacheI in t in
                    exact t).
  Proof.
    auto.
  Qed.

  Ltac learn_invariant :=
    match goal with
    | [ H: invariant delta _ _ _ |- _ ] =>
      learn that (unfold_invariant H)
    end.

  Ltac prove_protocol :=
    match goal with
    | [ |- guar delta ?tid _ _ ] =>
      cbn; unfold cacheR
    end.

  Ltac descend :=
    match goal with
    | [ |- _ /\ _ ] => split
    | [ |- exists (_:unit), _ ] => exists tt
    end.

  Ltac reduce_hlist :=
    match goal with
    | [ |- context[get _ (set _ _ _) ] ] =>
      autorewrite with hlist
    end.

  Lemma wb_val_mem {m: memory Sigma} {s: abstraction Sigma} :
      get mWriteBuffer m = get vWriteBuffer s ->
      wb_val (get mWriteBuffer m) = wb_val (get vWriteBuffer s).
  Proof.
    congruence.
  Qed.

  Lemma cache_val_mem {m: memory Sigma} {s: abstraction Sigma} :
      get mCache m = get vCache s ->
      cache_val (get mCache m) = cache_val (get vCache s).
  Proof.
    congruence.
  Qed.

  Ltac replace_mem_val :=
    match goal with
    | [ H: get mWriteBuffer ?m = get vWriteBuffer _,
           H': context[ wb_val (get mWriteBuffer ?m) ] |- _ ] =>
      rewrite (wb_val_mem H) in H'
    | [ H: get mCache ?m = get vCache _,
           H': context[ cache_val (get mCache ?m) ] |- _ ] =>
      rewrite (cache_val_mem H) in H'
    end.

  Ltac simp_hook := fail.

  Ltac simplify_step :=
    match goal with
    | [ |- forall _, _ ] => intros
    | _ => learn_invariant
    | _ => deex
    | _ => progress destruct_ands
    | _ => inv_opt
    | _ => progress subst
    | _ => replace_mem_val
    | _ => reduce_hlist
    | _ => simp_hook
    | _ => descend
    | _ => prove_protocol
    end.

  Ltac finish := time "finish"
                      try solve [ eauto; congruence ].

  Ltac simplify :=
    repeat (time "simplify_step" simplify_step).

  (* prove hoare specs *)

  Theorem modify_cache_ok : forall up,
      SPEC delta, tid |-
              {{ (_:unit),
               | PRE d m s0 s: invariant delta d m s
               | POST d' m' s0' s' r: invariant delta d m s /\
                                      s' = set vCache (up (get vCache s)) s /\
                                      guar delta tid s s' /\
                                      s0' = s0
              }} modify_cache up.
  Proof.
    hoare pre simplify with finish.
  Qed.

  Hint Extern 1 {{ modify_cache _; _ }} => apply modify_cache_ok : prog.

  Theorem modify_wb_ok : forall up,
      SPEC delta, tid |-
              {{ (_:unit),
               | PRE d m s0 s: invariant delta d m s
               | POST d' m' s0' s' r: invariant delta d m s /\
                                      s' = set vWriteBuffer (up (get vWriteBuffer s)) s /\
                                      guar delta tid s s' /\
                                      s0' = s0
              }} modify_wb up.
  Proof.
    hoare pre simplify with finish.
  Qed.

  Hint Extern 1 {{ modify_wb _; _ }} => apply modify_wb_ok : prog.

  Hint Resolve wb_val_vd cache_val_vd wb_val_none.

  Theorem cache_maybe_read_ok : forall a,
      SPEC delta, tid |-
              {{ v0,
               | PRE d m s0 s: invariant delta d m s /\
                               get vdisk s a = Some v0
               | POST d' m' s0' s' r:
                   invariant delta d m s /\
                   s0' = s0 /\
                   forall v, r = Some v ->
                        v = v0
              }} cache_maybe_read a.
  Proof.
    hoare pre simplify with finish.
    (* for some reason, wb_val_none has a Hint doesn't work, but this
    does *)
    eauto using wb_val_none.
  Qed.

End ConcurrentCache.
