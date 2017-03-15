Require Import Prog.
Require Import Hashmap.
Require Import CCL.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.
Require Import SeqSpecs.

Require Export OptimisticCache.

Inductive OptimisticException :=
| CacheMiss (a:addr)
| Unsupported
| WriteRequired.

Inductive ModifiedFlag := NoChange | Modified.

Inductive Result T :=
| Success (f:ModifiedFlag) (v:T)
| Failure (e:OptimisticException).
Arguments Failure {T} e.

Definition modified_or T (f1:ModifiedFlag) (r:Result T) : Result T :=
  match f1 with
  | NoChange => r
  | Modified => match r with
               | Success _ v => Success Modified v
               | Failure e => Failure e
               end
  end.

Section OptimisticTranslator.

  Variable G:TID -> Sigma -> Sigma -> Prop.

  Fixpoint translate T (p: prog T) :
    LockState -> Cache -> cprog (Result T * Cache) :=
    fun l c => match p with
           | Prog.Ret v => Ret (Success NoChange v, c)
           | Prog.AlertModified => Ret (Success Modified tt, c)
           | Prog.Read a => do '(v, c) <- CacheRead c a l;
                             match v with
                             | Some v => Ret (Success NoChange v, c)
                             | None => Ret (Failure (CacheMiss a), c)
                             end
           | Prog.Write a v => if CanWrite l then
                                do '(_, c) <- CacheWrite c a v;
                                  Ret (Success NoChange tt, c)
                              else
                                Ret (Failure WriteRequired, c)
           | Prog.Sync => Ret (Success NoChange tt, c)
           | Prog.Hash buf => v <- Hash buf;
                               Ret (Success NoChange v, c)
           | Prog.Bind p1 p2 => do '(r, c) <- translate p1 l c;
                                 match r with
                                 | Success f v =>
                                   do '(r', c') <- translate (p2 v) l c;
                                     Ret (modified_or f r', c')
                                 | Failure e => Ret (Failure e, c)
                                 end
           (* unhandled programs - Trim and memory operations *)
           | _ => Ret (Failure Unsupported, c)
           end.

  Definition add_buffers (d: Disk) : rawdisk :=
    fun a => match d a with
          | Some v => Some (v, nil)
          | None => None
          end.

  Hint Resolve PredCrash.possible_sync_refl.

  Lemma add_buffers_eq : forall vd a v,
      vd a = Some v ->
      add_buffers vd a = Some (v, nil).
  Proof.
    unfold add_buffers; intros; simpl_match; eauto.
  Qed.

  Lemma add_buffers_none : forall vd a,
      vd a = None ->
      add_buffers vd a = None.
  Proof.
    unfold add_buffers; intros; simpl_match; eauto.
  Qed.

  Lemma add_buffers_upd : forall vd a v,
      add_buffers (Mem.upd vd a v) = Mem.upd (add_buffers vd) a (v, nil).
  Proof.
    unfold add_buffers; intros.
    extensionality a'.
    destruct (addr_eq_dec a a'); subst; autorewrite with upd; eauto.
  Qed.

  Hint Resolve add_buffers_eq.
  Hint Resolve add_buffers_none.
  Hint Resolve add_buffers_upd.

  Hint Constructors Prog.exec Prog.step Prog.fail_step.

  (* TODO: move to PredCrash *)
  Lemma possible_sync_upd_nil : forall A AEQ (m: @Mem.mem A AEQ _) a v v0,
      PredCrash.possible_sync
        (Mem.upd m a (v, (cons v0 nil)))
        (Mem.upd m a (v, nil)).
  Proof.
    unfold PredCrash.possible_sync; intros.
    destruct (AEQ a a0); subst; autorewrite with upd.
    right; repeat eexists; intuition eauto.
    constructor; contradiction.

    case_eq (m a0); intuition eauto.
    destruct p; eauto 10 using List.incl_refl.
  Qed.

  Lemma sync_mem_add_buffers : forall vd,
      sync_mem (AEQ:=addr_eq_dec) (add_buffers vd) = add_buffers vd.
  Proof.
    unfold sync_mem, add_buffers; intros.
    extensionality a.
    destruct (vd a); eauto.
  Qed.

  Lemma exec_read : forall vd vd' m hm hm' a v,
      vd = vd' ->
      hm = hm' ->
      vd a = Some v ->
      Prog.exec (add_buffers vd) m hm
                (Read a) (Prog.Finished (add_buffers vd') m hm' v).
  Proof.
    intros; subst.
    eapply Prog.XStep; eauto.
  Qed.

  Hint Resolve exec_read.

  Lemma exec_write : forall vd vd' m hm hm' a v v0,
      vd a = Some v0 ->
      vd' = Mem.upd vd a v ->
      hm = hm' ->
      Prog.exec (add_buffers vd) m hm
                (Prog.Write a v) (Prog.Finished (add_buffers vd') m hm' tt).
  Proof.
    intros; subst.
    eapply Prog.XStep.
    eapply Prog.StepWrite; eauto.
    rewrite add_buffers_upd.
    apply possible_sync_upd_nil.
  Qed.

  Hint Resolve exec_write.

  Lemma exec_hash : forall vd vd' m hm hm' sz (buf: Word.word sz),
      vd = vd' ->
      hash_safe hm (hash_fwd buf) buf ->
      hm' = upd_hashmap' hm (hash_fwd buf) buf ->
      Prog.exec (add_buffers vd) m hm
                (Prog.Hash buf)
                (Prog.Finished (add_buffers vd') m hm' (hash_fwd buf)).
  Proof.
    intros; subst.
    eapply Prog.XStep; eauto.
  Qed.

  Lemma spec_to_exec' : forall tid A T (spec: Spec A T) (p: cprog T),
      cprog_spec G tid spec p ->
      forall st out, exec G tid st p out ->
                (forall a, precondition (spec a st) ->
                      match out with
                      | Finished sigma' v => postcondition (spec a st) sigma' v
                      | Error => False
                      end).
  Proof.
    intros.
    eapply spec_to_exec; eauto.
  Qed.

  Lemma forall_tuple : forall A B (P: A * B -> Prop),
      (forall p, P p) ->
      (forall a b, P (a, b)).
  Proof.
    eauto.
  Qed.

  Ltac destruct_forall H :=
    let Htemp := fresh in
    pose proof (forall_tuple _ H) as Htemp;
    simpl in Htemp;
    clear H;
    rename Htemp into H.

  Ltac apply_spec H pf :=
    let Htemp := fresh in
    pose proof (spec_to_exec' ltac:(eauto using pf) H) as Htemp;
    repeat destruct_forall Htemp;
    repeat lazymatch type of Htemp with
           | (forall (x:?A), _) =>
             match type of A with
             | Prop => specialize (Htemp ltac:(eauto))
             | _ => let x := fresh x in
                   evar (x:A);
                   specialize (Htemp x);
                   subst x
             end
           end;
    clear H;
    rename Htemp into H.

  Lemma prog_exec_add_buffers : forall d m hm,
      Prog.exec (add_buffers d) m hm Sync
                (Prog.Finished (add_buffers d) m hm tt).
  Proof.
    intros.
    eapply Prog.XStep.
    econstructor.
    rewrite sync_mem_add_buffers; eauto.
  Qed.

  Hint Resolve prog_exec_add_buffers.

  Hint Extern 2 (_ = _ -> _ = _) => intros; congruence.

  (* workaround https://coq.inria.fr/bugs/show_bug.cgi?id=5394 (congruence does
  a [repeat intro], which unfolds CacheRep) *)
  Opaque CacheRep.

  Definition translated_postcondition l d sigma c vd sigma' c' vd' :=
    let d' := if CanWrite l then Sigma.disk sigma' else d in
    CacheRep d' c' vd' /\
    (l = Free -> vd' = vd) /\
    (l = Free -> c' = c) /\
    (l = Free -> Sigma.disk sigma' = Sigma.disk sigma) /\
    hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
    Sigma.l sigma' = Sigma.l sigma.

  Lemma hashmap_le_refl_eq : forall hm hm',
      hm = hm' ->
      hashmap_le hm hm'.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma hashmap_le_upd : forall hm hm' sz (buf: Word.word sz),
      hm' = upd_hashmap' hm (hash_fwd buf) buf ->
      hash_safe hm (hash_fwd buf) buf ->
      hashmap_le hm hm'.
  Proof.
    intros; subst.
    unfold hashmap_le; eexists; eauto using HS_nil, HS_cons.
  Qed.

  Hint Resolve hashmap_le_refl_eq hashmap_le_upd.

  Theorem translate_simulation : forall T (p: prog T),
      forall tid sigma (F: heappred) d vd out l c,
        F (Sigma.mem sigma) ->
        CacheRep d c vd ->
        (l = WriteLock -> d = Sigma.disk sigma) ->
        CacheRep d c vd ->
        Sigma.l sigma = l ->
        exec G tid sigma (translate p l c) out ->
        match out with
        | Finished sigma' (r, c') =>
          exists vd',
          F (Sigma.mem sigma') /\
          translated_postcondition l d sigma c vd sigma' c' vd' /\
          match r with
          | Success _ v =>
            Prog.exec (add_buffers vd) Mem.empty_mem (Sigma.hm sigma) p
                      (Prog.Finished (add_buffers vd') Mem.empty_mem (Sigma.hm sigma') v)
          | Failure e =>
            match e with
            | WriteRequired => l = Free
            | _ => True
            end
          (* cache miss, unsupported operation, or need to upgrade lock: mostly
            give consistency properties (listed outside match) *)
          end
        | Error =>
          (* concurrent code will never just fail - we will prove in these cases
          that the sequential program would have failed, to guarantee no new
          error cases have to be added (all based on having the CacheRep already
          hold) *)
          False
        end \/
        Prog.exec (add_buffers vd) Mem.empty_mem (Sigma.hm sigma) p (Prog.Failed _).
  Proof.
    unfold translated_postcondition.
    induction p; simpl; intros;
      try solve [ CCLTactics.inv_ret;
                  match goal with
                  | [ H: Sigma.l ?sigma = WriteLock -> _ |- _ ] =>
                    destruct (Sigma.l sigma); (intuition subst);
                      left; eauto 10
                  end ].
    - case_eq (vd a); intros.
      + (* non-error read *)
        CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheRead _ _ _) _ |- _ ] =>
            apply_spec H CacheRead_ok
          end; intuition eauto.
        destruct v as [r c']; intuition.
        destruct r; subst; CCLTactics.inv_ret;
          left; descend; intuition eauto.
      + (* error read *)
        right.
        CCLTactics.inv_bind; eauto.

    - destruct l; simpl in *; intuition idtac.
      + CCLTactics.inv_ret; eauto 10.
      + case_eq (vd a); intros.
        * CCLTactics.inv_bind;
            match goal with
            | [ H: exec _ _ _ (CacheWrite _ _ _) _ |- _ ] =>
              apply_spec H CacheWrite_ok
            end; intuition eauto.
          destruct v0 as [? c']; intuition.
          CCLTactics.inv_ret; intuition eauto.
          left; descend; intuition (congruence || eauto).
        * (* error write *)
          CCLTactics.inv_bind; eauto.

    - CCLTactics.inv_bind;
        match goal with
        | [ H: exec _ _ _ (Hash _) _ |- _ ] =>
          apply_spec H Hash_ok
        end; simpl in *; intuition eauto.
      intuition (subst; eauto).
      left.

      destruct (Sigma.l sigma); simpl in *; intuition subst;
        CCLTactics.inv_ret; descend; (intuition eauto); try congruence.
      eapply Prog.XStep; eauto.
      replace (Sigma.hm sigma'0); eauto.
      replace (Sigma.hm sigma'0); eauto.

    - CCLTactics.inv_bind.
      match goal with
      | [ Hexec: exec _ _ _ (translate _ _ _) _ |- _ ] =>
        eapply IHp in Hexec; eauto
      end.
      destruct v as [r c']; intuition eauto.
      deex; intuition eauto.
      destruct r; try CCLTactics.inv_ret; intuition eauto.
      + CCLTactics.inv_bind;
          try match goal with
              | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
                let a := fresh a in
                let b := fresh b in
                destruct p as [a b]
              end;
          try CCLTactics.inv_ret;
          match goal with
          | [ Hexec: exec _ _ _ (translate (p2 _) _ _) _ |- _ ] =>
            eapply H in Hexec; intuition eauto
          end.
        left.
        deex; intuition eauto.
        exists vd'0.
        destruct (Sigma.l sigma); simpl in *; intuition (subst; eauto);
          try congruence.
        etransitivity; eauto.
        destruct f, r'; simpl; eauto.
        etransitivity; eauto.
        destruct f, r'; simpl; eauto.
        destruct (Sigma.l sigma); simpl in *; intuition (subst; eauto);
          try congruence.
        destruct (Sigma.l sigma); simpl in *; intuition (subst; eauto);
          try congruence.
      + left; eauto 10.
      + match goal with
        | [ Hexec: exec _ _ _ (translate _ _ _) _ |- _ ] =>
          eapply IHp in Hexec; intuition eauto
        end.
  Qed.

  Definition translate_spec A T (seq_spec: SeqSpec A T) l c :
    Spec _ (Result T * Cache) :=
    fun '(a, F, d, vd) sigma =>
      {| precondition :=
           F (Sigma.mem sigma) /\
           CacheRep d c vd /\
           (l = WriteLock -> d = Sigma.disk sigma) /\
           seq_pre (seq_spec a Mem.empty_mem (Sigma.hm sigma)) (add_buffers vd) /\
           Sigma.l sigma = l;
         postcondition :=
           fun sigma' '(r, c') =>
             (exists vd',
                 F (Sigma.mem sigma') /\
                 translated_postcondition l d sigma c vd sigma' c' vd' /\
                 match r with
                 | Success _ v => seq_post (seq_spec a Mem.empty_mem (Sigma.hm sigma))
                                          Mem.empty_mem (Sigma.hm sigma') v (add_buffers vd')
                 | Failure e =>
                   match e with
                   | WriteRequired => l = Free
                   | _ => True
                   end
                 end) |}.

  Theorem translate_ok : forall T (p: prog T) A (spec: SeqSpec A T) tid c l,
      prog_quadruple spec p ->
      cprog_spec G tid (translate_spec spec l c) (translate p l c).
  Proof.
    unfold prog_quadruple; intros.
    apply triple_spec_equiv; unfold cprog_triple; intros.
    rename st into sigma.

    simpl in *; intuition; subst.
    destruct a as (((a & F) & d) & vd); simpl in *.
    eapply translate_simulation in H1; intuition (subst; eauto).
    - (* concurrent execution finished *)
      destruct out; eauto.
      destruct r as [r c']; deex; intuition (subst; eauto).

      destruct r; eauto 10.
      match goal with
      | [ Hexec: Prog.exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; eauto 10
      end.
    -
      (* rather than showing something about concurrent execution, simulation
      showed that the sequential program fails; rule out this possibility from
      the spec and precondition *)
      match goal with
      | [ Hexec: Prog.exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; eauto
      end; contradiction.
  Qed.

End OptimisticTranslator.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)