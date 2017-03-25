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

  Fixpoint translate' T (p: prog T) :
    LocalLock -> CacheSt -> cprog (Result T * CacheSt) :=
    fun l cs => match p with
           | Prog.Ret v => Ret (Success NoChange v, cs)
           | Prog.AlertModified => Ret (Success Modified tt, cs)
           | Prog.Read a => do '(v, cs) <- CacheRead cs a l;
                             match v with
                             | Some v => Ret (Success NoChange v, cs)
                             | None => Ret (Failure (CacheMiss a), cs)
                             end
           | Prog.Write a v => if l then
                                do '(_, cs) <- CacheWrite cs a v;
                                  Ret (Success NoChange tt, cs)
                              else
                                Ret (Failure WriteRequired, cs)
           | Prog.Sync => Ret (Success NoChange tt, cs)
           | Prog.Hash buf => v <- Hash buf;
                               Ret (Success NoChange v, cs)
           | Prog.Bind p1 p2 => do '(r, cs) <- translate' p1 l cs;
                                 match r with
                                 | Success f v =>
                                   do '(r', cs') <- translate' (p2 v) l cs;
                                     Ret (modified_or f r', cs')
                                 | Failure e => Ret (Failure e, cs)
                                 end
           (* unhandled programs - Trim and memory operations *)
           | _ => Ret (Failure Unsupported, cs)
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

  Definition translated_postcondition (l:LocalLock) d sigma c vd sigma' c' vd' :=
    let d' := if l then Sigma.disk sigma' else d in
    cache_rep d' c' vd' /\
    (l = Unacquired -> vd' = vd) /\
    (l = Unacquired -> c' = c) /\
    (l = Unacquired -> Sigma.disk sigma' = Sigma.disk sigma) /\
    hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
    Sigma.l sigma' = Sigma.l sigma /\
    Sigma.init_disk sigma' = Sigma.init_disk sigma.

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

  Lemma cache_rep_from_CacheRep : forall d cs vd0 vd,
      CacheRep d cs vd0 vd ->
      cache_rep d (cache cs) vd.
  Proof.
    unfold CacheRep; intuition eauto.
  Qed.

  Hint Resolve cache_rep_from_CacheRep.
  Hint Resolve local_locked.

  Theorem translate_simulation : forall T (p: prog T),
      forall tid sigma (F: heappred) d vd0 vd out l cs,
        F (Sigma.mem sigma) ->
        CacheRep d cs vd0 vd ->
        (l = Locked -> d = Sigma.disk sigma) ->
        local_l tid (Sigma.l sigma) = l ->
        exec G tid sigma (translate' p l cs) out ->
        match out with
        | Finished sigma' (r, cs') =>
          exists vd',
          F (Sigma.mem sigma') /\
          let d' := if l then Sigma.disk sigma' else d in
          CacheRep d' cs' vd0 vd' /\
          translated_postcondition l d sigma (cache cs) vd sigma' (cache cs') vd' /\
          (l = Unacquired -> cs' = cs) /\
          match r with
          | Success _ v =>
            Prog.exec (add_buffers vd) Mem.empty_mem (Sigma.hm sigma) p
                      (Prog.Finished (add_buffers vd') Mem.empty_mem (Sigma.hm sigma') v)
          | Failure e =>
            match e with
            | WriteRequired => l = Unacquired
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
                  | [ H: local_l ?tid (Sigma.l ?sigma) = Locked -> _ |- _ ] =>
                    destruct (local_l tid (Sigma.l sigma)); (intuition subst);
                      left; descend; intuition eauto 10
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
          left; descend; intuition (subst; eauto).
      + (* error read *)
        right.
        CCLTactics.inv_bind; eauto.
    - destruct l; simpl in *; intuition idtac.
      + case_eq (vd a); intros.
        * CCLTactics.inv_bind;
            match goal with
            | [ H: exec _ _ _ (CacheWrite _ _ _) _ |- _ ] =>
              apply_spec H CacheWrite_ok
            end; simplify; intuition eauto.
          CCLTactics.inv_ret; intuition eauto.
          left; descend; intuition (congruence || eauto).
        * (* error write *)
          CCLTactics.inv_bind; eauto.
      + CCLTactics.inv_ret; left; descend; intuition eauto using hashmap_le_refl.
    - CCLTactics.inv_bind;
        match goal with
        | [ H: exec _ _ _ (Hash _) _ |- _ ] =>
          apply_spec H Hash_ok
        end; simpl in *; intuition eauto.
      intuition (subst; eauto).
      left.

      destruct (local_l tid (Sigma.l sigma)); simpl in *; intuition subst;
        CCLTactics.inv_ret; descend; (intuition eauto); try congruence.
      replace (Sigma.disk sigma'); eauto.
      replace (Sigma.hm sigma'); eauto.
      eapply Prog.XStep; eauto.
      replace (Sigma.hm sigma'); eauto.
    - CCLTactics.inv_bind.
      match goal with
      | [ Hexec: exec _ _ _ (translate' _ _ _) _ |- _ ] =>
        eapply IHp in Hexec; eauto
      end.
      destruct v as [r c']; intuition eauto.
      deex; intuition eauto.
      destruct r; try CCLTactics.inv_ret; intuition eauto.
      + CCLTactics.inv_bind;
          try break_tuple;
          try CCLTactics.inv_ret;
          match goal with
          | [ Hexec: exec _ _ _ (translate' (p2 _) _ _) _ |- _ ] =>
            eapply H in Hexec; intuition eauto
          end.
        left.
        deex; intuition eauto.
        exists vd'0.
        destruct (local_l tid (Sigma.l sigma)); simpl in *; intuition (subst; eauto);
          try congruence.
        etransitivity; eauto.
        destruct f, r'; simpl; eauto.
        etransitivity; eauto.
        destruct f, r'; simpl; eauto.
        destruct (local_l tid (Sigma.l sigma)) eqn:?; congruence.
        destruct (local_l tid (Sigma.l sigma)) eqn:?; congruence.
        destruct (local_l tid (Sigma.l sigma)) eqn:?; congruence.
        destruct (local_l tid (Sigma.l sigma)) eqn:?; congruence.
      + left; descend; intuition eauto.
      + match goal with
        | [ Hexec: exec _ _ _ (translate' _ _ _) _ |- _ ] =>
          eapply IHp in Hexec; intuition eauto
        end.
  Qed.

  Theorem translate'_ok : forall T (p: prog T) A (seq_spec: SeqSpec A T) tid cs l,
      prog_quadruple seq_spec p ->
      cprog_spec G tid
                 (fun '(a, F, d, vd0, vd) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         CacheRep d cs vd0 vd /\
                         (l = Locked -> d = Sigma.disk sigma) /\
                         seq_pre (seq_spec a Mem.empty_mem (Sigma.hm sigma)) (add_buffers vd) /\
                         local_l tid (Sigma.l sigma) = l;
                       postcondition :=
                         fun sigma' '(r, cs') =>
                           (exists vd',
                               F (Sigma.mem sigma') /\
                               let d' := if  l then Sigma.disk sigma' else d in
                               CacheRep d' cs' vd0 vd' /\
                               translated_postcondition l d sigma (cache cs) vd sigma' (cache cs') vd' /\
                               (l = Unacquired -> cs' = cs) /\
                               match r with
                               | Success _ v => seq_post (seq_spec a Mem.empty_mem (Sigma.hm sigma))
                                                        Mem.empty_mem (Sigma.hm sigma') v (add_buffers vd')
                               | Failure e =>
                                 l = Locked -> e <> WriteRequired
                               end) |}) (translate' p l cs).
  Proof.
    unfold prog_quadruple; intros.
    apply triple_spec_equiv; unfold cprog_triple; intros.
    rename st into sigma.

    simpl in *; intuition; subst.
    repeat break_tuple; simpl in *.
    eapply translate_simulation in H1; intuition (subst; eauto).
    - (* concurrent execution finished *)
      destruct out; eauto.
      repeat break_tuple; deex; intuition (subst; eauto).

      destruct r0; eauto 10.
      match goal with
      | [ Hexec: Prog.exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; eauto 10
      end.
      descend; intuition eauto.
      subst; congruence.
    -
      (* rather than showing something about concurrent execution, simulation
      showed that the sequential program fails; rule out this possibility from
      the spec and precondition *)
      match goal with
      | [ Hexec: Prog.exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; eauto
      end; contradiction.
  Qed.

  Definition translate_spec A T (seq_spec: SeqSpec A T) tid l c :
    Spec _ (Result T * Cache) :=
    fun '(a, F, d, vd) sigma =>
      {| precondition :=
           F (Sigma.mem sigma) /\
           cache_rep d c vd /\
           (l = Locked -> d = Sigma.disk sigma) /\
           seq_pre (seq_spec a Mem.empty_mem (Sigma.hm sigma)) (add_buffers vd) /\
           local_l tid (Sigma.l sigma) = l;
         postcondition :=
           fun sigma' '(r, c') =>
             (exists vd',
                 F (Sigma.mem sigma') /\
                 translated_postcondition l d sigma c vd sigma' c' vd' /\
                 match r with
                 | Success _ v => seq_post (seq_spec a Mem.empty_mem (Sigma.hm sigma))
                                          Mem.empty_mem (Sigma.hm sigma') v (add_buffers vd')
                 | Failure e =>
                   (l = Locked -> e <> WriteRequired) /\
                   vd' = vd
                 end) |}.

  Definition translate T (p: prog T) l c :=
    cs <- CacheInit c;
    do '(r, cs) <- translate' p l cs;
      match r with
      | Success _ _ =>
        c <- CacheCommit cs;
          Ret (r, c)
      | Failure _ =>
        c <- CacheAbort cs;
          Ret (r, c)
      end.

  Hint Extern 1 {{ CacheInit _; _ }} => apply CacheInit_ok : prog.
  Hint Extern 1 {{ CacheCommit _; _ }} => apply CacheCommit_ok : prog.
  Hint Extern 1 {{ CacheAbort _; _ }} => apply CacheAbort_ok : prog.

  Ltac norm_eq :=
    repeat match goal with
           | [ H: _ = _ |- _ ] =>
             progress rewrite H in *
           | _ => progress subst
           end.

  Theorem translate_ok : forall T (p: prog T) A (spec: SeqSpec A T) tid c l,
      prog_quadruple spec p ->
      cprog_spec G tid (translate_spec spec tid l c) (translate p l c).
  Proof.
    unfold translate, translate_spec; intros.
    step; repeat break_tuple; simpl in *.
    descend; simpl in *; intuition eauto.

    monad_simpl.
    eapply cprog_ok_weaken; [ eapply translate'_ok; eauto | ];
      intros; simplify.
    descend; simpl in *; (intuition eauto); norm_eq; eauto.

    destruct a0; step;
      descend; simpl in *; intuition eauto.
    step; intuition; descend; intuition (norm_eq; eauto).
    unfold translated_postcondition in *; intuition (norm_eq; eauto).

    step; intuition; descend; intuition (norm_eq; eauto).
    unfold translated_postcondition in *; intuition (norm_eq; eauto).
  Qed.

End OptimisticTranslator.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)