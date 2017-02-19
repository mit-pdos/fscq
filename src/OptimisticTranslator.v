Require Import Prog.
Require Import Pred.
Require Import CCL.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.
Require Import SeqSpecs.

Require Export OptimisticCache.

Inductive Result T := Success (v:T) | Failed.
Arguments Failed {T}.

Section OptimisticTranslator.

  Variable P:CacheParams.
  Variable G:Protocol.

  Fixpoint translate T (p: prog T) :
    WriteBuffer -> cprog (Result T * WriteBuffer) :=
    fun wb => match p with
           | Prog.Ret v => Ret (Success v, wb)
           | Prog.Read a => r <- CacheRead P wb a;
                             let '(v, wb) := r in
                             match v with
                             | Some v => Ret (Success v, wb)
                             | None => Ret (Failed, wb)
                             end
           | Prog.Write a v => r <- CacheWrite P wb a v;
                                let '(_, wb) := r in
                                Ret (Success tt, wb)
           | Prog.Sync => Ret (Success tt, wb)
           | Prog.Hash buf => v <- Hash buf;
                               Ret (Success v, wb)
           | Prog.Bind p1 p2 => r <- translate p1 wb;
                                 let '(r, wb) := r in
                                 match r with
                                 | Success v => translate (p2 v) wb
                                 | Failed => Ret (Failed, wb)
                                 end
           | Prog.Trim _ => Ret (Failed, wb)
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

  Lemma hashmap_le_refl_eq : forall hm hm',
      hm = hm' ->
      hashmap_le hm hm'.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Hint Resolve hashmap_le_refl_eq.

  Lemma spec_to_exec' : forall tid A T (spec: Spec A T) (p: cprog T),
      cprog_spec G tid spec p ->
      forall st out, exec G tid st p out ->
                (forall a, precondition (spec a st) ->
                      match out with
                      | Finished st' v => postcondition (spec a st) st' v
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

  Theorem translate_simulation : forall T (p: prog T),
      forall tid F sigma_i sigma vd0 vd out wb,
        (F * CacheRep P (Sigma.disk sigma) wb vd0 vd)%pred (Sigma.mem sigma) ->
        exec G tid (sigma_i, sigma) (translate p wb) out ->
        match out with
        | Finished (sigma_i', sigma') r =>
          let (r, wb') := r in
          exists vd',
            (F * CacheRep P (Sigma.disk sigma') wb' vd0 vd')%pred (Sigma.mem sigma') /\
            match r with
            | Success v =>
              Prog.exec (add_buffers vd) (Sigma.hm sigma) p
                        (Prog.Finished (add_buffers vd') (Sigma.hm sigma') v)
            | Failed =>
              (* cache miss: just give cache rep *)
              True
            end /\
            hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
            sigma_i' = sigma_i
        | Error =>
          (* concurrent code will never just fail - we will prove in these cases
          that the sequential program would have failed, to guarantee no new
          error cases have to be added (all based on having the CacheRep already
          hold) *)
          False
        end \/
        Prog.exec (add_buffers vd) (Sigma.hm sigma) p (Prog.Failed _).
  Proof.
    induction p; simpl; intros.
    - CCLTactics.inv_ret; intuition eauto.
    - case_eq (vd a); intros.
      + (* non-error read *)
        CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheRead _ _ _) _ |- _ ] =>
            apply_spec H CacheRead_ok
          end; intuition eauto.
        destruct st' as [sigma_i' sigma'].
        destruct v as [r wb']; intuition.
        destruct r; subst; CCLTactics.inv_ret;
          intuition eauto 10.
        left; descend; intuition eauto.
        eapply Prog.XStep; [ | eauto ].
        replace (Sigma.hm sigma').
        eauto.
      + (* error read *)
        right.
        CCLTactics.inv_bind; eauto.
    - case_eq (vd a); intros.
      + CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheWrite _ _ _ _) _ |- _ ] =>
            apply_spec H CacheWrite_ok
          end; intuition eauto.
        destruct st' as [sigma_i' sigma'].
        destruct v0 as [? wb']; intuition.
        CCLTactics.inv_ret; intuition eauto.
        left; descend; intuition eauto 10.
        eapply Prog.XStep.
        replace (Sigma.hm sigma').
        eapply Prog.StepWrite; eauto.
        rewrite add_buffers_upd.
        apply possible_sync_upd_nil.
      + (* error write *)
        CCLTactics.inv_bind; eauto.
    - left.
      CCLTactics.inv_ret; descend; intuition eauto.
      eapply Prog.XStep.
      econstructor.
      rewrite sync_mem_add_buffers; eauto.
    - CCLTactics.inv_ret; intuition eauto.
    - CCLTactics.inv_bind;
        match goal with
        | [ H: exec _ _ _ (Hash _) _ |- _ ] =>
          apply_spec H Hash_ok
        end; simpl in *; intuition eauto.
      destruct st' as [sigma_i' sigma']; simpl in *; intuition (subst; eauto).
      left.
      CCLTactics.inv_ret; descend; intuition eauto.
      destruct sigma; simpl; eauto.
      eapply Prog.XStep; eauto.
      destruct sigma; simpl in *.
      eauto.
      destruct sigma; simpl.
      hnf; eauto.
    - CCLTactics.inv_bind.
      eapply IHp in H6; eauto.
      destruct v as [r wb']; intuition eauto.
      destruct st' as [sigma_i' sigma']; deex; intuition eauto.
      destruct r; try CCLTactics.inv_ret; intuition eauto.
      + eapply H in H9; intuition eauto.
        left.
        destruct out; eauto.
        destruct sigma0 as [sigma_i'' sigma''].
        destruct r as [r wb'']; deex; intuition eauto.
        descend; intuition eauto.
        destruct r; eauto.
        etransitivity; eauto.
      + eapply IHp in H5; intuition eauto.
  Qed.

  Definition translate_spec A T (seq_spec: SeqSpec A T) :
    WriteBuffer -> Spec _ (Result T * WriteBuffer) :=
    fun wb '(a, F, vd0, vd) '(sigma_i, sigma) =>
      {| precondition :=
           (F * CacheRep P (Sigma.disk sigma) wb vd0 vd)%pred (Sigma.mem sigma) /\
           seq_pre (seq_spec a (Sigma.hm sigma)) (add_buffers vd);
         postcondition :=
           fun '(sigma_i', sigma') '(r, wb') =>
             (exists vd',
                 (F * CacheRep P (Sigma.disk sigma') wb' vd0 vd')%pred (Sigma.mem sigma') /\
                 match r with
                 | Success v => seq_post (seq_spec a (Sigma.hm sigma))
                                        (Sigma.hm sigma') v (add_buffers vd')
                 | Failed => True
                 end) /\
             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
             sigma_i' = sigma_i |}.

  Theorem translate_ok : forall T (p: prog T) A (spec: SeqSpec A T) tid wb,
      prog_quadruple spec p ->
      cprog_spec G tid (translate_spec spec wb) (translate p wb).
  Proof.
    unfold prog_quadruple; intros.
    apply triple_spec_equiv; unfold cprog_triple; intros.
    destruct st as [sigma_i sigma].
    destruct a as (((a & F) & vd0) & vd); simpl in *.
    eapply translate_simulation in H1; simpl in *; intuition eauto.
    - (* concurrent execution finished *)
      destruct out; eauto.
      destruct sigma0 as [sigma_i' sigma'].
      destruct r as [r wb']; deex; intuition eauto.
      destruct r; eauto.
      match goal with
      | [ Hexec: Prog.exec _ _ p _ |- _ ] =>
        eapply H in Hexec; eauto
      end.
    -
      (* rather than showing something about concurrent execution, simulation
      showed that the sequential program fails; rule out this possibility from
      the spec and precondition *)
      eapply H in H0; eauto; contradiction.
  Qed.

End OptimisticTranslator.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)