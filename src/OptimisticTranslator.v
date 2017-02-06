Require Import Prog.
Require Import CCL.
Require Import AsyncDisk.
Require Import WriteBuffer.
Require Import FunctionalExtensionality.
Require Import SeqSpecs.

Require Export OptimisticCache.

Inductive Result T := Success (v:T) | Failed.
Arguments Failed {T}.

Section OptimisticTranslator.

  Variable St:StateTypes.
  Variable G:TID -> Sigma St -> Sigma St -> Prop.

  Variable P:CacheParams St.

  Fixpoint translate T (p: prog T) :
    WriteBuffer -> @cprog St (Result T * WriteBuffer) :=
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

  Hint Resolve locally_modified_refl.

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

  (* The relation between the concurrent state and the sequential disk state,
  expressed as projecting the sequential disk from the concurrent state. The
  sequential state also includes a hashmap, which can already be projected with
  [Sigma.hm]. *)
  Definition seq_disk sigma : rawdisk :=
    add_buffers (get_vdisk P (Sigma.s sigma)).

  Theorem translate_simulation : forall T (p: prog T),
      forall tid sigma_i sigma out wb,
        CacheRep P wb sigma ->
        exec G tid (sigma_i, sigma) (translate p wb) out ->
        match out with
        | Finished sigma_i' sigma' r =>
          let (r, wb') := r in
          CacheRep P wb' sigma' /\
           locally_modified P sigma sigma' /\
           get_vdisk0 P (Sigma.s sigma') = get_vdisk0 P (Sigma.s sigma) /\
           sigma_i' = sigma_i /\
          match r with
          | Success v =>
            Prog.exec (seq_disk sigma) (Sigma.hm sigma) p
                      (Prog.Finished (seq_disk sigma') (Sigma.hm sigma') v)
          | Failed =>
            (* cache miss: just give consistency properties (listed outside
            match) *)
            True
          end
        | Error =>
          (* concurrent code will never just fail - we will prove in these cases
          that the sequential program would have failed, to guarantee no new
          error cases have to be added (all based on having the CacheRep already
          hold) *)
          False
        end \/
        Prog.exec (seq_disk sigma) (Sigma.hm sigma) p (Prog.Failed _).
  Proof.
    unfold seq_disk.
    induction p; simpl; intros.
    - CCLTactics.inv_ret; intuition eauto.
    - case_eq (get_vdisk P (Sigma.s sigma) a); intros.
      + (* non-error read *)
        CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheRead _ _ _) _ |- _ ] =>
            eapply spec_to_exec in H;
              eauto using CacheRead_ok
          end; simpl in *; intuition eauto.
        destruct v as [r wb']; intuition.
        destruct r; subst; CCLTactics.inv_ret;
          intuition eauto.
        left; intuition eauto.
        eapply Prog.XStep; [ | eauto ].
        rewrite H2, H5.
        eauto.
      + (* error read *)
        right.
        CCLTactics.inv_bind; eauto.
    - case_eq (get_vdisk P (Sigma.s sigma) a); intros.
      + CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheWrite _ _ _ _) _ |- _ ] =>
            eapply spec_to_exec in H;
              eauto using CacheWrite_ok
          end; simpl in *; intuition eauto.
        destruct v0 as [? wb']; intuition.
        CCLTactics.inv_ret; intuition eauto.
        left; intuition eauto.
        eapply Prog.XStep.
        rewrite H5.
        eapply Prog.StepWrite; eauto.
        rewrite H2. rewrite add_buffers_upd.
        apply possible_sync_upd_nil.
      + (* error write *)
        CCLTactics.inv_bind; eauto.
    - left.
      CCLTactics.inv_ret; intuition eauto.
      eapply Prog.XStep.
      econstructor.
      rewrite sync_mem_add_buffers; eauto.
    - CCLTactics.inv_ret; intuition eauto.
    - CCLTactics.inv_bind;
        match goal with
        | [ H: exec _ _ _ (Hash _) _ |- _ ] =>
          eapply spec_to_exec in H;
            eauto using Hash_ok
        end; simpl in *; intuition (subst; eauto).
      left.
      CCLTactics.inv_ret; intuition eauto.
      unfold CacheRep; destruct sigma; eauto.
      apply locally_modified_hashmap.
      destruct sigma; simpl; auto.
      eapply Prog.XStep; eauto.
      destruct sigma; simpl in *.
      eauto.
    - CCLTactics.inv_bind.
      eapply IHp in H6; eauto.
      destruct v as [r wb']; intuition eauto.
      destruct r; try CCLTactics.inv_ret; intuition eauto.
      + eapply H in H10; intuition eauto.
        left.
        destruct out; eauto.
        destruct r as [r wb'']; intuition eauto.
        eapply locally_modified_trans; eauto.
        congruence.
        congruence.
        destruct r; eauto.
      + apply IHp in H4; intuition.

      Unshelve.
      all: exact tt.
  Qed.

  Definition translate_spec A T (seq_spec: SeqSpec A T) :
    WriteBuffer -> Spec A (Result T * WriteBuffer) :=
    fun wb a '(sigma_i, sigma) =>
      {| precondition :=
           seq_pre (seq_spec a (Sigma.hm sigma)) (seq_disk sigma) /\
           CacheRep P wb sigma;
         postcondition :=
           fun '(sigma_i', sigma') '(r, wb) =>
             CacheRep P wb sigma' /\
             locally_modified P sigma sigma' /\
             match r with
             | Success v => seq_post (seq_spec a (Sigma.hm sigma))
                                    (Sigma.hm sigma') v (seq_disk sigma')
             | Failed => True
             end /\
             sigma_i' = sigma_i |}.

  Theorem translate_ok : forall T (p: prog T) A (spec: SeqSpec A T) tid wb,
      prog_quadruple spec p ->
      cprog_spec G tid (translate_spec spec wb) (translate p wb).
  Proof.
    unfold prog_quadruple; intros.
    apply triple_spec_equiv; unfold cprog_triple; intros.
    destruct st.
    eapply translate_simulation in H1; simpl in *; intuition eauto.
    - (* concurrent execution finished *)
      destruct out; eauto.
      destruct r as [r wb']; intuition eauto.
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