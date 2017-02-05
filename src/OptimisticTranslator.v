Require Import Prog.
Require Import CCL.
Require Import AsyncDisk.
Require Import OptimisticCache WriteBuffer.
Require Import FunctionalExtensionality.

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

  Theorem spec_to_exec : forall tid A T (spec: Spec A T) a p,
      cprog_triple G tid spec p ->
      forall st out,
      exec G tid st p out ->
      precondition (spec a st) ->
      match out with
        | Finished sigma_i' sigma' v =>
          postcondition (spec a st) (sigma_i', sigma') v
        | Error => False
      end.
  Proof.
    unfold cprog_triple, ReflectDouble; intros.
    unfold cprog_ok at 1 in H.
    specialize (H _ Ret st).
    specialize (H (fun st' v => postcondition (spec a st) st' v)).
    specialize (H out).

    apply H.

    exists a; intuition eauto.
    unfold cprog_ok; intros.
    CCLTactics.inv_ret; intuition (subst; eauto).

    apply monad_right_id; auto.
  Qed.

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

  Theorem CacheRead_fail_oob : forall sigma wb a,
      CacheRep P wb sigma ->
      get_vdisk P (Sigma.s sigma) a = None ->
      forall tid sigma_i out, exec G tid (sigma_i, sigma) (CacheRead P wb a) out ->
                         out = Error.
  Proof.
    unfold CacheRead; intros.
    CCLTactics.inv_bind; eauto.
    eapply spec_to_exec in H6;
      eauto using BufferRead_oob;
      simpl in *;
      intuition eauto; subst.

    CCLTactics.inv_bind; eauto.
    CCLTactics.inv_exec; eauto.
    erewrite CacheRep_missing_cache in H9 by eauto.

    CCLTactics.inv_bind; eauto.
    match goal with
    | [ H: exec _ _ _ (BeginRead _) _ |- _ ] =>
      CCLTactics.inv_exec' H; eauto
    end.

    assert (Sigma.disk sigma' a = None).
    eapply CacheRep_missing_disk; eauto.

    congruence.

    Unshelve.
    all: exact tt.
  Qed.

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
          match r with
          | Success v =>
            Prog.exec (add_buffers (get_vdisk P (Sigma.s sigma)))
                      (Sigma.hm sigma) p
                      (Prog.Finished (add_buffers (get_vdisk P (Sigma.s sigma')))
                                     (Sigma.hm sigma') v)
          | Failed =>
          (* cache miss: anything to say is common to the success case and is
          outside this match *)
            True
          end
        | Error =>
            Prog.exec (add_buffers (get_vdisk P (Sigma.s sigma)))
                      (Sigma.hm sigma) p
                      (Prog.Failed _)
        end.
  Proof.
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
        eapply Prog.XStep; [ | eauto ].
        rewrite H2, H5. eauto.
      + (* error read *)
        CCLTactics.inv_bind.

        eapply CacheRead_fail_oob in H6; eauto.
        congruence.

        eauto.
    - case_eq (get_vdisk P (Sigma.s sigma) a); intros.
      + CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheWrite _ _ _ _) _ |- _ ] =>
            eapply spec_to_exec in H;
              eauto using CacheWrite_ok
          end; simpl in *; intuition eauto.
        destruct v0 as [? wb']; intuition.
        CCLTactics.inv_ret; intuition eauto.
        eapply Prog.XStep.
        rewrite H5.
        eapply Prog.StepWrite; eauto.
        rewrite H2. rewrite add_buffers_upd.
        apply possible_sync_upd_nil.
      + (* error write *)
        CCLTactics.inv_bind.

        admit. (* CacheWrite doesn't actually fail when writing out-of-bounds,
but it does break the CacheRep, so we can't prove the Finished case. Should be
ok to reduce the number of failing cases, but this requires that the resulting
execution be somewhat detached from the original. *)

        eauto.
    - CCLTactics.inv_ret; intuition eauto.
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
      destruct r; intuition eauto.
      eapply H in H10; eauto.
      destruct out.
      destruct r as [r wb'']; intuition eauto.
      eapply locally_modified_trans; eauto.
      congruence.
      destruct r; eauto.
      eapply Prog.XBindFinish; eauto.
      CCLTactics.inv_ret; intuition eauto.

      eapply IHp in H4; eauto.

      Unshelve.
      all: exact tt.
  Admitted.

End OptimisticTranslator.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)