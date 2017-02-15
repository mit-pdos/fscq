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

Inductive Result T :=
| Success (v:T)
| Failure (e:OptimisticException).

Arguments Failure {T} e.

Section OptimisticTranslator.

  Variable OtherSt:StateTypes.
  Variable G:TID -> Sigma (St OtherSt) -> Sigma (St OtherSt) -> Prop.

  Fixpoint translate l T (p: prog T) :
    WriteBuffer -> @cprog (St OtherSt) (Result T * WriteBuffer) :=
    fun wb => match p with
           | Prog.Ret v => Ret (Success v, wb)
           | Prog.Read a => r <- CacheRead wb a l;
                             let '(v, wb) := r in
                             match v with
                             | Some v => Ret (Success v, wb)
                             | None => Ret (Failure (CacheMiss a), wb)
                             end
           | Prog.Write a v => if CanWrite l then
                                r <- CacheWrite wb a v;
                                  let '(_, wb) := r in
                                  Ret (Success tt, wb)
                              else
                                Ret (Failure WriteRequired, wb)
           | Prog.Sync => Ret (Success tt, wb)
           | Prog.Hash buf => v <- Hash buf;
                               Ret (Success v, wb)
           | Prog.Bind p1 p2 => r <- translate l p1 wb;
                                 let '(r, wb) := r in
                                 match r with
                                 | Success v => translate l (p2 v) wb
                                 | Failure e => Ret (Failure e, wb)
                                 end
           (* unhandled programs - Trim and memory operations *)
           | _ => Ret (Failure Unsupported, wb)
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
  Definition seq_disk (sigma: Sigma (St OtherSt)) : rawdisk :=
    add_buffers (vdisk (Sigma.s sigma)).

  Theorem translate_simulation : forall l T (p: prog T),
      forall tid sigma_i sigma out wb,
        CacheRep wb sigma ->
        Sigma.l sigma = l ->
        ReadPermission l ->
        exec G tid (sigma_i, sigma) (translate l p wb) out ->
        match out with
        | Finished sigma_i' sigma' r =>
          let (r, wb') := r in
          CacheRep wb' sigma' /\
           locally_modified sigma sigma' /\
           vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
           sigma_i' = sigma_i /\
          match r with
          | Success v =>
            Prog.exec (seq_disk sigma) Mem.empty_mem (Sigma.hm sigma) p
                      (Prog.Finished (seq_disk sigma') Mem.empty_mem (Sigma.hm sigma') v)
          | Failure e =>
            match e with
            | WriteRequired => l = ReadLock
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
        Prog.exec (seq_disk sigma) Mem.empty_mem (Sigma.hm sigma) p (Prog.Failed _).
  Proof.
    unfold seq_disk.
    induction p; simpl; intros;
      try solve [ CCLTactics.inv_ret; intuition eauto ].
    - case_eq (vdisk (Sigma.s sigma) a); intros.
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
        match goal with
        | [ H: Sigma.hm _ = Sigma.hm _,
               H': vdisk _ = vdisk _ |- _ ] =>
          rewrite H, H'
        end.
        eauto.
      + (* error read *)
        right.
        CCLTactics.inv_bind; eauto.
    - case_eq (vdisk (Sigma.s sigma) a); intros.
      + destruct (CanWrite l).
        CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheWrite _ _ _) _ |- _ ] =>
            eapply spec_to_exec in H;
              eauto using CacheWrite_ok
          end; simpl in *; intuition eauto.
        destruct v0 as [? wb']; intuition.
        CCLTactics.inv_ret; intuition eauto.
        left; intuition eauto.
        eapply Prog.XStep.
        match goal with
        | [ H: Sigma.hm _ = Sigma.hm _ |- _ ] =>
          rewrite H
        end.
        eapply Prog.StepWrite; eauto.
        match goal with
        | [ H: vdisk _ = _ |- _ ] =>
          rewrite H
        end.
        rewrite add_buffers_upd.
        apply possible_sync_upd_nil.

        CCLTactics.inv_ret; intuition eauto.
        match goal with
        | [ H: ReadPermission _ |- _ ] =>
          inversion H; intuition eauto; try congruence
        end.
      + (* error write *)
        destruct (CanWrite l).
        CCLTactics.inv_bind; eauto.
        CCLTactics.inv_ret; eauto.
    - left.
      CCLTactics.inv_ret; intuition eauto.
      eapply Prog.XStep.
      econstructor.
      rewrite sync_mem_add_buffers; eauto.
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
      match goal with
      | [ Hexec: exec _ _ _ (translate _ p _) _ |- _ ] =>
        eapply IHp in Hexec; eauto
      end.
      destruct v as [r wb']; intuition eauto.
      destruct r; try CCLTactics.inv_ret; intuition eauto.
      + match goal with
        | [ Hexec: exec _ _ _ (translate _ (p2 _) _) _ |- _ ] =>
          eapply H in Hexec; intuition eauto
        end.
        left.
        destruct out; eauto.
        destruct r as [r wb'']; intuition eauto.
        eapply locally_modified_trans; eauto.
        congruence.
        congruence.
        destruct r; eauto.

        auto using locally_modified_lock_preserved.
      + match goal with
        | [ Hexec: exec _ _ _ (translate _ p _) _ |- _ ] =>
          eapply IHp in Hexec; eauto
        end.
        intuition.

      Unshelve.
      all: exact tt.
  Qed.

  Definition translate_spec A T (seq_spec: SeqSpec A T) wb l :
    Spec A (Result T * WriteBuffer) :=
    fun a '(sigma_i, sigma) =>
      {| precondition :=
           seq_pre (seq_spec a Mem.empty_mem (Sigma.hm sigma)) (seq_disk sigma) /\
           ReadPermission (Sigma.l sigma) /\
           l = Sigma.l sigma /\
           CacheRep wb sigma;
         postcondition :=
           fun '(sigma_i', sigma') '(r, wb) =>
             CacheRep wb sigma' /\
             locally_modified sigma sigma' /\
             vdisk_committed (Sigma.s sigma') = vdisk_committed (Sigma.s sigma) /\
             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
             match r with
             | Success v => seq_post (seq_spec a Mem.empty_mem (Sigma.hm sigma))
                                    Mem.empty_mem (Sigma.hm sigma') v (seq_disk sigma')
             | Failure e =>
               match e with
               | WriteRequired => l = ReadLock
               | _ => True
               end
             end /\
             sigma_i' = sigma_i |}.

  Theorem translate_ok : forall T (p: prog T) A (spec: SeqSpec A T) tid wb l,
      prog_quadruple spec p ->
      cprog_spec G tid (translate_spec spec wb l) (translate l p wb).
  Proof.
    unfold prog_quadruple; intros.
    apply triple_spec_equiv; unfold cprog_triple; intros.
    destruct st.

    pose proof (CCLHashExec.exec_hashmap_le H1).

    simpl in *; intuition; subst.
    eapply translate_simulation in H1; intuition eauto; subst.
    - (* concurrent execution finished *)
      destruct out; eauto.
      destruct r as [r wb']; intuition eauto.

      destruct r; eauto.
      match goal with
      | [ Hexec: Prog.exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; eauto
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