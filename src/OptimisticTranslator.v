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

  Variable P:CacheParams.
  Variable G:TID -> Sigma -> Sigma -> Prop.

  Fixpoint translate T (p: prog T) :
    LockState -> WriteBuffer -> cprog (Result T * WriteBuffer) :=
    fun l wb => match p with
           | Prog.Ret v => Ret (Success v, wb)
           | Prog.Read a => r <- CacheRead P wb a l;
                             let '(v, wb) := r in
                             match v with
                             | Some v => Ret (Success v, wb)
                             | None => Ret (Failure (CacheMiss a), wb)
                             end
           | Prog.Write a v => if CanWrite l then
                                r <- CacheWrite P wb a v;
                                  let '(_, wb) := r in
                                  Ret (Success tt, wb)
                              else
                                Ret (Failure WriteRequired, wb)
           | Prog.Sync => Ret (Success tt, wb)
           | Prog.Hash buf => v <- Hash buf;
                               Ret (Success v, wb)
           | Prog.Bind p1 p2 => r <- translate p1 l wb;
                                 let '(r, wb) := r in
                                 match r with
                                 | Success v => translate (p2 v) l wb
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
                      | Finished sigma_i' sigma' v => postcondition (spec a st) (sigma_i', sigma') v
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
      forall tid sigma_i sigma F vd0 vd out l wb,
        (F * CacheRep P (Sigma.disk sigma) wb vd0 vd)%pred (Sigma.mem sigma) ->
        Sigma.l sigma = l ->
        ReadPermission l ->
        exec G tid (sigma_i, sigma) (translate p l wb) out ->
        match out with
        | Finished sigma_i' sigma' (r, wb') =>
          exists vd',
          (F * CacheRep P (Sigma.disk sigma') wb' vd0 vd')%pred (Sigma.mem sigma') /\
          Sigma.l sigma' = l /\
          (l = ReadLock -> vd' = vd) /\
          (l = ReadLock -> wb' = wb) /\
          sigma_i' = sigma_i /\
          match r with
          | Success v =>
            Prog.exec (add_buffers vd) Mem.empty_mem (Sigma.hm sigma) p
                      (Prog.Finished (add_buffers vd') Mem.empty_mem (Sigma.hm sigma') v)
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
        Prog.exec (add_buffers vd) Mem.empty_mem (Sigma.hm sigma) p (Prog.Failed _).
  Proof.
    induction p; simpl; intros;
      try solve [ CCLTactics.inv_ret; left; eauto 10 ].

    - case_eq (vd a); intros.
      + (* non-error read *)
        CCLTactics.inv_bind;
          match goal with
          | [ H: exec _ _ _ (CacheRead _ _ _ _) _ |- _ ] =>
            apply_spec H CacheRead_ok
          end; intuition eauto.
        destruct v as [r wb']; intuition.
        destruct r; subst; CCLTactics.inv_ret;
          intuition eauto 10.
      + (* error read *)
        right.
        CCLTactics.inv_bind; eauto.

    - match goal with
      | [ H: ReadPermission ?l |- _ ] =>
        destruct l; try solve [ inversion H ]; simpl in *
      end.
      + CCLTactics.inv_ret; eauto 10.
      + case_eq (vd a); intros.
        * CCLTactics.inv_bind;
            match goal with
            | [ H: exec _ _ _ (CacheWrite _ _ _ _) _ |- _ ] =>
              apply_spec H CacheWrite_ok
            end; intuition eauto.
          destruct v0 as [? wb']; intuition.
          CCLTactics.inv_ret; intuition eauto.
          left; descend; intuition (congruence || eauto).
        * (* error write *)
          CCLTactics.inv_bind; eauto.

    - left.
      CCLTactics.inv_ret; descend; intuition eauto.
      eapply Prog.XStep.
      econstructor.
      rewrite sync_mem_add_buffers; eauto.

    - CCLTactics.inv_bind;
        match goal with
        | [ H: exec _ _ _ (Hash _) _ |- _ ] =>
          apply_spec H Hash_ok
        end; simpl in *; intuition eauto.
      intuition (subst; eauto).
      left.
      CCLTactics.inv_ret; descend; (intuition eauto); try congruence.
      eapply Prog.XStep; eauto.
      replace (Sigma.hm sigma'0).
      eauto.

    - CCLTactics.inv_bind.
      match goal with
      | [ Hexec: exec _ _ _ (translate _ _ _) _ |- _ ] =>
        eapply IHp in Hexec; eauto
      end.
      destruct v as [r wb']; intuition eauto.
      deex; intuition eauto.
      destruct r; try CCLTactics.inv_ret; intuition eauto.
      + match goal with
          | [ Hexec: exec _ _ _ (translate (p2 _) _ _) _ |- _ ] =>
            eapply H in Hexec; intuition eauto
        end.
        left.
        destruct out; eauto.
        destruct sigma0 as [sigma_i'' sigma''].
        destruct r as [r wb'']; deex; intuition eauto.
        descend; (intuition eauto); try congruence.
        destruct r; eauto.
      + left; eauto 10.
      + match goal with
        | [ Hexec: exec _ _ _ (translate _ _ _) _ |- _ ] =>
          eapply IHp in Hexec; intuition eauto
        end.
  Qed.

  Definition translate_spec A T (seq_spec: SeqSpec A T) l wb :
    Spec _ (Result T * WriteBuffer) :=
    fun '(a, F, vd0, vd) '(sigma_i, sigma) =>
      {| precondition :=
           (F * CacheRep P (Sigma.disk sigma) wb vd0 vd)%pred (Sigma.mem sigma) /\
           seq_pre (seq_spec a Mem.empty_mem (Sigma.hm sigma)) (add_buffers vd) /\
           ReadPermission (Sigma.l sigma) /\
           l = Sigma.l sigma;
         postcondition :=
           fun '(sigma_i', sigma') '(r, wb') =>
             (exists vd',
                 (F * CacheRep P (Sigma.disk sigma') wb' vd0 vd')%pred (Sigma.mem sigma') /\
                 Sigma.l sigma' = l /\
                 (l = ReadLock -> vd' = vd) /\
                 hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                 match r with
                 | Success v => seq_post (seq_spec a Mem.empty_mem (Sigma.hm sigma))
                                        Mem.empty_mem (Sigma.hm sigma') v (add_buffers vd')
                 | Failure e =>
                   match e with
                   | WriteRequired => l = ReadLock
                   | _ => True
                   end
                 end) /\
             sigma_i' = sigma_i |}.

  Theorem translate_ok : forall T (p: prog T) A (spec: SeqSpec A T) tid wb l,
      prog_quadruple spec p ->
      cprog_spec G tid (translate_spec spec l wb) (translate p l wb).
  Proof.
    unfold prog_quadruple; intros.
    apply triple_spec_equiv; unfold cprog_triple; intros.
    destruct st.

    pose proof (CCLHashExec.exec_hashmap_le H1).

    simpl in *; intuition; subst.
    rename s into sigma_i, s0 into sigma.
    destruct a as (((a & F) & vd0) & vd); simpl in *.
    eapply translate_simulation in H1; intuition (subst; eauto).
    - (* concurrent execution finished *)
      destruct out; eauto.
      destruct r as [r wb']; deex; intuition (subst; eauto).

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