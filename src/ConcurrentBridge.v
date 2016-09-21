Require Import CoopConcur.
Require Import ConcurrentCache.
Require Import Specifications.
Require Import CoopConcurMonad.
Import HlistNotations.

Module MakeBridge (C:CacheSubProtocol).

  Module ConcurrentCache := MakeConcurrentCache C.
  (* App (and some useless aspects of the projection) *)
  Import C.
  (* cache variables (and uselessly the cache invariant/guar) *)
  Import CacheProtocol.
  (* cache operations (and a preponderance of useless automation) *)
  Import ConcurrentCache.

  (* Exc is a (somewhat obscure) synonym for option defined in Specif *)
  Fixpoint compiler {T} (p: Prog.prog T) : prog App.Sigma (Exc T) :=
    match p with
    | Prog.Ret v => Ret (value v)
    | Prog.Read a => opt_v <- cache_read a;
                        match opt_v with
                        | Some v => Ret (value v)
                        (* in this branch T = valu so error_rx is safe;
                        might need to write this as a dependent match
                        to get it to typecheck *)
                        | None => Ret error
                        end
    | Prog.Write a v => _ <- cache_write a v;
                         Ret (value tt)
    | Prog.Sync => (* current concurrent disk model has no
                     asynchrony, but otherwise would need to issue
                     our own Sync here *)
      Ret (value tt)
    (* TODO: should really just remove Trim from Prog.prog *)
    | Prog.Trim a => Ret error
    (* TODO: should be a direct translation, but need hashing in
      concurrent execution semantics *)
    | Prog.Hash buf => Ret error
    | Prog.Bind p1 p2 => x <- compiler p1;
                          match x with
                          | Some x => compiler (p2 x)
                          | None => Ret error
                          end
    end.

  Record ConcurHoareSpec R :=
    ConcurSpec
      { concur_spec_pre: TID -> DISK ->
                         memory App.Sigma -> abstraction App.Sigma -> abstraction App.Sigma -> Prop;
        concur_spec_post: TID -> R ->
                          DISK -> memory App.Sigma -> abstraction App.Sigma -> abstraction App.Sigma ->
                          DISK -> memory App.Sigma -> abstraction App.Sigma -> abstraction App.Sigma -> Prop }.

  Definition concur_hoare_double R A (spec: A -> ConcurHoareSpec R)
             (p: prog App.Sigma R) :=
    forall T (rx: _ -> prog App.Sigma T) (tid:TID),
      valid App.delta tid
            (fun done d m s_i s =>
               exists a,
                 concur_spec_pre (spec a) tid d m s_i s /\
                 (forall ret_,
                     valid App.delta tid
                           (fun done_rx d' m' s_i' s' =>
                              concur_spec_post (spec a) tid ret_ d m s_i s d' m' s_i' s' /\
                              done_rx = done)
                           (rx ret_))
            ) (Bind p rx).

  (* [lift_disk] and [project_disk] convert between the view of the disk from
    sequential programs [Prog.prog] and concurrent programs [prog]: the
    differences are in the extra state (buffered writes vs race detecting
    readers) and the annoyance of having two different but provably equal valu
    definitions. *)

  Definition lift_disk (m: @mem addr _ prog_valuset) : DISK.
  Proof.
    intro a.
    destruct (m a); [ apply Some | apply None ].
    destruct p.
    exact (w, None).
  Defined.

  Definition project_disk (s: abstraction App.Sigma) : @mem addr _ prog_valuset.
  Proof.
    pose proof (get vdisk s) as vd.
    intro a.
    destruct (vd a); [ apply Some | apply None ].
    exact (w, nil).
  Defined.

  (* The idea of concurrent_spec is to compute a concurrent spec
     corresponding to sequential spec, capturing the same spec on top of
     the abstraction exported by the cache.

     Several things are important and currently broken with this definition:

     - The abstraction from the cache is some combination of vDisk0 and vdisk:
       vDisk0 is for between system calls and vdisk is for a given system call.
       [project_disk] currently just uses vdisk - vDisk0 is probably needed
       since aborts jump to it.
     - We currently never state we're not in a system call. Here we expect to be
       at the beginning but need a generalized correctness property for
       induction during a system call.
   *)
  Definition concurrent_spec R (spec: SeqHoareSpec R) : ConcurHoareSpec (Exc R) :=
    let 'SeqSpec pre post _ := spec in
    ConcurSpec
      (fun tid d m s_i s =>
         invariant delta d m s /\
         pre (project_disk s) /\
         guar delta tid s_i s)
      (fun tid r d m s_i s d' m' s_i' s' =>
         invariant delta d' m' s' /\
         match r with
         | Some r => post r (project_disk s')
         (* why is this rely? shouldn't it be guar? *)
         | None => rely delta tid s s'
         end /\
         guar delta tid s_i' s').

  Ltac inv_exec' H :=
    inversion H; subst; repeat sigT_eq;
    try solve [ inv_step ].

  Ltac inv_exec :=
    match goal with
    | [ H: exec _ _ _ _ _ |- _ ] =>
      inv_exec' H
    end.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ _ |- _ ] =>
      inversion H; subst
    | [ H: fail_step _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Ltac inv_outcome :=
    match goal with
    | [ H: @eq (outcome _) _ _ |- _ ] =>
      inversion H; subst
    end; unfold Exc in *; cleanup.

  Lemma exec_ret : forall Sigma (delta: Protocol Sigma)  tid T (v: T) st out,
      exec delta tid (Ret v) st out ->
      out = Finished st v.
  Proof.
    inversion 1; subst; repeat sigT_eq; auto.
    inversion H4.
    inversion H4.
  Qed.

  Ltac exec_ret :=
    match goal with
    | [ H: exec _ _ (Ret _) _ _ |- _ ] =>
      pose proof (exec_ret H); clear H; subst
    end; try inv_outcome.

  Hint Constructors Prog.exec.
  Hint Constructors Prog.step.

  Theorem cache_read_hoare_triple : forall tid a
                                      d m s_i s
                                      d' m' s_i' s' v0 v,
      exec App.delta tid (cache_read a) (d, m, s_i, s)
           (Finished (d', m', s_i', s') (Some v)) ->
      cacheI d m s ->
      get vdisk s a = Some v0 ->
      modified [( vCache; vDisk0 )] s s' /\
      cacheI d' m' s' /\
      v = v0 /\
      s_i' = s_i.
  Proof.
    intros.
    apply bind_right_id in H.
    eapply cache_read_ok in H.
    2: instantiate (1 := fun r d' m' s_i' s' =>
                           (forall v, r = Some v -> v = v0) /\
                           modified [( vCache; vDisk0 )] s s' /\
                           cacheI d' m' s' /\
                           s_i' = s_i).
    repeat deex; inv_outcome; auto.

    exists v0; intuition.
    apply valid_unfold; intuition idtac.
    subst.
    exec_ret.
    repeat match goal with
           | |- exists _, _ => eexists
           end; intuition eauto.
  Qed.

  Theorem cache_read_no_failure : forall tid a
                                    d m s_i s
                                    v0,
      exec App.delta tid (cache_read a) (d, m, s_i, s)
           (Failed _) ->
      cacheI d m s ->
      get vdisk s a = Some v0 ->
      False.
  Proof.
    intros.
    apply bind_right_id in H.
    eapply cache_read_ok in H.
    2: instantiate (1 := fun _ _ _ _ _ => True).
    repeat deex; inv_outcome.
    exists v0; intuition.
    apply valid_unfold; intuition idtac.
    exec_ret.
    repeat match goal with
           | |- exists _, _ => eexists
           end; intuition eauto.
  Qed.

  Theorem cache_write_hoare_triple : forall tid a
                                      d m s_i s
                                      d' m' s_i' s' v0 v r,
      exec App.delta tid (cache_write a v) (d, m, s_i, s)
           (Finished (d', m', s_i', s') r) ->
      cacheI d m s ->
      get vdisk s a = Some v0 ->
      modified [( vCache; vDisk0; vWriteBuffer; vdisk )] s s' /\
      cacheI d' m' s' /\
      get vdisk s' = upd (get vdisk s) a v /\
      s_i' = s_i /\
      r = tt.
  Proof.
    intros.
    destruct r.
    apply bind_right_id in H.
    eapply cache_write_ok in H.
    2: instantiate (1 := fun r d' m' s_i' s' =>
                           modified [( vCache; vDisk0; vWriteBuffer; vdisk )] s s' /\
                           cacheI d' m' s' /\
                           get vdisk s' = upd (get vdisk s) a v /\
                           s_i' = s_i).
    repeat deex; inv_outcome; auto.

    exists v0; intuition.
    apply valid_unfold; intuition idtac.
    subst.
    exec_ret.
    repeat match goal with
           | |- exists _, _ => eexists
           end; intuition eauto.
  Qed.

  Lemma cache_addr_valid : forall d m s a v,
      cacheI d m s ->
      get vdisk s a = Some v ->
      exists v', d a = Some v'.
  Proof.
    unfold cacheI; intuition idtac.
    specialize (H2 a).
    specialize (H4 a).
    apply equal_f_dep with a in H3.
    destruct matches in *; intuition idtac;
      repeat deex; eauto.
    unfold DiskReaders.hide_readers in H3.
    simpl_match; congruence.
    unfold DiskReaders.hide_readers in H3.
    simpl_match; congruence.
  Qed.

  Lemma possible_sync_refl : forall A AEQ (m: @mem A AEQ valuset),
      PredCrash.possible_sync m m.
  Proof.
    unfold PredCrash.possible_sync; intros.
    destruct (m a).
    - right.
      destruct p.
      exists w, l, l; intuition auto.
      apply List.incl_refl.
    - left; auto.
  Qed.

  Lemma cache_read_success_in_domain : forall tid a
                                         d m s_i s v
                                         d' m' s_i' s',
      exec App.delta tid (cache_read a) (d, m, s_i, s)
           (Finished (d', m', s_i', s') (Some v)) ->
      cacheI d m s ->
      get vdisk s a = Some v.
  Proof.
    intros.
    inv_exec.

    inv_exec' H6.
    inv_step; repeat sigT_eq.

    unfold cacheI in H0; destruct_ands.
    rewrite H1 in *.
    destruct matches in *;
      repeat exec_ret.
    match goal with
    | [ H: WriteBuffer.wb_rep _ _ _ |- _ ] =>
      specialize (H a)
    end.
    simpl_match; destruct_ands; repeat deex.

    inv_exec' H8.
    inv_step; repeat sigT_eq.
    inv_exec' H15.
    inv_step; repeat sigT_eq.
    rewrite H0 in *.
    match goal with
    | [ H: MemCache.cache_rep _ _ _ |- _ ] =>
      specialize (H a)
    end.
    match goal with
    | [ H: WriteBuffer.wb_rep _ _ _ |- _ ] =>
      specialize (H a)
    end.
    destruct matches in *;
      repeat exec_ret;
      repeat simpl_match;
      destruct_ands; repeat deex.
    - apply equal_f_dep with a in H3.
      unfold DiskReaders.hide_readers in H3; simpl_match.
      congruence.
    - apply equal_f_dep with a in H3.
      unfold DiskReaders.hide_readers in H3; simpl_match.
      congruence.
    - apply equal_f_dep with a in H3.
      unfold DiskReaders.hide_readers in H3; simpl_match.
      (* need hoare spec for finish_fill *)
      admit.
    - inv_exec' H17.
      exec_ret.
  Admitted.

  Lemma project_disk_synced : forall s,
      sync_mem (project_disk s) = project_disk s.
  Proof.
    intros.
    extensionality a.
    unfold sync_mem, project_disk.
    destruct matches.
  Qed.

  Lemma project_disk_upd : forall (s s': abstraction App.Sigma) a v,
      get vdisk s' = upd (get vdisk s) a v ->
      project_disk s' = upd (project_disk s) a (v, nil).
  Proof.
    unfold project_disk, upd; intros.
    rewrite H.
    extensionality a'.
    destruct matches.
  Qed.

  Theorem cache_simulation : forall T (p: Prog.prog T)
                               (tid:TID) d m s_i s out hm,
      exec App.delta tid (compiler p) (d, m, s_i, s) out ->
      cacheI d m s ->
      (forall d' m' s_i' s' (v:T),
          out = Finished (d', m', s_i', s') (value v) ->
          Prog.exec (project_disk s) hm p (Prog.Finished (project_disk s') hm v) /\
          (* this invariant allows us to continue running code in a bind (no pun
           intended) *)
          cacheI d' m' s').
  Proof.
    induction p; simpl; intros; subst.
    - exec_ret; eauto.
    - (* Read *)
      inv_exec.
      destruct v0; exec_ret; eauto.

      case_eq (get vdisk s a); intros.
      {
        eapply cache_read_hoare_triple in H6; eauto.
        intuition idtac; subst.

        eapply Prog.XStep.
        apply possible_sync_refl.
        assert (project_disk s = project_disk s') as Hproj.
        assert (get vdisk s = get vdisk s') by (apply H2; auto).
        unfold project_disk.
        rewrite H3; auto.
        rewrite <- Hproj.
        eapply Prog.StepRead.
        unfold project_disk.
        simpl_match; auto.
      }
      {
        apply cache_read_success_in_domain in H6; auto.
        congruence.
      }
    - (* Write *)
      inv_exec.
      exec_ret.
      case_eq (get vdisk s a); intros.
      {
        eapply cache_write_hoare_triple in H6; eauto.
        intuition idtac; subst.
        econstructor.
        apply possible_sync_refl.

        erewrite (project_disk_upd s s') by eauto.
        (* need to move the sync after the write to make this valid *)
        admit.
      }
      {
        (* this just isn't true; it's possible for cache_write to succeed with
        an out-of-bounds address, whereas Prog.Write would fail *)
        admit.
      }
    - (* Sync *)
      (* probably don't need the writeback (just do nothing) *)
      exec_ret.
      split; auto.
      econstructor.
      apply possible_sync_refl.
      rewrite <- project_disk_synced at 2.
      auto.
    - (* Trim *)
      (* this is fine *)
      exec_ret.
    - (* Hash *)
      (* should add hashing to concurrent execution so it can be directly
      translated *)
      exec_ret.
    - (* Bind *)
      inv_exec' H0.
      destruct st' as (((d'',m''),s_i''),s'').
      destruct v0.

      * eapply IHp with (hm := hm) in H7; eauto; destruct_ands.
        2: reflexivity.
        split; intros; subst.
        eapply Prog.XBindFinish; eauto.
        eapply H; eauto.

        eapply H; eauto.
      * split; intros; subst; exec_ret; inv_outcome.
Abort.

  Theorem cache_simulation_finish : forall T (p: Prog.prog T)
                                      (tid:TID) d m s_i s out hm,
      exec App.delta tid (compiler p) (d, m, s_i, s) out ->
      cacheI d m s ->
      (forall d' m' s_i' s' (v:T),
          out = Finished (d', m', s_i', s') (value v) ->
          (Prog.exec (project_disk s) hm p (Prog.Finished (project_disk s') hm v) /\
           cacheI d' m' s') \/
          (Prog.exec (project_disk s) hm p (Prog.Failed T))).
  Proof.
  Admitted.

  Theorem cache_simulation_failure : forall T (p: Prog.prog T)
                                       (tid:TID) d m s_i s hm,
      exec App.delta tid (compiler p) (d, m, s_i, s) (Failed (Exc T)) ->
      cacheI d m s ->
      Prog.exec (project_disk s) hm p (Prog.Failed T).
  Proof.
  Admitted.

  Theorem prog_exec_ret : forall T m hm (r:T) out,
      Prog.exec m hm (Prog.Ret r) out ->
      out = (Prog.Finished m hm r).
  Proof.
    intros.
    inversion H; repeat sigT_eq; auto.
    inversion H6.
    inversion H5.
    inversion H5.
  Qed.

  (* The master theorem: convert a sequential program into a concurrent
program via [compiler], convert its spec to a concurrent spec via
[concurrent_spec], and prove the resulting concurrent Hoare double.
   *)
  Theorem compiler_correct : forall T (p: Prog.prog T) A (spec: A -> SeqHoareSpec T),
      seq_hoare_double spec p ->
      concur_hoare_double (fun a => concurrent_spec (spec a)) (compiler p).
  Proof.
    unfold seq_hoare_double, concur_hoare_double, Hoare.corr2; intros.
    apply valid_unfold; intros.
    deex.
    case_eq (spec a); intros.
    rewrite H0 in *; simpl in *.
    destruct_ands.
    specialize (H T Prog.Ret).
    Print Hoare.donecond.
    specialize (H (fun hm r d => seq_spec_post r d) (fun _ _ => True)).
    specialize (H (project_disk s) empty_hashmap).

    inv_exec' H1; try solve [ inv_fail_step ].
    destruct v as [r |].
    { (* executed succesfully to (Some r) *)
      destruct st' as (((d',m'),s_i'),s').
      match goal with
        | [ H: exec _ _ (compiler p) _ _ |- _ ] =>
          eapply cache_simulation_finish with (hm:=empty_hashmap) in H;
            eauto; try reflexivity
      end.
      intuition.
      specialize (H (Prog.Finished (project_disk s') empty_hashmap r)).
      match type of H with
      | ?P -> ?Q -> _ =>
        assert Q
      end.
      apply ProgMonad.bind_right_id; auto.
      intuition.
      match type of H with
      | ?P -> ?Q -> ?R \/ ?R' =>
        assert (P -> R) as H'
      end.
      intros.
      intuition.
      repeat deex; congruence.
      match type of H' with
      | ?P -> _ => assert P
      end.
      {
        exists a; exists emp.
        repeat apply sep_star_lift_apply'; auto.
        apply pimpl_star_emp; auto.
        replace (spec a); simpl; auto.
        intros.
        destruct_lifts.
        replace (spec a) in H9; simpl in H9.

        apply prog_exec_ret in H10; subst.
        left.
        do 3 eexists; eauto.
      }
      intuition; repeat deex; try congruence.
      inversion H10; subst; clear H10.
      inversion H11; subst; clear H11.
      eapply H3 in H13; eauto.
      intuition auto.
      admit. (* lemmas need to prove cacheR s_i' s' for compiled programs *)


      specialize (H (Prog.Failed T)).
      match type of H with
      | ?P -> ?Q -> _ =>
        assert Q
      end.
      apply ProgMonad.bind_right_id; auto.
      match type of H with
      | ?P -> ?Q -> ?R \/ ?R' =>
        assert (P -> R) as H'
      end.
      intros.
      intuition.
      repeat deex; congruence.
      match type of H' with
      | ?P -> _ => assert P
      end.
      {
        exists a; exists emp.
        repeat apply sep_star_lift_apply'; auto.
        apply pimpl_star_emp; auto.
        replace (spec a); simpl; auto.
        intros.
        destruct_lifts.
        replace (spec a) in H8; simpl in H8.

        apply prog_exec_ret in H9; subst.
        left.
        do 3 eexists; eauto.
      }
      intuition; repeat deex; try congruence.
    }
    {
      (* execute to None case; need lemma to show compiled program "did nothing"
         (from cache_abort spec and invariant) *)
      admit.
    }

    (* compiled code failed *)
    apply cache_simulation_failure with (hm:=empty_hashmap) in H11; auto.
    (* TODO: this snippet of proof is repetitive *)
    specialize (H (Prog.Failed T)).
    match type of H with
    | ?P -> ?Q -> ?R \/ ?R' =>
      assert (P -> R) as H'
    end.
    apply ProgMonad.bind_right_id in H11; intuition auto.
    repeat deex; congruence.
    match type of H' with
    | ?P -> _ => assert P
    end.
    {
      exists a; exists emp.
      repeat apply sep_star_lift_apply'; auto.
      apply pimpl_star_emp; auto.
      replace (spec a); simpl; auto.
      intros.
      destruct_lifts.
      replace (spec a) in H6; simpl in H6.

      apply prog_exec_ret in H7; subst.
      left.
      do 3 eexists; eauto.
    }
    intuition; repeat deex; try congruence.
  Abort.

End MakeBridge.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)