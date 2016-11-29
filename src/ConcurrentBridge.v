Require Import CoopConcur.
Require Import ConcurrentCache.
Require Import MemCache WriteBufferSet.
Require Import Specifications.
Require Import CoopConcurMonad.
Import HlistNotations.

(* [lift_disk] and [lower_disk] convert between the view of the disk from
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

Definition lower_disk (m: DiskReaders.Disk): @mem addr _ prog_valuset.
  intro a.
  destruct (m a); [ apply Some | apply None ].
  exact (w, nil).
Defined.

Module MakeBridge (C:CacheSubProtocol).

  Module ConcurrentCache := MakeConcurrentCache C.
  (* App (and some useless aspects of the projection) *)
  Import C.
  (* cache variables (and uselessly the cache invariant/guar) *)
  Import CacheProtocol.
  (* cache operations (and a preponderance of useless automation) *)
  Import ConcurrentCache.

  (* Exc is a (somewhat obscure) synonym for option defined in Specif *)
  Fixpoint compile {T} (p: Prog.prog T) : prog App.Sigma (Exc T) :=
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
    | Prog.Hash buf => h <- Hash buf;
                        Ret (Some h)
    | Prog.Bind p1 p2 => x <- compile p1;
                          match x with
                          | Some x => compile (p2 x)
                          | None => Ret error
                          end
    end.

  Record ConcurHoareSpec R :=
    ConcurSpec
      { concur_spec_pre: TID -> DISK -> hashmap ->
                         memory App.Sigma -> abstraction App.Sigma -> abstraction App.Sigma -> Prop;
        concur_spec_post: TID -> R ->
                          DISK -> hashmap ->
                          memory App.Sigma -> abstraction App.Sigma -> abstraction App.Sigma ->
                          DISK -> hashmap ->
                          memory App.Sigma -> abstraction App.Sigma -> abstraction App.Sigma -> Prop }.

  Definition concur_hoare_double R A (spec: A -> ConcurHoareSpec R)
             (p: prog App.Sigma R) :=
    forall T (rx: _ -> prog App.Sigma T) (tid:TID),
      valid App.delta tid
            (fun done d hm m s_i s =>
               exists a,
                 concur_spec_pre (spec a) tid d hm m s_i s /\
                 (forall ret_,
                     valid App.delta tid
                           (fun done_rx d' hm' m' s_i' s' =>
                              concur_spec_post (spec a) tid ret_ d hm m s_i s
                                               d' hm' m' s_i' s' /\
                              done_rx = done)
                           (rx ret_))
            ) (Bind p rx).

  Definition project_disk (s: abstraction App.Sigma) : @mem addr _ prog_valuset :=
    lower_disk (get vdisk s).

  Definition cache_vars := [( vCache; vWriteBuffer; vDisk0; vdisk0; vdisk )].

  (* The idea of concurrent_spec is to compute a concurrent spec
     corresponding to sequential spec, capturing the same spec on top of
     the abstraction exported by the cache. *)
  Definition concurrent_spec R (spec: hashmap -> SeqHoareSpec R) : ConcurHoareSpec (Exc R) :=
    ConcurSpec
      (fun tid d hm m s_i s =>
         invariant delta d hm m s /\
         seq_spec_pre (spec hm) (project_disk s) /\
         guar delta tid s_i s)
      (fun tid r d hm m s_i s d' hm' m' s_i' s' =>
         invariant delta d' hm' m' s' /\
         match r with
         | Some r => seq_spec_post (spec hm) r hm' (project_disk s')
         | None => guar delta tid s s'
         end /\
         hashmap_le hm hm' /\
         modified cache_vars s s' /\
         guar delta tid s_i' s').

  Ltac inv_exec' H :=
    inversion H; subst; repeat sigT_eq;
    try solve [ inv_step ];
    try solve [ inv_fail_step ].

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

  Ltac _pattern_f x e :=
    match eval pattern x in e with
    | ?f _ => f
    end.

  Ltac _donecond :=
    match goal with
    | [ H: exec App.delta _ _ _ (Finished (?d', ?hm', ?m', ?s_i', ?s') ?r) |- ?g ] =>
      let f := _pattern_f s' g in
      let f := _pattern_f s_i' f in
      let f := _pattern_f m' f in
      let f := _pattern_f hm' f in
      let f := _pattern_f d' f in
      let f := _pattern_f r f in
      f
    end.

  Theorem cache_read_hoare_triple : forall tid a
                                      d hm m s_i s
                                      d' hm' m' s_i' s' v0 r,
      exec App.delta tid (cache_read a) (d, hm, m, s_i, s)
           (Finished (d', hm', m', s_i', s') r) ->
      cacheI d hm m s ->
      get vdisk s a = Some v0 ->
      modified [( vCache; vDisk0 )] s s' /\
      cacheI d' hm' m' s' /\
      (forall v, r = Some v -> v = v0) /\
      s_i' = s_i /\
      hm' = hm /\
      guar delta tid s s'.
  Proof.
    intros.
    apply bind_right_id in H.
    let done := _donecond in
    apply (cache_read_ok (done:=done)) in H.
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
                                    d hm m s_i s
                                    v0,
      exec App.delta tid (cache_read a) (d, hm, m, s_i, s)
           (Failed _) ->
      cacheI d hm m s ->
      get vdisk s a = Some v0 ->
      False.
  Proof.
    intros.
    apply bind_right_id in H.
    eapply cache_read_ok in H.
    2: instantiate (1 := fun _ _ _ _ _ _ => True).
    repeat deex; inv_outcome.
    exists v0; intuition.
    apply valid_unfold; intuition idtac.
    exec_ret.
    repeat match goal with
           | |- exists _, _ => eexists
           end; intuition eauto.
  Qed.

  Theorem cache_write_hoare_triple : forall tid a
                                      d hm m s_i s
                                      d' hm' m' s_i' s' v0 v r,
      exec App.delta tid (cache_write a v) (d, hm, m, s_i, s)
           (Finished (d', hm', m', s_i', s') r) ->
      cacheI d hm m s ->
      get vdisk s a = Some v0 ->
      modified [( vCache; vDisk0; vWriteBuffer; vdisk )] s s' /\
      cacheI d' hm' m' s' /\
      get vdisk s' = upd (get vdisk s) a v /\
      guar delta tid s s' /\
      s_i' = s_i /\
      hm' = hm /\
      r = tt.
  Proof.
    intros.
    destruct r.
    apply bind_right_id in H.
    let done := _donecond in
    apply (cache_write_ok (done:=done)) in H.
    repeat deex; inv_outcome; auto.

    exists v0; intuition.
    apply valid_unfold; intuition idtac.
    subst.
    exec_ret.
    repeat match goal with
           | |- exists _, _ => eexists
           end; intuition eauto.
  Qed.

  Theorem finish_fill_hoare_triple : forall tid a
                                       d hm m s_i s
                                       d' hm' m' s_i' s' v0 r,
      exec App.delta tid (finish_fill a) (d, hm, m, s_i, s)
           (Finished (d', hm', m', s_i', s') r) ->
      cacheI d hm m s ->
      get vdisk s a = Some v0 ->
      cache_get (get vCache s) a = Invalid ->
      wb_get (get vWriteBuffer s) a = WbMissing ->
      cacheI d' hm' m' s' /\
      modified [( vCache; vDisk0 )] s s' /\
      cache_get (get vCache s') a = Clean v0 /\
      guar delta tid s s' /\
      r = v0 /\
      hm' = hm /\
      s_i' = s_i.
  Proof.
    intros.
    apply bind_right_id in H.
    let done := _donecond in
    apply (finish_fill_ok (done := done)) in H.
    repeat deex; inv_outcome; auto.

    exists v0; intuition eauto.
    apply valid_unfold; intuition idtac.
    subst.
    exec_ret.
    repeat match goal with
           | |- exists _, _ => eexists
           end; intuition eauto.
  Qed.

  Lemma cache_addr_valid : forall d hm m s a v,
      cacheI d hm m s ->
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

  Hint Resolve List.incl_refl List.incl_tl List.incl_cons.

  Lemma possible_sync_refl : forall A AEQ (m: @mem A AEQ valuset),
      PredCrash.possible_sync m m.
  Proof.
    unfold PredCrash.possible_sync; intros.
    destruct (m a).
    - right.
      destruct p.
      exists w, l, l; intuition auto.
    - left; auto.
  Qed.

  Lemma cache_read_success_in_domain : forall tid a
                                         d hm m s_i s v
                                         d' hm' m' s_i' s',
      exec App.delta tid (cache_read a) (d, hm, m, s_i, s)
           (Finished (d', hm', m', s_i', s') (Some v)) ->
      cacheI d hm m s ->
      get vdisk s a = Some v.
  Proof.
    intros.
    inv_exec.

    inv_exec' H6.
    inv_step; repeat sigT_eq.

    pose proof H0 as HcacheI.
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
      inv_exec' H17.
      exec_ret.
      assert (get vdisk s a = Some v0) by congruence.
      eapply finish_fill_hoare_triple in H22; eauto.
      intuition subst; auto.
    - inv_exec' H17.
      exec_ret.
  Qed.

  Lemma project_disk_synced : forall s,
      sync_mem (project_disk s) = project_disk s.
  Proof.
    intros.
    extensionality a.
    unfold sync_mem, project_disk, lower_disk.
    destruct matches.
  Qed.

  Lemma project_disk_upd : forall (s s': abstraction App.Sigma) a v,
      get vdisk s' = upd (get vdisk s) a v ->
      project_disk s' = upd (project_disk s) a (v, nil).
  Proof.
    unfold project_disk, lower_disk, upd; intros.
    rewrite H.
    extensionality a'.
    destruct matches.
  Qed.

  Hint Extern 1 (guar _ _ ?a ?a) => apply guar_preorder.

  Theorem project_disk_vdisk_none : forall (s: abstraction App.Sigma) a,
      get vdisk s a = None ->
      project_disk s a = None.
  Proof.
    unfold project_disk, lower_disk; intros; rewrite H; auto.
  Qed.

  Hint Resolve project_disk_vdisk_none.

  Lemma value_is : forall T (v v':T),
      (forall t, Some v = Some t -> t = v') ->
      v = v'.
  Proof.
    eauto.
  Qed.

  Lemma hashmap_le_upd : forall hm h sz (buf: word sz),
      hash_safe hm h buf ->
      hashmap_le hm (upd_hashmap' hm h buf).
  Proof.
    unfold hashmap_le; intros.
    eexists.
    eapply HS_cons; eauto.
    eapply HS_nil.
  Qed.

  Hint Resolve hashmap_le_upd.

  Hint Immediate modified_refl.
  Hint Resolve modified_reduce_strict.

  Ltac prove_hincl :=
    intros;
    repeat match goal with
    | [ H: HIn _ _ |- _ ] =>
      inversion H; repeat sigT_eq; clear H
    | [ |- HIn _ _ ] =>
      solve [ repeat econstructor ]
    end.

  Lemma cache_disk0_cache_vars : forall t (v: var _ t),
      HIn v [(vCache; vDisk0)] ->
      HIn v cache_vars.
  Proof.
    prove_hincl.
  Qed.

  Hint Resolve cache_disk0_cache_vars.

  Lemma cache_disk0_wb_disk_cache_vars :
    forall (t : Type) (v0 : var (abstraction_types App.Sigma) t),
      HIn v0 [(vCache; vDisk0; vWriteBuffer; vdisk)] ->
      HIn v0 cache_vars.
  Proof.
    prove_hincl.
  Qed.

  Hint Resolve cache_disk0_wb_disk_cache_vars.

  Theorem cache_simulation_finish : forall T (p: Prog.prog T)
                                      (tid:TID) d hm m s_i s out,
      exec App.delta tid (compile p) (d, hm, m, s_i, s) out ->
      cacheI d hm m s ->
      (forall d' hm' m' s_i' s' (v:T),
          out = Finished (d', hm', m', s_i', s') (value v) ->
          (Prog.exec (project_disk s) hm p (Prog.Finished (project_disk s') hm' v) /\
           cacheI d' hm' m' s' /\
           guar delta tid s s' /\
           hashmap_le hm hm' /\
           modified cache_vars s s' /\
           s_i' = s_i) \/
          (Prog.exec (project_disk s) hm p (Prog.Failed T))).
  Proof.
    induction p; simpl; intros; subst.
    - exec_ret.
      left.
      intuition eauto.
      apply cacheR_preorder.
    - inv_exec.
      destruct v0; exec_ret; eauto.

      case_eq (get vdisk s a); intros.
      {
        left.
        eapply cache_read_hoare_triple in H6; eauto.
        intuition auto; subst.
        apply value_is in H3; subst.

        eapply Prog.XStep; [ | apply possible_sync_refl ].
        assert (project_disk s = project_disk s') as Hproj.
        assert (get vdisk s = get vdisk s') by (apply H2; auto).
        unfold project_disk.
        replace (get vdisk s); auto.
        rewrite <- Hproj.
        eapply Prog.StepRead.
        unfold project_disk, lower_disk.
        simpl_match; auto.
        auto.
        eauto.
      }
      {
        right.
        constructor.
        constructor.
        auto.
      }
    - inv_exec.
      destruct v0; exec_ret; eauto.

      case_eq (get vdisk s a); intros.
      {
        left.
        eapply cache_write_hoare_triple in H6; eauto.
        intuition auto; subst.

        eapply Prog.XStep with (upd (project_disk s) a (v, w::nil)).
        constructor.
        unfold project_disk, lower_disk; simpl_match; auto.
        assert (project_disk s' = upd (project_disk s) a (v, nil)) as Hproj.
        unfold project_disk, lower_disk.
        rewrite H3.
        extensionality a'.
        destruct (nat_dec a a'); subst; autorewrite with upd; auto.
        rewrite Hproj.
        eapply PredCrash.possible_sync_respects_upd; eauto.
        apply possible_sync_refl.
        auto.
        eauto.
      }
      {
        right.
        constructor.
        constructor.
        auto.
      }
    - (* Sync *)
      (* probably don't need the writeback (just do nothing) *)
      exec_ret.
      left.
      intuition auto.
      eapply Prog.XStep; [ | apply possible_sync_refl ].
      rewrite <- project_disk_synced at 2.
      auto.
      apply cacheR_preorder.
    - (* Trim *)
      (* this is fine *)
      exec_ret.
    - (* Hash *)
      (* should add hashing to concurrent execution so it can be directly
      translated *)
      inv_exec.
      exec_ret.
      inv_exec.
      inv_step; repeat sigT_eq.
      left.
      intuition eauto.
      eapply Prog.XStep; [ | apply possible_sync_refl ].
      eapply Prog.StepHash; eauto.
      apply cacheR_preorder.
    - (* Bind *)
      inv_exec' H0.
      destruct st' as ((((d'',hm''),m''),s_i''),s'').
      destruct v0.

      * eapply IHp in H7; eauto.
        2: reflexivity.
        intuition auto.
        edestruct H; eauto.
        destruct_ands.
        subst.
        left.
        intuition auto.
        eapply Prog.XBindFinish; eauto.
        eapply cacheR_preorder; eauto.
        eapply hashmap_le_preorder; eauto.
        eapply modified_trans; eauto.
      * left.
        split; intros; subst; exec_ret; inv_outcome.
  Qed.

  Theorem prog_exec_ret : forall T m hm (r:T) out,
      Prog.exec m hm (Prog.Ret r) out ->
      out = (Prog.Finished m hm r).
  Proof.
    intros.
    inv_exec' H; auto.
    inversion H5.
    inversion H5.
    inversion H5.
  Qed.

  Hint Extern 1 (cacheR _ ?a ?a) => apply cacheR_preorder.

  Theorem cache_simulation_finish_error : forall T (p: Prog.prog T)
                                            (tid:TID) d hm m s_i s
                                            d' hm' m' s_i' s',
      exec App.delta tid (compile p) (d, hm, m, s_i, s) (Finished (d', hm', m', s_i', s') error) ->
      cacheI d hm m s ->
      (cacheI d' hm' m' s' /\
       guar delta tid s s' /\
       hashmap_le hm hm' /\
       modified cache_vars s s' /\
       s_i' = s_i) \/
      (Prog.exec (project_disk s) hm p (Prog.Failed T)).
  Proof.
    induction p; simpl; intros.
    - exec_ret.
    - inv_exec.
      case_eq (get vdisk s a); intros.
      destruct v; exec_ret; try congruence.
      eapply cache_read_hoare_triple in H6; eauto.
      left.
      intuition eauto; subst.
      auto.

      right.
      constructor.
      constructor.
      auto.
    - inv_exec.
      exec_ret.
    - exec_ret.
    - exec_ret.
      left.
      intuition auto.
    - inv_exec.
      exec_ret.
    - inv_exec.
      destruct v; try exec_ret.
      destruct st' as ((((d'', hm''), m''), s_i''), s'').
      pose proof H7.
      eapply cache_simulation_finish in H7; eauto; try reflexivity.
      destruct H7; [ destruct_ands | right ]; subst.
      pose proof H9.
      eapply H in H9; eauto.
      destruct H9; [ destruct_ands | right ].
      subst.
      left.
      intuition eauto.
      eapply cacheR_preorder; eauto.
      eapply hashmap_le_preorder; eauto.
      eapply modified_trans; eauto.
      eapply Prog.XBindFinish; eauto.
      eapply Prog.XBindFail; eauto.

      eapply IHp in H7; eauto.
      destruct H7; eauto.
  Qed.

  Lemma modify_wb_no_failure : forall tid up st,
        exec App.delta tid (modify_wb up) st (Failed _) ->
        False.
  Proof.
    intros.
    repeat inv_exec.
  Qed.

  Lemma modify_cache_no_failure : forall tid up st,
        exec App.delta tid (modify_cache up) st (Failed _) ->
        False.
  Proof.
    intros.
    repeat inv_exec.
  Qed.

  Lemma var_update_no_failure : forall tid T v (up: T -> T)
                                  st,
      exec App.delta tid (CoopConcurAuto.var_update v up) st (Failed _) ->
      False.
  Proof.
    intros.
    repeat inv_exec.
  Qed.

  Lemma Ret_no_failure : forall tid T (v: T) st,
      exec App.delta tid (Ret v) st (Failed _) ->
      False.
  Proof.
    intros.
    exec_ret.
  Qed.

  Hint Resolve modify_wb_no_failure
       modify_cache_no_failure
       var_update_no_failure
       Ret_no_failure.

  Ltac impossible_failure := exfalso; solve [ repeat (inv_exec; eauto) ].

  Theorem finish_fill_failure : forall tid a
                                  d hm m s_i s,
      exec App.delta tid (finish_fill a) (d, hm, m, s_i, s) (Failed _) ->
      cache_get (get vCache s) a = Invalid ->
      cacheI d hm m s ->
      get vdisk s a = None.
  Proof.
    intros.
    inv_exec.
    - (* finish read succeeded; everything else always succeeds *)
      impossible_failure.
    - (* FinishRead_upd failed *)
      inv_exec.
      impossible_failure.
      (* FinishRead itself failed *)
      inv_exec.
      inv_fail_step.
      * (* failure do to out-of-bounds address *)
        unfold cacheI in *; destruct_ands.
        specialize (H3 a).
        destruct matches in *; intuition idtac; repeat deex; try congruence.
      * unfold cacheI in *; destruct_ands.
        specialize (H3 a).
        destruct matches in *; intuition idtac; repeat deex; try congruence.
  Qed.

  Theorem Get_hoare_triple : forall tid T var (v: T)
                               d hm m s_i s
                               d' hm' m' s_i' s',
      exec App.delta tid (Get var) (d, hm, m, s_i, s)
           (Finished (d', hm', m', s_i', s') v) ->
      d' = d /\ m' = m /\ s_i' = s_i /\ s' = s /\ hm' = hm /\
      v = get var m.
  Proof.
    intros.
    inv_exec.
    inv_step; repeat sigT_eq; subst.
    intuition auto.
  Qed.

  Theorem cache_write_failure : forall tid a v
                                  d hm m s_i s,
      exec App.delta tid (cache_write a v) (d, hm, m, s_i, s)
           (Failed _) ->
      cacheI d hm m s ->
      get vdisk s a = None.
  Proof.
    intros.
    inv_exec.
    destruct matches in *.
    impossible_failure.
    impossible_failure.

    inv_exec.
    impossible_failure.

    match goal with
    | [ H: exec _ _ (Get mCache) _ (Finished ?st' _) |- _ ] =>
      destruct st' as ((((d', hm'), m'), s_i'), s');
        apply Get_hoare_triple in H;
        destruct_ands; subst
    end.

    eapply finish_fill_failure in H9; eauto.
    unfold cacheI in *; destruct_ands; congruence.

    impossible_failure.
    impossible_failure.
  Qed.

  Theorem cache_simulation_failure : forall T (p: Prog.prog T)
                                       (tid:TID) d hm m s_i s,
      exec App.delta tid (compile p) (d, hm, m, s_i, s) (Failed (Exc T)) ->
      cacheI d hm m s ->
      Prog.exec (project_disk s) hm p (Prog.Failed T).
  Proof.
    induction p; simpl; intros; subst;
      try exec_ret.
    - inv_exec.
      destruct v; exec_ret.
      case_eq (get vdisk s a); intros.
      exfalso.
      eapply cache_read_no_failure; eauto.
      constructor.
      constructor.
      auto.
    - inv_exec.
      exec_ret.
      eapply cache_write_failure in H6; eauto.
      constructor.
      constructor.
      auto.
    - inv_exec.
      exec_ret.
      inv_exec.
    - inv_exec.
      destruct v; try solve [ exec_ret ].
      destruct st' as ((((d', hm'), m'), s_i'), s').
      replace (Some t) with (value t) in H7 by reflexivity.
      eapply cache_simulation_finish in H7; intuition eauto.

      eauto.
  Qed.

  (* The master theorem: convert a sequential program into a concurrent
program via [compile], convert its spec to a concurrent spec via
[concurrent_spec], and prove the resulting concurrent Hoare double.
   *)
  Theorem compiler_correct : forall T (p: Prog.prog T) A (spec: A -> hashmap -> SeqHoareSpec T),
      seq_hoare_double spec p ->
      concur_hoare_double (fun a => concurrent_spec (spec a)) (compile p).
  Proof.
    unfold seq_hoare_double, concur_hoare_double, Hoare.corr2; intros.
    apply valid_unfold; intros.
    deex.
    specialize (H T Prog.Ret).
    specialize (H (fun hm' r d => seq_spec_post (spec a hm) r hm' d) (fun _ _ => True)).
    specialize (H (project_disk s) hm).

    inv_exec' H1; try solve [ inv_fail_step ].
    destruct v as [r |].
    { (* executed succesfully to (Some r) *)
      destruct st' as ((((d',hm'),m'),s_i'),s').
      match goal with
        | [ H: exec _ _ (compile p) _ _ |- _ ] =>
          eapply cache_simulation_finish in H;
            eauto; try reflexivity
      end.
      intuition.
      specialize (H (Prog.Finished (project_disk s') hm' r)).
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
        simpl in *; intuition eauto.

        intros.
        destruct_lifts.
        match goal with
        | [ H: Prog.exec _ _ (Prog.Ret _) _ |- _ ] =>
          apply prog_exec_ret in H; subst
        end.
        left.
        do 3 eexists; eauto.
      }
      intuition; repeat deex; try congruence.
      repeat match goal with
               [ H: @eq (Prog.outcome _) _ _ |- _ ] =>
               inversion H; clear H
             end; subst.
      simpl in *; intuition auto.
      match goal with
      | [ H: forall _, valid _ _ _ (rx _),
            H': exec _ _ (rx _) _ _ |- _ ] =>
        eapply H in H'; eauto
      end.
      intuition auto.
      eapply cacheR_preorder; eauto.

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
        simpl in *; intuition eauto.

        intros.
        destruct_lifts.
        simpl in *.

        match goal with
        | [ H: Prog.exec _ _ (Prog.Ret _) _ |- _ ] =>
          apply prog_exec_ret in H; subst
        end.
        left.
        do 3 eexists; eauto.
      }
      intuition; repeat deex; try congruence.
      simpl in *; intuition eauto.
    }
    {
      (* execute to None case; need to apply cache_simulation_finish_error *)
      destruct st' as ((((d', hm'), m'), s_i'), s').
      simpl in *; intuition eauto.
      match goal with
      | [ H: exec _ _ (compile _) _ _ |- _ ] =>
        eapply cache_simulation_finish_error in H; [ destruct H | eauto ]
      end.
      - destruct_ands.
        match goal with
        | [ H: forall _, valid _ _ _ (rx _),
              H': exec _ _ (rx _) _ _ |- _ ] =>
          eapply H in H'; eauto
        end.
        subst.
        intuition eauto.
        eapply cacheR_preorder; eauto.
      - (* failure if sequential isn't possible *)
        exfalso.
        specialize (H (Prog.Failed T)).
        match type of H with
        | ?P -> ?Q -> ?R \/ ?R' =>
          assert (P -> R) as H'
        end.
        intuition eauto.
        apply ProgMonad.bind_right_id in H4; intuition auto.
        repeat deex; congruence.
        match type of H' with
        | ?P -> _ => assert P
        end.
        {
          exists a; exists emp.
          repeat apply sep_star_lift_apply'; auto.
          apply pimpl_star_emp; auto.
          simpl in *; intuition eauto.

          apply prog_exec_ret in H7; subst.
          destruct_lifts.
          left.
          do 3 eexists; eauto.
        }
        intuition; repeat deex; try congruence.
    }

    (* compiled code failed *)
    simpl in *; intuition eauto.
    match goal with
      | [ H: exec _ _ _ _ (Failed _) |- _ ] =>
        apply cache_simulation_failure in H; auto
    end.
    (* TODO: this snippet of proof is repetitive *)
    specialize (H (Prog.Failed T)).
    match type of H with
    | ?P -> ?Q -> ?R \/ ?R' =>
      assert (P -> R) as H'
    end.
    apply ProgMonad.bind_right_id in H8; intuition auto.
    repeat deex; congruence.
    match type of H' with
    | ?P -> _ => assert P
    end.
    {
      exists a; exists emp.
      repeat apply sep_star_lift_apply'; auto.
      apply pimpl_star_emp; auto.

      intros.
      destruct_lifts.

      apply prog_exec_ret in H6; subst.
      left.
      do 3 eexists; eauto.
    }
    intuition; repeat deex; try congruence.
  Qed.

End MakeBridge.

(* Local Variables: *)
(* company-coq-local-symbols: (("delta" . ?δ) ("Sigma" . ?Σ)) *)
(* End: *)