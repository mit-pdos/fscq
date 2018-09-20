Require Import Arith.
Require Import Mem Pred.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import Errno.

Require Import Instr.

Transparent corr2 corr2_weak.

Theorem weak_conversion':
    forall T A1 (p1: prog T) pr
      pre post crash,
      
      {< (e1: A1),
         PERM: pr
         PRE: bm, hm, pre e1 bm hm
         POST: bm', hm', (fun F r => F * post F r e1 bm' hm')
         CRASH: bm'', hm'', crash e1 bm'' hm'' >} p1 ->
                           
      {<W (e1: A1),
          PERM: pr
          PRE: bm, hm, pre e1 bm hm 
          POST: bm', hm', (fun F r => F * post F r e1 bm' hm')
          CRASH: bm'', hm'', crash e1 bm'' hm'' W>} p1.
  Proof.
    intros.
    monad_simpl_weak.
    unfold corr2_weak; intros.
    inv_exec_perm.
    - destruct_lift H0.
      edestruct H.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        {
          unfold corr2; intros.
          denote Ret as Hret.
          inv_exec'' Hret.
          instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                    [[ hm = hm0 ]] *
                                    [[ bm c= bm0 ]])%pred d1) in H3.
          denote sep_star as Hstar;
            destruct_lift Hstar.
          eassign crashc.
          split; auto.
           do 3 eexists; left; eexists; repeat (split; eauto).         
          simpl; pred_apply; cancel.
        }
        eauto.
      }
      
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      edestruct H6.
      2: repeat econstructor; eauto.
      pred_apply; cancel; eauto.
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      split.
      do 3 eexists; left; repeat eexists; eauto.
      repeat (apply trace_secure_app; eauto).
      apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H0.
        edestruct H with (rx:=@Ret T).
        2: eapply CrashBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H2.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply only_public_operations_to_trace_secure; auto.
        
      + destruct_lift H0.
        edestruct H.
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H3.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H6; eauto.
        pred_apply; cancel.
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply trace_secure_app; auto.
        apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H0.
        edestruct H with (rx:=@Ret T).
        2: eapply FailBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H2.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
      + destruct_lift H0.
        edestruct H with (rx:=@Ret T).
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H3.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H6; eauto.
        pred_apply; cancel.
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        Unshelve.
        all: try exact handle.
        all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.


Theorem weak_conversion_chdom:
 forall T T' A1 (p1: prog T) (p2: T -> prog T') pr
      pre post post2 crash1 crash2,
      
      {< (e1: A1),
         PERM: pr
         PRE: bm, hm, pre e1 bm hm
         POST: bm', hm', (fun F r => F * post F r e1 bm' hm')
         CRASH: bm'', hm'', crash1 e1 bm'' hm'' >} p1 ->
      
      (forall F r e1,
          {~<W 
             PERM: pr
              PRE: bm, hm, post F r e1 bm hm 
              POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
              CRASH: bm'', hm'', crash2 e1 bm'' hm'' W>~} (p2 r)) ->
      
      (forall e1 bm'' hm'' , crash1 e1 bm'' hm'' =p=> crash2 e1 bm'' hm'') ->
                           
      {~<W (e1: A1),
          PERM: pr
          PRE: bm, hm, pre e1 bm hm 
          POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
          CRASH: bm'', hm'', crash2 e1 bm'' hm'' W>~} (Bind p1 p2).
  Proof.
    intros.
    monad_simpl_weak.
    unfold corr2_weak; intros.
    inv_exec_perm.
    - destruct_lift H2.
      edestruct H.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        {
          unfold corr2; intros.
          denote Ret as Hret.
          inv_exec'' Hret.
          instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                    [[ hm = hm0 ]] *
                                    [[ bm c= bm0 ]])%pred d1) in H5.
          denote sep_star as Hstar;
            destruct_lift Hstar.
          eassign crashc.
          split; auto.
          do 3 eexists; left; eexists; repeat (split; eauto).         
          simpl; pred_apply; cancel.
        }
        rewrite <- H7; cancel; eauto.
      }
      
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      inv_exec_perm.
      edestruct H0.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        eauto.
         {
          unfold corr2_weak; intros.
          denote Ret as Hret.
          inv_exec'' Hret.
          denote sep_star as Hstar;
            destruct_lift Hstar.
          eassign crashc.
          split; auto.
          do 3 eexists; left; eexists; repeat (split; eauto).  
          eassign (fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                    [[ x6 c= bm0 ]])%pred d1).
          simpl; pred_apply; cancel.
        }
         rewrite <- H7; cancel; eauto.
      }

      simpl in *; cleanup; split_ors; cleanup; try congruence.
      edestruct H8; eauto.
      destruct_lift H11.
      pred_apply; cancel; eauto.
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      split.
      do 3 eexists; left; repeat eexists; eauto.
      repeat (apply trace_secure_app; eauto).
      apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply CrashBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:=fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                       [[ hm = hm0 ]] *
                                       [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply only_public_operations_to_trace_secure; auto.
        
      + destruct_lift H2.
        edestruct H.
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                       [[ hm = hm0 ]] *
                                       [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0; eauto.
        {
           pred_apply; safecancel.
           eassign dummy; cancel.
           eauto.
           auto.
           destruct_lift H11.
           eassign crashc.
           unfold corr2_weak; intros.
           destruct_lift H11.
           edestruct H8; eauto.
           pred_apply; cancel; eauto.
           rewrite <- H7; cancel; eauto.
         }
         simpl in *; cleanup; split_ors; cleanup; try congruence.
         split.
         do 3 eexists; right; repeat eexists; eauto.
         apply trace_secure_app; auto.
         apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply FailBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                       [[ hm = hm0 ]] *
                                       [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; auto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                       [[ hm = hm0 ]] *
                                       [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          destruct_lift H11.
          unfold corr2_weak; intros.
          destruct_lift H11.
          edestruct H8; eauto.
          pred_apply; cancel; eauto.
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        
        Unshelve.
        all: try exact handle.
        all: unfold Mem.EqDec; apply Blockmem.handle_eq_dec.
  Qed.

  


   Theorem weak_conversion:
    forall T T' A1 (p1: prog T) (p2: T -> prog T') pr
      pre post post2 crash1 crash2,
      
      {< (e1: A1),
         PERM: pr
         PRE: bm, hm, pre e1 bm hm
         POST: bm', hm', (fun F r => F * post F r e1 bm' hm')
         CRASH: bm'', hm'', crash1 e1 bm'' hm'' >} p1 ->
      
      (forall F r e1,
          {<W PERM: pr
              PRE: bm, hm, post F r e1 bm hm 
              POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
              CRASH: bm'', hm'', crash2 e1 bm'' hm'' W>} (p2 r)) ->
      
      (forall e1 bm'' hm'' , crash1 e1 bm'' hm'' =p=> crash2 e1 bm'' hm'') ->
                           
      {<W (e1: A1),
          PERM: pr
          PRE: bm, hm, pre e1 bm hm 
          POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
          CRASH: bm'', hm'', crash2 e1 bm'' hm'' W>} (Bind p1 p2).
  Proof.
    intros.
    monad_simpl_weak.
    unfold corr2_weak; intros.
    inv_exec_perm.
    - destruct_lift H2.
      edestruct H.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        {
          unfold corr2; intros.
          denote Ret as Hret.
          inv_exec'' Hret.
          instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                    [[ hm = hm0 ]] *
                                    [[ bm c= bm0 ]])%pred d1) in H5.
          denote sep_star as Hstar;
            destruct_lift Hstar.
          eassign crashc.
          split; auto.
          do 3 eexists; left; eexists; repeat (split; eauto).         
          simpl; pred_apply; cancel.
        }
        rewrite <- H7; cancel; eauto.
      }
      
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      inv_exec_perm.
      edestruct H0.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        eauto.
        {
          unfold corr2_weak; intros.
          denote Ret as Hret.
          inv_exec'' Hret.
          instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                    [[ x7 = hm0 ]] *
                                    [[ x6 c= bm0 ]])%pred d1) in H12.
          denote sep_star as Hstar;
            destruct_lift Hstar.
          eassign crashc.
          split; auto.
          do 3 eexists; left; eexists; repeat (split; eauto).         
          simpl; pred_apply; cancel.
        }
         rewrite <- H7; cancel; eauto.
      }

      simpl in *; cleanup; split_ors; cleanup; try congruence.
      edestruct H8; eauto.
      destruct_lift H11.
      pred_apply; cancel; eauto.
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      split.
      do 3 eexists; left; repeat eexists; eauto.
      repeat (apply trace_secure_app; eauto).
      apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply CrashBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
          unfold corr2; intros.
          denote Ret as Hret.
          inv_exec'' Hret.
          instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                    [[ hm = hm0 ]] *
                                    [[ bm c= bm0 ]])%pred d1) in H4.
          denote sep_star as Hstar;
            destruct_lift Hstar.
          eassign crashc.
          split; auto.
          do 3 eexists; left; eexists; repeat (split; eauto).         
          simpl; pred_apply; cancel.
        }
          rewrite <- H6; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply only_public_operations_to_trace_secure; auto.
        
      + destruct_lift H2.
        edestruct H.
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0; eauto.
        {
           pred_apply; safecancel.
           eassign dummy; cancel.
           eauto.
           auto.
           destruct_lift H11.
           eassign crashc.
           unfold corr2_weak; intros.
           destruct_lift H11.
           edestruct H8; eauto.
           pred_apply; cancel; eauto.
           rewrite <- H7; cancel; eauto.
         }
         simpl in *; cleanup; split_ors; cleanup; try congruence.
         split.
         do 3 eexists; right; repeat eexists; eauto.
         apply trace_secure_app; auto.
         apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply FailBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; auto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          destruct_lift H11.
          unfold corr2_weak; intros.
          destruct_lift H11.
          edestruct H8; eauto.
          pred_apply; cancel; eauto.
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        Unshelve.
        all: try exact handle.
        all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  Theorem weak_conversion_xcrash:
    forall T T' A1 (p1: prog T) (p2: T -> prog T') pr
      pre post post2 crash1 crash2,
      
      {< (e1: A1),
         PERM: pr
         PRE: bm, hm, pre e1 bm hm
         POST: bm', hm', (fun F r => F * post F r e1 bm' hm')
         XCRASH: bm'', hm'', crash1 e1 bm'' hm'' >} p1 ->
      
      (forall F r e1,
          {<W (_: A1),
              PERM: pr
              PRE: bm, hm, post F r e1 bm hm 
              POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
              XCRASH: bm'', hm'', crash2 e1 bm'' hm'' W>} (p2 r)) ->
      
      (forall e1 bm'' hm'' , crash1 e1 bm'' hm'' =p=> crash2 e1 bm'' hm'') ->
                           
      {<W (e1: A1),
          PERM: pr
          PRE: bm, hm, pre e1 bm hm 
          POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
          XCRASH: bm'', hm'', crash2 e1 bm'' hm'' W>} (Bind p1 p2).
  Proof.
    intros.
    monad_simpl_weak.
    unfold corr2_weak; intros.
    inv_exec_perm.
    - destruct_lift H2.
      edestruct H.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
        rewrite <- H7; cancel; eauto.
        xcrash.
        rewrite H1; eauto.
      }
      
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      inv_exec_perm.
      edestruct H0.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        eauto.
         {
            unfold corr2_weak; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                               [[ x7 = hm0 ]] *
                                               [[ x6 c= bm0 ]])%pred d1) in H12.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
         rewrite <- H7; cancel; eauto.
      }

      simpl in *; cleanup; split_ors; cleanup; try congruence.
      edestruct H8; eauto.
      destruct_lift H11.
      pred_apply; cancel; eauto.
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      split.
      do 3 eexists; left; repeat eexists; eauto.
      repeat (apply trace_secure_app; eauto).
      apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply CrashBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; eauto.
          xcrash.
        rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply only_public_operations_to_trace_secure; auto.
        
      + destruct_lift H2.
        edestruct H.
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
          xcrash.
          rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0; eauto.
        {
           pred_apply; safecancel.
           eassign dummy; cancel.
           eauto.
           auto.
           destruct_lift H11.
           eassign crashc.
           unfold corr2_weak; intros.
           destruct_lift H11.
           edestruct H8; eauto.
           pred_apply; cancel; eauto.
           rewrite <- H7; cancel; eauto.
         }
         simpl in *; cleanup; split_ors; cleanup; try congruence.
         split.
         do 3 eexists; right; repeat eexists; eauto.
         apply trace_secure_app; auto.
         apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply FailBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; auto.
          xcrash.
          rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
          xcrash.
          rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          destruct_lift H11.
          unfold corr2_weak; intros.
          destruct_lift H11.
          edestruct H8; eauto.
          pred_apply; cancel; eauto.
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        Unshelve.
        all: try exact handle; eauto.
        all: unfold Mem.EqDec; apply handle_eq_dec.
Qed.



  Theorem weak_conversion_reverse_xcrash:
    forall T T' A1 (p1: prog T) (p2: T -> prog T') pr
      pre post post2 crash1 crash2,
      
      {<W (e1: A1),
         PERM: pr
         PRE: bm, hm, pre e1 bm hm
         POST: bm', hm', (fun F r => F * post F r e1 bm' hm')
         XCRASH: bm'', hm'', crash1 e1 bm'' hm'' W>} p1 ->
      
      (forall F r e1,
          {< (_: A1),
              PERM: pr
              PRE: bm, hm, post F r e1 bm hm 
              POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
              XCRASH: bm'', hm'', crash2 e1 bm'' hm'' >} (p2 r)) ->
      
      (forall e1 bm'' hm'' , crash1 e1 bm'' hm'' =p=> crash2 e1 bm'' hm'') ->
                           
      {<W (e1: A1),
          PERM: pr
          PRE: bm, hm, pre e1 bm hm 
          POST: bm', hm', (fun F r => F * post2 F r e1 bm' hm')
          XCRASH: bm'', hm'', crash2 e1 bm'' hm'' W>} (Bind p1 p2).
  Proof.
    intros.
    monad_simpl_weak.
    unfold corr2_weak; intros.
    inv_exec_perm.
    - destruct_lift H2.
      edestruct H.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        {
            unfold corr2_weak; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
        rewrite <- H7; cancel; eauto.
        xcrash.
        rewrite H1; eauto.
      }
      
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      inv_exec_perm.
      edestruct H0.
      2: repeat econstructor; eauto.
      {
        pred_apply; safecancel.
        eassign dummy; cancel.
        eauto.
        eauto.
        {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                               [[ x7 = hm0 ]] *
                                               [[ x6 c= bm0 ]])%pred d1) in H12.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
         rewrite <- H7; cancel; eauto.
      }

      simpl in *; cleanup; split_ors; cleanup; try congruence.
      edestruct H8; eauto.
      destruct_lift H11.
      pred_apply; cancel; eauto.
      simpl in *; cleanup; split_ors; cleanup; try congruence.
      split.
      do 3 eexists; left; repeat eexists; eauto.
      repeat (apply trace_secure_app; eauto).
      apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply CrashBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2_weak; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; eauto.
          xcrash.
        rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        eauto.
        
      + destruct_lift H2.
        edestruct H.
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          {
            unfold corr2_weak; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
          xcrash.
          rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        inv_exec_perm.
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0 with (rx:=@Ret T').
         2: eapply CrashBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                               [[ x7 = hm0 ]] *
                                               [[ x6 c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply trace_secure_app; auto.
        apply only_public_operations_to_trace_secure; auto.

        edestruct H0 with (rx:=@Ret T').
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                               [[ x7 = hm0 ]] *
                                               [[ x6 c= bm0 ]])%pred d1) in H12.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.        
        edestruct H8; eauto.
        destruct_lift H11.
        pred_apply; cancel; eauto.
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        split.
        do 3 eexists; right; repeat eexists; eauto.
        apply trace_secure_app; auto.
        apply trace_secure_app; auto.
        apply only_public_operations_to_trace_secure; auto.

    - split_ors; cleanup.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: eapply FailBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2_weak; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H4.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H6; cancel; auto.
          xcrash.
          rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
      + destruct_lift H2.
        edestruct H with (rx:=@Ret T).
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          auto.
          {
            unfold corr2_weak; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post dummy r dummy0 bm0 hm0 *
                                               [[ hm = hm0 ]] *
                                               [[ bm c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
          xcrash.
          rewrite H1; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        inv_exec_perm.
        simpl in *; cleanup; split_ors; cleanup; try congruence.
        edestruct H0 with (rx:=@Ret T').
         2: eapply FailBind; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                               [[ x7 = hm0 ]] *
                                               [[ x6 c= bm0 ]])%pred d1) in H5.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.

        edestruct H0 with (rx:=@Ret T').
        2: repeat econstructor; eauto.
        {
          pred_apply; safecancel.
          eassign dummy; cancel.
          eauto.
          auto.
          {
            unfold corr2; intros.
            denote Ret as Hret.
            inv_exec'' Hret.
            instantiate (2:= fun d1 bm0 hm0 r => (dummy * post2 dummy r dummy0 bm0 hm0 *
                                               [[ x7 = hm0 ]] *
                                               [[ x6 c= bm0 ]])%pred d1) in H12.
            denote sep_star as Hstar;
              destruct_lift Hstar.
            eassign crashc.
            split; auto.
            do 3 eexists; left; eexists; repeat (split; eauto).         
            simpl; pred_apply; cancel.
          }
          rewrite <- H7; cancel; eauto.
        }
        simpl in *; cleanup; split_ors; cleanup; try congruence.        
        edestruct H8; eauto.
        destruct_lift H11.
        pred_apply; cancel; eauto.
        simpl in *; cleanup; split_ors; cleanup; try congruence.

        Unshelve.
        all: try exact handle; eauto.
        all: unfold Mem.EqDec; apply handle_eq_dec.
Qed.

  Opaque corr2 corr2_weak.