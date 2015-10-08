Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSep.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import ByteFile.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.

Set Implicit Arguments.
Import ListNotations.

Parameter cachesize : nat.

Definition compute_xparams (data_bitmaps inode_bitmaps : addr) :=
  (* Block $0 stores the superblock (layout information).
   * The other block numbers, except for Log, are relative to
   * the Log data area, which starts at $1.
   * To account for this, we bump [log_base] by $1, to ensure that
   * the data area does not run into the logging structures.
   *)
  let data_blocks := data_bitmaps ^* BALLOC.items_per_valu in
  let inode_blocks := inode_bitmaps ^* BALLOC.items_per_valu ^/ INODE.items_per_valu in
  let inode_base := data_blocks in
  let balloc_base := inode_base ^+ inode_blocks ^+ inode_bitmaps in
  let log_base := $1 ^+ balloc_base ^+ data_bitmaps in
  let log_size := $ LOG.addr_per_block in
  let max_addr := log_base ^+ $3 ^+ log_size in
  (Build_fs_xparams
   (Build_log_xparams $1 log_base (log_base ^+ $1) (log_base ^+ $2) log_size)
   (Build_inode_xparams inode_base inode_blocks)
   (Build_balloc_xparams (inode_base ^+ inode_blocks) inode_bitmaps)
   (Build_balloc_xparams balloc_base data_bitmaps)
   $0
   max_addr).

Definition set_root_inode fsxp rootinum :=
  Build_fs_xparams
    fsxp.(FSXPLog)
    fsxp.(FSXPInode)
    fsxp.(FSXPInodeAlloc)
    fsxp.(FSXPBlockAlloc)
    rootinum
    fsxp.(FSXPMaxBlock).

Definition mkfs T data_bitmaps inode_bitmaps rx : prog T :=
  let fsxp := compute_xparams data_bitmaps inode_bitmaps in
  cs <- BUFCACHE.init cachesize;
  cs <- sb_init fsxp cs;
  mscs <- LOG.init (FSXPLog fsxp) cs;
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  mscs <- BALLOC.init' (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
  mscs <- BALLOC.init' (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
  (* XXX this overflows the transaction and makes it impossible for mkfs to succeed *)
  (* mscs <- INODE.init (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) mscs; *)
  let^ (mscs, r) <- BALLOC.alloc_gen (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
  match r with
  | None =>
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx (Err ENOSPC)
  | Some inum =>
    let fsxp' := set_root_inode fsxp inum in
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    rx (OK ^(mscs, fsxp))
  end.

Definition recover {T} rx : prog T :=
  cs <- BUFCACHE.init_recover (if eq_nat_dec cachesize 0 then 1 else cachesize);
  let^ (cs, fsxp) <- sb_load cs;
  mscs <- LOG.recover (FSXPLog fsxp) cs;
  rx ^(mscs, fsxp).

Local Opaque BUFCACHE.rep.

Theorem recover_ok :
  {< fsxp old newpred,
  PRE
    crash_xform (LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) old newpred)
  POST RET:^(mscs, fsxp')
    [[ fsxp' = fsxp ]] *
    (LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction old) mscs \/
     exists new, LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction new) mscs *
     [[ newpred (list2mem new) ]])
  CRASH
    LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) old newpred
  >} recover.
Proof.
  unfold recover, LOG.would_recover_either_pred; intros.

  eapply pimpl_ok2; eauto with prog.
  intros. norm'l. unfold stars; simpl.
  repeat ( setoid_rewrite crash_xform_exists_comm ||
           setoid_rewrite crash_xform_sep_star_dist ||
           setoid_rewrite crash_xform_lift_empty ).
  cancel.

  destruct (eq_nat_dec cachesize 0); congruence.

  step.
  autorewrite with crash_xform. cancel.

  eapply pimpl_ok2; eauto with prog.
  unfold LOG.would_recover_either_pred.
  cancel.

  set_evars; rewrite crash_xform_sep_star_dist; subst_evars.
  set_evars; rewrite crash_xform_sep_star_dist; subst_evars.
  cancel; eauto.

  step.
  unfold LOG.rep. setoid_rewrite crash_xform_sb_rep. cancel.
  unfold LOG.rep. setoid_rewrite crash_xform_sb_rep. cancel.
  subst. pimpl_crash. cancel. autorewrite with crash_xform. cancel.

  autorewrite with crash_xform.
  rewrite LOG.after_crash_pred'_would_recover_either_pred'.
  cancel.

  pimpl_crash. norm'l; unfold stars; simpl. autorewrite with crash_xform.
  norm. cancel. intuition.
  eapply pred_apply_crash_xform_pimpl; eauto.
  autorewrite with crash_xform.
  rewrite LOG.after_crash_pred'_would_recover_either_pred'.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (recover) _) => apply recover_ok : prog.


Definition file_get_attr T fsxp inum mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, attr).

Theorem file_getattr_ok : forall fsxp inum mscs,
  {< m pathname Fm Ftop tree bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs  *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ r = attr ]]
  CRASH  LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m
  >} file_get_attr fsxp inum mscs.
Proof.
  unfold file_get_attr.
  hoare.
  apply LOG.would_recover_old_either.
  rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
  rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.

Ltac recover_ro_ok := intros;
  repeat match goal with 
  | [ |- forall_helper _ ] => idtac "forall"; unfold forall_helper; intros; eexists; intros
  | [ |- corr3 ?pre' _ _ ] => idtac "corr3 pre"; eapply corr3_from_corr2_rx; eauto with prog
  | [ |- corr3 _ _ _ ] => idtac "corr3"; eapply pimpl_ok3; intros
  | [ |- pimpl (exis (fun F_ : pred => _ ))  _ ] =>  
    idtac "bounded"; setoid_rewrite LOG.notxn_bounded_length at 1; cancel; eauto
  | [ |- corr2 _ _ ] => idtac "corr2"; step
  | [ |- pimpl (crash_xform _) _ ] => idtac "crash_xform"; autorewrite with crash_xform
  | [ |- pimpl (sep_star _ (crash_xform (LOG.would_recover_either _ _ _ _ ))) _ ] =>  
        idtac "sep_star xform"; rewrite LOG.would_recover_either_pred_diskIs; cancel
  | [ |- pimpl (sep_star _ (LOG.rep _ _ (NoTransaction _) _)) _ ] =>  
    idtac "sep_star rep"; rewrite LOG.notxn_bounded_length
  | [ H: pimpl (crash_xform _) _ |- _ ] => idtac "crash_xform2"; rewrite H; cancel
  | [ H: diskIs _ _ |- _ ] => idtac "unfold"; unfold diskIs in *
  | [ |- pimpl (LOG.rep _ _ (NoTransaction ?a) _) (LOG.rep _ _ (NoTransaction ?v) _) ] => idtac "rewrite";
    replace (v) with (a) by ( eapply list2mem_inj; eauto ); cancel
  | [ |- pimpl (LOG.would_recover_either_pred _ _ _ _ ) _ ] => idtac "would_rec";
       rewrite LOG.would_recover_either_pred_diskIs_rev by auto; cancel
  end.


Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {<< m pathname Fm Ftop tree bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs  *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ r = attr ]]
  REC RET:^(mscs, fsxp)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs 
  >>} file_get_attr fsxp inum mscs >> recover.
Proof.
  recover_ro_ok.
Qed.


Definition file_get_sz T fsxp inum mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, len) <- DIRTREE.getlen fsxp inum mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, len).

Theorem file_get_sz_ok : forall fsxp inum mscs,
  {< m F Fm Ftop tree pathname bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) F (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]]
  POST RET:^(mscs, sz)
         LOG.rep fsxp.(FSXPLog) F (NoTransaction m) mscs *
         [[ sz = $ (length bytes) ]]
  CRASH  LOG.would_recover_either (FSXPLog fsxp) F m m
  >} file_get_sz fsxp inum mscs.
Proof.
  unfold file_get_sz.
  hoare.
  unfold BYTEFILE.rep in *. deex. intuition.
  unfold BYTEFILE.rep in *. deex. intuition.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (file_get_sz _ _ _) _) => apply file_get_sz_ok : prog.

Theorem file_get_sz_recover_ok : forall fsxp inum mscs,
  {<< m Fm Ftop tree pathname bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]]
  POST RET:^(mscs, sz)
         LOG.rep fsxp.(FSXPLog) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ sz = $ (length bytes) ]]
  REC RET:^(mscs, fsxp)
         LOG.rep fsxp.(FSXPLog) (sb_rep fsxp) (NoTransaction m) mscs
  >>} file_get_sz fsxp inum mscs >> recover.
Proof.
  recover_ro_ok.
Qed.


Definition file_resize T fsxp inum newlen mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, ok) <- DIRTREE.resize fsxp inum newlen mscs;
  If (bool_dec ok true) {
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, false)
  }.

Theorem file_resize_ok : forall fsxp inum newlen mscs,
  {< m pathname Fm Ftop tree bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs  *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]] *
         [[ goodSize addrlen newlen ]]
  POST RET:^(mscs, ok)
         [[ ok = false ]] * LOG.rep fsxp.(FSXPLog) (sb_rep fsxp) (NoTransaction m) mscs \/
         (exists m', LOG.rep fsxp.(FSXPLog) (sb_rep fsxp) (NoTransaction m') mscs * 
          exists tree' bytes', [[ ok = true ]] *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
         [[ bytes' = firstn newlen bytes ++ (repeat $0 (newlen - length bytes)) ]])
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
           exists tree' bytes',
         (Fm * DIRTREE.rep fsxp Ftop tree')*
         [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
         [[ bytes' = firstn newlen bytes ++ (repeat $0 (newlen - length bytes)) ]])
  >} file_resize fsxp inum newlen mscs.
Proof.
  unfold file_resize.
  hoare.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (file_resize  _ _ _ _) _) => apply file_resize_ok : prog.

Ltac recover_rw_ok := unfold forall_helper; intros; eexists; intros; eapply pimpl_ok3;
  [eapply corr3_from_corr2_rx; eauto with prog | idtac ];
  cancel; eauto; [ step | autorewrite with crash_xform ];
  match goal with H: crash_xform _ =p=> _ |- crash_xform _ * _ =p=> _ => rewrite H end; cancel; step.


Theorem file_resize_recover_ok : forall fsxp inum newlen mscs,
  {<< m pathname Fm Ftop tree bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs  *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]] *
         [[ goodSize addrlen newlen ]]
  POST RET:^(mscs, ok)
         [[ ok = false ]] * LOG.rep fsxp.(FSXPLog) (sb_rep fsxp) (NoTransaction m) mscs \/
         (exists m', LOG.rep fsxp.(FSXPLog) (sb_rep fsxp) (NoTransaction m') mscs * 
          exists tree' bytes', [[ ok = true ]] *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
         [[ bytes' = firstn newlen bytes ++ (repeat $0 (newlen - length bytes)) ]])
  REC RET:^(mscs, fsxp)   
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
           exists tree' bytes',
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
         [[ bytes' = firstn newlen bytes ++ (repeat $0 (newlen - length bytes)) ]]
  >>} file_resize fsxp inum newlen mscs >> recover.
Proof.
  recover_rw_ok.
Qed.


Definition read_bytes T fsxp inum off len mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, data) <- DIRTREE.read_bytes fsxp inum off len mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, data).

Theorem read_bytes_ok : forall fsxp inum off len mscs,
  {< m F Fm Ftop tree pathname bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) F (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]]
  POST RET:^(mscs,b)
         exists Fx v,
         LOG.rep fsxp.(FSXPLog) F (NoTransaction m) mscs *
         [[ (Fx * arrayN off v)%pred (list2nmem bytes) ]] *
         [[ @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type (BYTEFILE.buf_len b))
           (BYTEFILE.buf_data b) = v ]] *
         (* non-error guarantee *)
         [[ 0 < len -> off < length bytes -> 0 < BYTEFILE.buf_len b ]]
  CRASH  LOG.would_recover_either (FSXPLog fsxp) F m m
  >} read_bytes fsxp inum off len mscs.
Proof.
  unfold read_bytes.
  hoare.
  apply LOG.would_recover_old_either.
  rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
  rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (read_bytes _ _ _ _ _) _) => apply read_bytes_ok : prog.

Theorem read_bytes_recover_ok : forall fsxp inum off len mscs,
  {<< m Fm Ftop tree pathname bytes attr,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]]
  POST RET:^(mscs,b)
       exists Fx v,
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
       [[ (Fx * arrayN off v)%pred (list2nmem bytes) ]] *
       [[ @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type (BYTEFILE.buf_len b))
         (BYTEFILE.buf_data b) = v ]] *
       (* non-error guarantee *)
       [[ 0 < len -> off < length bytes -> 0 < BYTEFILE.buf_len b ]]
  REC RET:^(mscs,fsxp)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
  >>} read_bytes fsxp inum off len mscs >> recover.
Proof.
  recover_ro_ok.
Qed.

Definition update_bytes T fsxp inum off len (data:bytes len) mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs) <- DIRTREE.update_bytes fsxp inum off data mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, ok).

Theorem update_bytes_ok: forall fsxp inum off len (newbytes:bytes len) mscs,
   {< m pathname Fm Ftop tree bytes attr olddata Fx,
   PRE LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
       [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]] *
       [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]] *
       [[ length olddata = len ]]
   POST RET: ^(mscs, ok)
       [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
       [[ ok = true ]] *
       exists m' tree' bytes',
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ let newdata := @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes in
          (Fx * arrayN off newdata)%pred (list2nmem bytes') ]]
   CRASH LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
       exists tree' bytes',
       (Fm * DIRTREE.rep fsxp Ftop tree') *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ let newdata := @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes in
          (Fx * arrayN off newdata)%pred (list2nmem bytes') ]] )
   >} update_bytes fsxp inum off newbytes mscs.
Proof.
  unfold update_bytes.
  time hoare. (* 60s *)
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel; eauto.
Qed.

Hint Extern 1 ({{_}} progseq (update_bytes _ _ _ _ _) _) => apply update_bytes_ok : prog.

Theorem update_bytes_recover_ok: forall fsxp inum off len (newbytes:bytes len) mscs,
   {<< m pathname Fm Ftop tree bytes attr olddata newdata Fx,
   PRE LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
       [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]] *
       [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]] *
       (* this spec uses an existential newdata since length olddata = len
          gives dependent type issues, at least when using the automation *)
       [[ newdata =
            @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes ]] *
       [[ length olddata = length newdata ]]
   POST RET: ^(mscs, ok)
       [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
       [[ ok = true ]] *
       exists m' tree' bytes',
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ (Fx * arrayN off newdata)%pred (list2nmem bytes') ]]
    REC RET:^(mscs,fsxp)
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
      exists m' tree' bytes',
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ (Fx * arrayN off newdata)%pred (list2nmem bytes') ]]
   >>} update_bytes fsxp inum off newbytes mscs >> recover.
Proof.
  (* recover_rw_ok fails in step *)
  (* manually begin recover_rw_ok *)
  unfold forall_helper; intros; eexists; intros; eapply pimpl_ok3.
  eapply corr3_from_corr2_rx.
  eauto with prog.
  eauto with prog.

  (* take over for step *)
  intros.
  cancel; eauto.
  - replace (length v6).
    replace v7.
    rewrite Rec.array_of_word_length with (ft := BYTEFILE.byte_type).
    auto.
  - step.
  (* resume recover_rw_ok *)
  - autorewrite with crash_xform.
    rewrite H3.
    subst v7.
    cancel.
    step.
Qed.

Definition append T fsxp inum off len (data:bytes len) mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, ok) <- DIRTREE.append fsxp inum off data mscs;
  If (bool_dec ok true) {
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, false)
  }.

Theorem append_ok: forall fsxp inum off len (newbytes:bytes len) mscs,
   {< m pathname Fm Ftop tree Fi bytes attr,
   PRE LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
       [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]] *
       [[ Fi (list2nmem bytes) ]] *
       [[ goodSize addrlen (off + len) ]] *
       (* makes this an append *)
       [[ length bytes <= off ]]
   POST RET: ^(mscs, ok)
       [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
       [[ ok = true ]] *
       exists m' tree' bytes' zeros,
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ let newdata := @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes in
           (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
       [[ zeros = arrayN (length bytes) (repeat $0 (off - length bytes)) ]]
   CRASH LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
       exists tree' bytes' zeros,
       (Fm * DIRTREE.rep fsxp Ftop tree') *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ let newdata := @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes in
            (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
       [[ zeros = arrayN (length bytes) (repeat $0 (off - length bytes)) ]] )
   >} append fsxp inum off newbytes mscs.
Proof.
  unfold append.
  time hoare. (* 60s *)
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel; eauto.
Qed.

Hint Extern 1 ({{_}} progseq (append _ _ _ _ _) _) => apply append_ok : prog.

Theorem append_recover_ok: forall fsxp inum off len (newbytes:bytes len) mscs,
   {<< m pathname Fm Ftop tree Fi bytes attr,
   PRE LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
       [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum bytes attr) ]] *
       [[ Fi (list2nmem bytes) ]] *
       [[ goodSize addrlen (off + len) ]] *
       (* makes this an append *)
       [[ length bytes <= off ]]
   POST RET: ^(mscs, ok)
       [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
       [[ ok = true ]] *
       exists m' tree' bytes' zeros,
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ let newdata := @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes in
           (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
       [[ zeros = arrayN (length bytes) (repeat $0 (off - length bytes)) ]]
   REC RET: ^(mscs,fsxp)
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
      exists m' tree' bytes' zeros,
       LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum bytes' attr) tree ]] *
       [[ let newdata := @Rec.of_word (Rec.ArrayF BYTEFILE.byte_type len) newbytes in
            (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
       [[ zeros = arrayN (length bytes) (repeat $0 (off - length bytes)) ]]
   >>} append fsxp inum off newbytes mscs >> recover.
Proof.
  recover_rw_ok.
Qed.

Definition readdir T fsxp dnum mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, files) <- SDIR.dslist (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) dnum mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, files).

Theorem readdir_ok: forall fsxp dnum mscs,
  {< F1 A m dsmap,
  PRE      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs  *
           [[ SDIR.rep_macro F1 A m (FSXPBlockAlloc fsxp) (FSXPInode fsxp) dnum dsmap ]]
  POST RET:^(mscs,res)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ listpred SDIR.dslmatch res dsmap ]]
  CRASH    LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m
  >} readdir fsxp dnum mscs.
Proof.
  unfold readdir.
  hoare.
  apply LOG.would_recover_old_either.
  rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
  rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (readdir _ _ _ ) _) => apply readdir_ok : prog.

Theorem readdir_recover_ok: forall fsxp dnum mscs,
  {<< F1 A m dsmap,
  PRE      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs  *
           [[ SDIR.rep_macro F1 A m (FSXPBlockAlloc fsxp) (FSXPInode fsxp) dnum dsmap ]]
  POST RET:^(mscs,res)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ listpred SDIR.dslmatch res dsmap ]]
  REC RET:^(mscs, fsxp)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
  >>} readdir fsxp dnum mscs >> recover.
Proof.
  recover_ro_ok.
Qed.

Definition create T fsxp dnum name mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
  match oi with
  | None =>
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, None)
  | Some inum =>
    mscs <- DIRTREE.setattr fsxp inum
                            (BYTEFILE.Build_bytefile_attr $0 $0 $0) mscs;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    match ok with
    | true => rx ^(mscs, Some inum)
    | false => rx ^(mscs, None)
    end
  end.

Theorem create_ok : forall fsxp dnum name mscs,
  {< m pathname Fm Ftop tree tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,r)
          [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
           (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum nil BYTEFILE.attr0) tree ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
            exists inum tree',
            (Fm * DIRTREE.rep fsxp Ftop tree') *
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum nil BYTEFILE.attr0) tree ]])
  >} create fsxp dnum name mscs.
Proof.
  unfold create.
  hoare.
  erewrite DIRTREE.find_subtree_tree_graft by eauto; reflexivity.
  eapply pimpl_or_r; right; cancel.
  erewrite DIRTREE.update_subtree_tree_graft by eauto; reflexivity.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
  erewrite DIRTREE.update_subtree_tree_graft by eauto; reflexivity.
  Grab Existential Variables.
  all: eauto.
  exact BFILE.bfile0.
Qed.

Hint Extern 1 ({{_}} progseq (create _ _ _ _ ) _) => apply create_ok : prog.

Theorem create_recover_ok : forall fsxp dnum name mscs,
  {<< m pathname Fm Ftop tree tree_elem,
  PRE     [[ cachesize <> 0 ]] *
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,r)
          [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum nil BYTEFILE.attr0) tree  ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
           exists inum tree',
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum nil BYTEFILE.attr0) tree  ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]]
  >>} create fsxp dnum name mscs >> recover.
Proof.
  recover_rw_ok.
Qed.

Definition mkdev T fsxp dnum name type dev mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
  match oi with
  | None =>
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, None)
  | Some inum =>
    mscs <- DIRTREE.setattr fsxp inum
                            (BYTEFILE.Build_bytefile_attr $0 type dev) mscs;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    match ok with
    | true => rx ^(mscs, Some inum)
    | false => rx ^(mscs, None)
    end
  end.

Definition mkdir T fsxp dnum name mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, oi) <- DIRTREE.mkdir fsxp dnum name mscs;
  match oi with
  | None =>
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, None)
  | Some inum =>
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    match ok with
    | true => rx ^(mscs, Some inum)
    | false => rx ^(mscs, None)
    end
  end.

Theorem mkdir_ok: forall fsxp dnum name mscs,
  {< m pathname Fm Ftop tree tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,r)
          [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
           (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' =  DIRTREE.update_subtree pathname (DIRTREE.TreeDir dnum
                      ((name, DIRTREE.TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
            exists inum tree',
            (Fm * DIRTREE.rep fsxp Ftop tree') *
            [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeDir dnum
                      ((name, DIRTREE.TreeDir inum nil) :: tree_elem)) tree ]])
  >} mkdir fsxp dnum name mscs.
Proof.
  unfold mkdir.
  hoare.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (mkdir _ _ _ _ ) _) => apply mkdir_ok : prog. 

Theorem mkdir_recover_ok : forall fsxp dnum name mscs,
  {<< m pathname Fm Ftop tree tree_elem,
  PRE     [[ cachesize <> 0 ]] *
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,r)
          [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' =   DIRTREE.update_subtree pathname (DIRTREE.TreeDir dnum
                      ((name, DIRTREE.TreeDir inum nil) :: tree_elem)) tree]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
           exists inum tree',
            [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeDir dnum
                      ((name, DIRTREE.TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]]
  >>} mkdir fsxp dnum name mscs >> recover.
Proof.
  recover_rw_ok.
Qed.


Definition delete T fsxp dnum name mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, ok) <- DIRTREE.delete fsxp dnum name mscs;
  If (bool_dec ok true) {
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, false)
  }.


Theorem delete_ok: forall fsxp dnum name mscs,
  {< m pathname Fm Ftop tree tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs, ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
           (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists tree', [[ ok = true ]] *
            [[ tree' =   DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) tree  ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
            exists tree',
            (Fm * DIRTREE.rep fsxp Ftop tree') *
            [[ tree' =  DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) tree ]])
  >} delete fsxp dnum name mscs.
Proof.
  unfold delete.
  hoare.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (delete _ _ _ _ ) _) => apply delete_ok : prog. 

Theorem delete_recover_ok : forall fsxp dnum name mscs,
  {<< m pathname Fm Ftop tree tree_elem,
  PRE     [[ cachesize <> 0 ]] *
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs, ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists tree', [[ ok = true ]] *
            [[ tree' =   DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) tree ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
           exists tree',
            [[ tree' = DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) tree ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]]
  >>} delete fsxp dnum name mscs >> recover.
Proof.
  recover_rw_ok.
Qed.


Definition lookup T fsxp dnum names mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, r) <- DIRTREE.namei fsxp dnum names mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, r).

Theorem lookup_ok: forall fsxp dnum fnlist mscs,
  {< m Fm Ftop tree,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = DIRTREE.dirtree_inum tree ]] *
           [[ DIRTREE.dirtree_isdir tree = true ]]
  POST RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ r = DIRTREE.find_name fnlist tree ]]
  CRASH   LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m
  >} lookup fsxp dnum fnlist mscs.
Proof.
  unfold lookup.
  hoare.
  apply LOG.would_recover_old_either.
  rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
  rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (lookup _ _ _ _) _) => apply lookup_ok : prog.


Theorem lookup_recover_ok : forall fsxp dnum fnlist mscs,
  {<< m Fm Ftop tree,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = DIRTREE.dirtree_inum tree ]] *
           [[ DIRTREE.dirtree_isdir tree = true ]]
  POST RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ r = DIRTREE.find_name fnlist tree ]]
  REC RET:^(mscs, fsxp)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
  >>} lookup fsxp dnum fnlist mscs >> recover.
Proof.
  recover_ro_ok.
Qed.

Definition rename T fsxp dnum srcpath srcname dstpath dstname mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname mscs;
  If (bool_dec r true) {
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- LOG.abort (FSXPLog fsxp) mscs;
    rx ^(mscs, false)
  }.

Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
  {< m Ftop tree cwd tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (DIRTREE.rep fsxp Ftop tree) (list2mem m) ]] *
          [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
          exists srcnum srcents dstnum dstents subtree pruned renamed tree',
          (DIRTREE.rep fsxp Ftop tree')%pred *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]])
  >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
Proof.
  unfold rename.
  hoare.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.

Theorem rename_recover_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
  {<< m Ftop tree cwd tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (DIRTREE.rep fsxp Ftop tree) (list2mem m) ]] *
          [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
  >>} rename fsxp dnum srcpath srcname dstpath dstname mscs >> recover.
Proof.
  recover_rw_ok.
Qed.

Definition statfs T fsxp mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
  let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, free_blocks, free_inodes).
