Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

(* Disk with atomicity of n writes. Histories are "backwards": writing and then
reading a block with value n is represented by: (Read d n) :: (Write d n) ::
nil. *)

Definition value := nat.
Definition block := nat.
Definition trans := nat.

Inductive event : Set :=
  | Read: block -> value -> event
  | Write: block -> value -> event
  | Sync: block -> event   (* XXX don't apply to transactions; i.e., TEnd syncs *)
  | TBegin: trans -> event
  | TEnd: trans -> event
  | TSync: trans -> event
  | Crash: event.    (* what does it mean in begin and end: ignore? *)

Definition history := list event.

(* we are now inside a transaction *)
Inductive in_tx: history -> trans -> Prop :=
  | InTX_tbegin: forall h t,
    in_tx (TBegin t :: h) t
  | InTX_read: forall h t b v,
    in_tx h t -> in_tx (Read b v :: h) t
  | InTX_write: forall h t b v,
    in_tx h t -> in_tx (Write b v :: h) t.

Let no_tx h : Prop := forall t, ~ in_tx h t.

(* lastw b v holds when there is a write b v in h since the last crash *)
Inductive lastw: history -> block -> value -> Prop :=
  | LW_write: forall h b v,
    lastw (Write b v :: h) b v
  | LW_write_other: forall h b v wb wv,
    wb <> b -> lastw h b v -> lastw (Write wb wv :: h) b v
  | LW_read: forall h b v rb rv,
    lastw h b v -> lastw (Read rb rv :: h) b v
  | LW_sync: forall h b v sb,
    lastw h b v -> lastw (Sync sb :: h) b v
  | LW_tbegin: forall h b v t,
    lastw h b v -> lastw (TBegin t :: h) b v
  | LW_tend: forall h b v t,
    lastw h b v -> lastw (TEnd t :: h) b v
  | LW_tsync: forall h b v t,
    lastw h b v -> lastw (TSync t :: h) b v.

Let no_write h b : Prop := ~ exists v, lastw h b v.

Lemma lastw_unique:
  forall h b v v', lastw h b v -> lastw h b v' -> v = v'.
Proof.
  induction h; intros; [ inversion H | destruct a ];
  inversion H; inversion H0; crush; apply IHh with (b:=b); assumption.
Qed.

(* lastw for b is decidable: there is a unique last write to b or no write to b. *)
Lemma lastw_dec:
  forall h b, (exists v, lastw h b v) + no_write h b.
Proof.
  induction h; unfold no_write in *.
  - right; intuition; inversion H; inversion H0.
  - intros; destruct IHh with (b:=b); destruct a eqn:DA;
    (* trivial cases *)
    match goal with
    | [ DA: _ = Write _ _ |- _ ] => idtac
    | [ DA: _ = Crash     |- _ ] => right; intuition; inversion H; inversion H0
    | [ e: exists _, _ |- _ ] => 
        left; inversion e; exists x; constructor; assumption
    | [ e: ~ exists _, _ |- _ ] =>
        right; intuition; inversion H; inversion H0; apply n; exists x; assumption
    end.
    (* writes *)
    + left; destruct (eq_nat_dec b b0).
      * rewrite e0; exists v; constructor.
      * inversion e; exists x; constructor; auto; assumption.
    + destruct (eq_nat_dec b b0).
      * left; rewrite e; exists v; constructor.
      * right; intuition; apply n; inversion H; exists x. inversion H0; crush.
Qed.

(* what's a block's value after a transaction? *)
Inductive tx_write: history -> trans -> block -> value -> Prop :=
  | TW_write: forall h t b v,
    in_tx h t -> tx_write (Write b v :: h) t b v
  | TW_write_other: forall h t b v wb wv,
    wb <> b -> tx_write h t b v -> tx_write (Write wb wv :: h) t b v
  | TW_read: forall h t b v rb rv,
    tx_write h t b v -> tx_write (Read rb rv :: h) t b v
  | TW_sync: forall h t b v sb,
    tx_write h t b v -> tx_write (Sync sb :: h) t b v
  | TW_tbegin: forall h b v t ot,
    ot <> t -> tx_write h t b v -> tx_write (TBegin ot :: h) t b v
  | TW_tend: forall h b v t ot,
    tx_write h t b v -> tx_write (TEnd ot :: h) t b v
  | TW_tsync: forall h b v t ot,
    ot <> t -> tx_write h t b v -> tx_write (TSync ot :: h) t b v.

Let tx_pending h b : Prop := exists t v, tx_write h t b v.

Inductive could_ondisk: history -> block -> value -> Prop :=
  | OD_nil: forall b,
    could_ondisk nil b 0
  (* write *)
  | OD_write: forall h b v t,
    ~ in_tx h t -> could_ondisk (Write b v :: h) b v
  | OD_write_other: forall h b v wb wv,
    could_ondisk h b v -> could_ondisk (Write wb wv :: h) b v
  (* sync *)
  | OD_sync_w: forall h b v,
    lastw h b v -> could_ondisk (Sync b :: h) b v
  | OD_sync_nw: forall h b v,
    no_write h b -> could_ondisk h b v -> could_ondisk (Sync b :: h) b v
  | OD_sync_other: forall h b v sb,
    sb <> b -> could_ondisk h b v -> could_ondisk (Sync sb :: h) b v
  (* read *)
  | OD_read_w: forall h b v wv,
    lastw h b wv -> could_ondisk h b v -> could_ondisk (Read b wv:: h) b v
  | OD_read_nw: forall h b v,
    no_write h b -> could_ondisk h b v -> could_ondisk (Read b v :: h) b v
  | OD_read_other: forall h b v rb rv,
    could_ondisk h b v -> could_ondisk (Read rb rv :: h) b v
  (* TSync *)
  | OD_tsync: forall h t b v,
    tx_write h t b v -> could_ondisk (TSync t :: h) b v
  | OD_tsync_other: forall h t b v,
    could_ondisk h b v -> could_ondisk (TSync t :: h) b v
  (* others *)
  | OD_crash: forall h b v,
    could_ondisk h b v -> could_ondisk (Crash :: h) b v
  | OD_tbegin: forall h b v t,
    could_ondisk h b v -> could_ondisk (TBegin t :: h) b v
  | OD_tend: forall h b v t,
    could_ondisk h b v -> could_ondisk (TEnd t :: h) b v.

Inductive could_read: history -> block -> value -> Prop :=
  | Read_write: forall h b v,
    lastw h b v -> could_read h b v
  | Read_crash: forall h b v,
    no_write h b -> could_ondisk h b v -> could_read h b v.

(* blegal h b means that h is legal for disk block b *)
Inductive blegal: history -> block -> Prop :=
  | BL_nil : forall b,
    blegal nil b
  | BL_read: forall h b rb rv,
    blegal h b -> blegal h rb -> could_read h rb rv -> blegal (Read rb rv :: h) b
  | BL_write: forall h b wb wv,
    blegal h b -> blegal h wb -> blegal (Write wb wv :: h) b
  | BL_sync: forall h b sb,
    blegal h b -> blegal h sb -> no_tx h -> ~ tx_pending h sb -> blegal (Sync sb :: h) b
  | BL_crash: forall h b,
    blegal h b -> blegal (Crash :: h) b
  | BL_tbegin: forall h b t,
    blegal h b -> no_tx h -> blegal (TBegin t :: h) b
  | BL_tend: forall h b t,
    blegal h b -> in_tx h t -> blegal (TEnd t :: h) b
  | BL_tsync: forall h b t,
    blegal h b -> no_tx h -> blegal (TSync t :: h) b.

Let   legal h : Prop := forall b, blegal h b.
Let illegal h : Prop := exists b, ~ blegal h b.

Example test_legal_1:
  legal [ Read 1 1 ;  Write 1 1 ].
Proof.
  intro.
  repeat constructor.
Qed.

Example test_legal_2:
  illegal [ Read 0 1 ;  Write 1 1 ].
Proof.
  unfold illegal. intuition. exists 0. intro.
  inversion H. inversion H6.
  - inversion H7.
    inversion H17.
  - inversion H8.
    inversion H17.
Qed.

Example test_legal_3:
  legal [ Read 0 1; Read 1 1 ; Write 0 1; Write 1 1 ].
Proof.
  intro.
  repeat constructor; auto.
Qed.

Example test_legal_4:
  legal [ Read 0 1 ; Read 1 1 ; TEnd 0; Write 0 1 ; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
    | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
    | _ => constructor; auto
  end.
Qed.

(* No syncs inside of a transaction: *)
Example test_legal_5:
  illegal [ Read 0 1 ; Read 1 1 ; TEnd 0; Write 0 1 ; Sync 1; Write 1 1 ; TBegin 0].
Proof.
  unfold illegal. intuition. exists 0. intro.
  inversion H. inversion H5. inversion H12. inversion H18. inversion H23.
Qed.

(* No writes of an incomplete transaction are visible after a crash: *)
Example test_legal_6:
  legal [ Read 0 0; Crash;  Write 0 1; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor
  end.
Qed.

(* Transaction may create before any writes: *)
Example test_legal_6b:
  legal [ Read 0 0; Crash; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor
  end.
Qed.

(* No writes of an incomplete transaction are visible after a crash: *)
Example test_legal_7:
  legal [ Read 1 0; Read 0 0 ; Crash; Write 1 1; Write 0 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor
  end.
Qed.

(* Results of a transactions are not durable: *)
Example test_legal_8:
  legal [ Read 0 0 ; Read 1 0 ; Crash; TEnd 0; Write 0 1 ; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor
  end.
Qed.

(* TSync makes transactions durable: *)
Example test_legal_9:
  legal [ Read 0 1 ; Read 1 1 ; Crash; TSync 0; TEnd 0; Write 0 1 ; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | _ => constructor; auto
  end.
Qed.

(* TSync n makes transaction n durable: *)
Example test_legal_10:
  legal [ Read 0 1 ; Read 1 1 ; Crash; TSync 1; TSync 0; TEnd 1; Write 0 1 ; TBegin 1; TEnd 0; Write 1 1 ; TBegin 0].
Proof.
  intro.
  repeat match goal with
  | [ |- could_read _ _ _ ] => apply Read_crash
  | [ |- no_write _ _ ] => unfold no_write; intuition; inversion H
  | [ |- no_tx _ ] => unfold no_tx; intuition; inversion H
  | [ H: lastw _ _ _ |- _ ] => inversion H
  | [ |- could_ondisk _ _ _ ] => idtac
  | _ => constructor
  end; constructor.
  - apply OD_tsync_other; repeat constructor; auto.
  - apply OD_tsync_other; repeat constructor; auto.
  - repeat constructor; auto.
Qed.

(* After a crash, a new transaction must start with TBegin *)
Example test_legal_11:
   illegal [ Read 0 0 ; Read 0 0 ; TEnd 0; Write 0 1 ; Crash; Write 1 1 ; TBegin 0].
Proof.
  unfold illegal. intuition. exists 0. intro.
  inversion H. inversion H5. inversion H12. inversion H18. inversion H23.
Qed.

Example test_legal_12:
  illegal [ Sync 0; TEnd 0; Write 0 1; TBegin 0].
Proof.
  unfold illegal. intuition. exists 0. intro.
  inversion H. unfold tx_pending in H6. intuition.  
  apply H6.
  exists 0.
  exists 1.
  repeat constructor.
Qed.

(* XXX reads inside of a transaction should probably return the value of most
(perhaps unncommitted) write *)

(* A disk whose reads and writes don't fail *)

Definition addr := nat.
Definition val := nat.

Parameter storage : Set.
Parameter st_init  : storage.
Parameter st_write : storage -> addr -> val -> option storage.
Parameter st_read  : storage -> addr -> option val.

Axiom st_eq:
  forall s a wv s' v,
  st_write s a wv = Some s' ->
  st_read s' a = Some v ->  v = wv.

Axiom st_ne:
  forall s a a' wv s' v v',
  a <> a' ->
  st_write s a wv = Some s' ->
  st_read s  a' = Some v ->
  st_read s' a' = Some v' ->  v = v'.

Axiom st_read_init:
  forall a v, st_read st_init a = Some v -> v = 0.

(*
Lemma disk_read_write_commute:
  forall a a' v v' s,
  a <> a' -> st_read (st_write (st_write s a v) a' v') a =  st_read (st_write (st_write s a' v') a v) a.
Proof.
  intros.
  rewrite disk_read_eq.
  rewrite disk_read_other.
  rewrite disk_read_eq.
  trivial.
  trivial.
Qed.
*)

(* The interface to an atomic disk: *)

Inductive invocation : Set :=
  | do_read: block -> invocation
  | do_write: block -> value -> invocation
  | do_sync: block -> invocation
  | do_begin: trans-> invocation
  | do_end: trans -> invocation
  | do_sync_trans: trans -> invocation.

Inductive result : Set :=
  | rs_read: value -> result
  | rs_bool: bool -> result
  | rs_void: result.

Inductive result_legal : invocation -> result -> Prop :=
  | RL_read: 
    forall b v, result_legal (do_read b) (rs_read v)
  | RL_write:
    forall b v, result_legal (do_write b v) rs_void
  | RL_sync:
    forall b x, result_legal (do_sync b) (rs_bool x)
  | RL_begin:
    forall t x, result_legal (do_begin t) (rs_bool x)
  | RL_end:
    forall t x, result_legal (do_end t) (rs_bool x)
  | RL_tsync:
    forall t x, result_legal (do_sync_trans t) (rs_bool x).

Fixpoint fs_apply_list {fsstate: Set}
                       (init: fsstate)
                       (applyfun: fsstate -> invocation -> fsstate * result)
                       (l: list invocation)
                       : fsstate * history :=
  match l with
  | nil => (init, nil)
  | i :: rest =>
    let (s, h) := fs_apply_list init applyfun rest in
    let (s', r) := applyfun s i in
      match r with
      | rs_bool false => (s', h)
      | _ => match i with
        | do_read b => match r with
          | rs_read v => (s', (Read b v) :: h)
          | _ => (s', h)    (* invalid *)
        end
        | do_write b v =>
          (s', (Write b v) :: h)
        | do_sync b =>
          (s', (Sync b) :: h)
        | do_begin t =>
          (s', (TBegin t) :: h)
        | do_end t => 
          (s', (TEnd t) :: h)
        | do_sync_trans t =>
          (s', (TSync t) :: h)
      end
    end
  end.

Definition fs_legal {fsstate: Set}
                     (init: fsstate)
                     (applyfun: fsstate -> invocation -> fsstate * result) :=
  forall (l: list invocation) (i:invocation) (h: history) (s: fsstate),
  result_legal i (snd (applyfun s i)) /\
  (fs_apply_list init applyfun l = (s, h) -> legal h).


(* An atomic abstract disk that implements the above interface with the above
spec. The abstract disk has a storage device and a list of actions in a
transactions that haven't been applied yet. They will be applied when the
transaction ends/commits atomically.  *)

Record TDisk: Set := mkTDisk {
  disk : storage;
  intrans : bool;
  pending : list invocation   (* list of pending writes in a transaction *)
}.

Definition TDisk_init := mkTDisk st_init false nil.

Definition TDisk_write_disk (s:TDisk) (b:block) (v:value) : TDisk :=
  match (st_write s.(disk) b v) with
    | Some d => mkTDisk d s.(intrans) s.(pending)
    | None   => s  (* TODO: recovery *)
  end.

Definition TDisk_read_disk (s:TDisk) (b:block) : TDisk * result :=
  match (st_read s.(disk) b) with
  | Some v => (s, rs_read v)
  | None   => (s, rs_read 0)  (* TODO: recovery *)
  end.

Fixpoint TDisk_find_pending (p:list invocation) (b:block) : option value :=
  match p with
  | nil => None
  | i :: rest => match i with
    | do_write b v  =>  Some v
    | _ => TDisk_find_pending rest b
    end
  end.

Fixpoint TDisk_commit (s:TDisk) (p:list invocation): TDisk :=
  match p with
  | nil => s
  | i :: rest => match i with
    | do_write b v =>
        let s' := TDisk_commit s rest in
        TDisk_write_disk s' b v
    | _ => (* ignore, should not happen *)
        TDisk_commit s rest
    end
  end.

Definition TDisk_apply (s: TDisk) (i: invocation) : TDisk * result :=
  if (intrans s) then
    match i with
      | do_read b => match (TDisk_find_pending s.(pending) b) with
          | Some v => (s, rs_read v)
          | None => TDisk_read_disk s b
          end
      | do_write b v =>
          (mkTDisk s.(disk) true ((do_write b v) :: s.(pending)), rs_void)
      | do_sync b =>       (s, rs_bool false)
      | do_begin t =>      (s, rs_bool false)
      | do_end _ =>
          let s' := TDisk_commit s s.(pending) in
          (mkTDisk s'.(disk) false nil, rs_bool true)
      | do_sync_trans t => (s, rs_bool false)
    end
  else
    match i with
      | do_read b =>       TDisk_read_disk s b
      | do_write b v =>    (TDisk_write_disk s b v, rs_void)
      | do_sync b =>       (s, rs_bool true) (* do nothing *)
      | do_begin t =>      (mkTDisk s.(disk) true nil, rs_bool true)
      | do_end t =>        (s, rs_bool false)
      | do_sync_trans t => (s, rs_bool true) (* do nothing *)
    end.


(* plan for getting some confidence (ie., fix spec and implementation): *)
Example TDisk_legal_1:
  forall (h:history) (s: TDisk),
    fs_apply_list TDisk_init TDisk_apply [] = (s, h) -> legal h.
Proof.
  intros.
  crush.
  constructor.
Qed.

Example TDisk_legal_2:
  forall (h:history) (s: TDisk),
    fs_apply_list TDisk_init TDisk_apply [do_read 0; do_write 0 1] = (s, h) -> legal h.
Proof.
  intros.
  inversion H. unfold TDisk_apply in H1.
Qed.

Example TDisk_legal_3:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool),
    apply_to_TDisk (mkTDisk st_init []) [do_read 0; do_read 1; do_end 0; do_write 0 1; do_write 1 1; do_begin 0] [] = (b, s, h) -> legal h.
Proof.
  intros.
  inversion H.  
  repeat rewrite disk_read_eq.
  rewrite disk_read_write_commute.
  repeat rewrite disk_read_eq.
  apply test_legal_4.
  crush.
Qed.

Example TDisk_legal_4:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool),
    apply_to_TDisk (mkTDisk st_init []) [do_read 0; do_crash; do_write 0 1; do_begin 0] [] = (b, s, h) -> legal h.
Proof.
  intros.
  inversion H.
  rewrite st_read_init.
  intros.
  apply test_legal_6b.
Qed.

Lemma TDisk_in_tx:
  forall (l: list invocation) (h: history) (s: TDisk),
    apply_to_TDisk (mkTDisk st_init []) l [] = (true, s, h) 
    -> exists t, in_tx h t.
Proof.
  induction l. crush.
  destruct a eqn:IA; case_eq (apply_to_TDisk (mkTDisk st_init []) l []);
  intros; simpl; inversion H0; rewrite H in H2; destruct p;
  destruct b; inversion H2;
  match goal with
  | [ IA : _ = do_end _ |- _ ] =>
      contradict H2; generalize (apply_pending t (pending t) h);
      intros; destruct p; discriminate
  | [ |- exists _ : trans, in_tx (TBegin ?n :: _) _ ] =>
      exists n; constructor
  | _ =>
      rewrite <- H4; apply IHl with (s:=t); assumption
  end.
Qed.

Lemma TDisk_no_tx:
  forall (l: list invocation) (h: history) (s: TDisk),
    apply_to_TDisk (mkTDisk st_init []) l [] = (false, s, h) 
    -> no_tx h.
Proof.
  unfold no_tx; induction l. crush; inversion H0.
  destruct a eqn:IA; case_eq (apply_to_TDisk (mkTDisk st_init []) l []);
  intros; simpl; inversion H0; rewrite H in H2; destruct p;
  destruct b; inversion H2;
  match goal with
  | [ IA : _ = do_end _ |- _ ] =>
      set (x:=apply_pending t0 (pending t0) h) in H2; destruct x;
      inversion H2; intuition; inversion H1
  | _ =>
      intuition; inversion H1; apply IHl with (s:=t0) (h:=h) (t:=t); assumption
  end.
Qed.

Lemma TDisk_could_read_ondisk:
    forall (l: list invocation) (h: history) (s: TDisk) (b:block),
    apply_to_TDisk (mkTDisk st_init []) l [] = (false, s, h) ->
    could_read h b (st_read (disk s) b) -> could_ondisk h b (st_read (disk s) b).
Proof.
  induction l.
  - intros. inversion H. simpl. rewrite st_read_init. constructor.
  - destruct a eqn:IA; case_eq (apply_to_TDisk (mkTDisk st_init []) l []);
    intros; simpl; inversion H0; rewrite H in H3; destruct p.
  Admitted.


Lemma TDisk_could_read:
  forall (l: list invocation) (h: history) (s: TDisk) (t: bool) (b:block),
    apply_to_TDisk (mkTDisk st_init []) l [] = (t, s, h) ->
    could_read h b (st_read (disk s) b).
Proof.
  induction l.
  - intros; inversion H; apply Read_crash.
    unfold no_write; intuition; inversion H0; inversion H4.
    crush. rewrite st_read_init. constructor.
  - destruct a eqn:IA; case_eq (apply_to_TDisk (mkTDisk st_init []) l []);
    intros; simpl; inversion H0; rewrite H in H2; destruct p;
    destruct b0 eqn:IT; inversion H2.

    rewrite <- H5; simpl; apply IHl with (t:=true); assumption.
    admit.
    rewrite <- H5; simpl; apply IHl with (t:=true); assumption.
    admit.
    rewrite <- H5, <- H4; simpl; apply IHl with (t:=true); assumption.
    admit.
    admit.
    admit.
    rewrite <- H5, <- H4; simpl; apply IHl with (t:=true); assumption.
    admit.
    rewrite <- H5, <- H4; simpl; apply IHl with (t:=true); assumption.
    admit.
    apply Read_crash. unfold no_write. intuition. inversion H1. inversion H6.
    constructor. simpl. apply IHl with (b:=b) in H. 



    match goal with
    | [ IT: ?b = true |- _ ] =>
      rewrite <- H5; try rewrite <- H4; simpl; apply IHl with (t:=true); assumption
    | _ => idtac
    end.


(* the main unproven theorem: *)
Theorem TDisk_legal:
  forall (l: list invocation) (h: history) (s: TDisk) (b: bool),
    apply_to_TDisk (mkTDisk st_init []) l [] = (b, s, h) -> legal h.
Proof.
  induction l; [crush; constructor | idtac].
  destruct a; case_eq (apply_to_TDisk (mkTDisk st_init []) l []);
  intros; simpl; inversion H0; rewrite H in H2; destruct p.
  (* read *)
  - destruct b0.
    + inversion H2.  apply IHl with (s:=t) (b:=b).
      rewrite <- H5. rewrite <- H3. assumption.
    + inversion H2.
      constructor; try apply IHl with (s:=t) (b:=false); try assumption.
      rewrite <- H4. apply TDisk_could_read with (l:=l) (t:=false). assumption.
      apply IHl with (b:=false) (h:=h) (s:=t). assumption.
  (* write *)
  - destruct b0.
    + inversion H2. apply IHl with (s:=t) (b:=true). rewrite <- H5. assumption.
    + inversion H2.
      constructor; auto; apply IHl with (s:=t) (b:=false); assumption.
  (* tbegin *)
  - destruct b0; inversion H2.
    + apply IHl with (h:=h0) (b:=true) (s:=t). rewrite <- H5. assumption.
    + assert (legal h). apply IHl with (s:=t) (b:=false); assumption.
      constructor. unfold legal in H1. apply H1.
      apply TDisk_no_tx with (l:=l) (s:=t). assumption.
  (* tend *)
  - admit. (* need lemmas on apply_pending -> legal *)
  (* tsync *)
  - destruct b0; crush; constructor.
    + assert (legal h). apply IHl with (s:=s) (b:=false). assumption.
      unfold legal in H1. apply H1.
    + apply TDisk_no_tx with (l:=l) (s:=s). assumption.
  (* sync *)
  - admit. (* need to fix sync spec *)
  (* crash *)
  - inversion H2. constructor. apply IHl with (s:=t) (b:=b0). assumption.
Qed.

  

(* Use two disks to implement to implement the same behavior as Tdisk but with a
disk for which read or write to disk can crash (jelle's disk).  *)

Record AtomicDisk : Set := mkAtomicLazy2 {
  LogDisk : storage_fail;
  DataDisk : storage_fail
}.

Definition AtomicLazy2_init := mkAtomicLazy2 st_fail_init st_fail_init.

(* An implementation of the interface using logging.  Tend writes a commit
record, and then applies to the logged updates to the data disk.  On recovery,
atomic disk applies any committed logdisk updates to data disk. *)

(* A refinement proof that every state AtomicDisk can be in is a legal state of
Tdisk. The mapping function is something along the line if there is a commit
record, then the atomic disks DataDisk is Tdisk.disk with pending applied.  If
there is no commit record, then the atomic DataDisk is Tdisk.disk (i.e., w/o
pending applied) Maybe a la Nickolai's coqfs implementation? *)

(* Standard refinement conclusion: because AtomicDisk implements TDisk and Tdisk
is correct, then AtomicDisk is correct. *)
