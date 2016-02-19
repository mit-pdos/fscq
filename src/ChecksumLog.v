Require Import Hashmap.
Require Import Word.
Require Import Prog.
Require Import BasicProg.
Require Import Hoare.
Require Import Pred.
Require Import Array.
Require Import List.
Require Import SepAuto2.
Require Import Cache.
Require Import Omega.
Require Import GenSep.
Require Import PredCrash.
Require Import Rec.

Import ListNotations.
Set Implicit Arguments.

Definition header_type : Rec.type := Rec.RecF ([
    ("previous_length",  Rec.WordF addrlen);
    ("current_length",  Rec.WordF addrlen);
    ("checksum",   Rec.WordF hashlen);
    ("padding", Rec.WordF (valulen - hashlen - addrlen - addrlen))
  ]).
Definition header := Rec.data header_type.
Definition make_header : header := (@Rec.of_word header_type $0)
                                :=> "checksum" := default_hash.

Theorem header_len :
  valulen = Rec.len header_type.
Proof.
  simpl. rewrite valulen_is. compute. auto.
Qed.

Definition header_to_valu (h : header) : valu.
  rewrite header_len.
  exact (Rec.to_word h).
Defined.

Definition valu_to_header (v : valu) : header.
  rewrite header_len in *.
  exact (Rec.of_word v).
Defined.

Parameter maxlen : addr.
Definition Header : addr := $0.
Definition DataStart : addr := $1.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

(** Log_rep:
  - The current list of values in the log is a prefix of the disk.
  - The checksum and current_length in the header matches the current
    list of values (previous_length can be anything)
  Eventually current_length can live in memory **)
Definition log_rep previous_length vl vdisk hm :
  @pred addr (@weq addrlen) valuset :=
  (exists h current_length,
    let header := make_header
      :=> "previous_length" := ($ previous_length)
      :=> "current_length"  := ($ current_length)
      :=> "checksum"        := h
    in
    [[ hash_list_rep (rev vl) h hm ]] *
    [[ length vl = current_length ]] *
    [[ list_prefix vl vdisk ]] *
    [[ length vdisk = # (maxlen) ]] *
    Header |-> (header_to_valu header, nil) *
    array DataStart (combine vdisk (repeat nil # (maxlen))) $1)%pred.

Definition log_rep' vl vl' hm cs d : pred :=
  BUFCACHE.rep cs d *
  [[ (exists vdisk, log_rep vl vl' vdisk hm)%pred d ]].

Definition append T v cs rx : prog T :=
  let^ (cs, header_valu) <- BUFCACHE.read Header cs;
  let header := valu_to_header header_valu in
  let log_pointer := header :-> "current_length" in
  checksum <- Hash (Word.combine v (header :-> "checksum"));
  cs <- BUFCACHE.write_array DataStart log_pointer $1 v cs;
  cs <- BUFCACHE.write Header (header_to_valu (
          make_header
            :=> "previous_length" := log_pointer
            :=> "current_length" := log_pointer ^+ $1
            :=> "checksum" := checksum
          )) cs;
  cs <- BUFCACHE.sync_array DataStart log_pointer $1 cs;
  cs <- BUFCACHE.sync Header cs;
  rx cs.

Definition truncate T cs rx : prog T :=
  hash0 <- Hash default_valu;
  cs <- BUFCACHE.write Header (header_to_valu (
          make_header
            :=> "previous_length" := $0 (* Could keep the previous length, but not much point... *)
            :=> "current_length"  := $0
            :=> "checksum"        := hash0
          )) cs;
  cs <- BUFCACHE.sync Header cs;
  rx cs.

Theorem append_ok : forall v cs,
  {< d previous_length vl,
  PRE:hm
    [[ length vl < # (maxlen) ]] *
    log_rep' previous_length vl hm cs d
  POST:hm' RET:cs'
    exists d',
      log_rep' (length vl) (vl ++ v :: nil) hm' cs' d'
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' (** TODO **)
  >} append v cs.
Proof.
  unfold append, log_rep', log_rep.
  step.
  pred_apply; cancel.

  step.
  step_idtac.
Admitted.

Theorem truncate_ok : forall cs,
  {< d previous_length vl,
  PRE:hm
    log_rep' previous_length vl hm cs d
  POST:hm' RET:cs'
    exists d',
      log_rep' 0 nil hm' cs' d'
  CRASH:hm'
    exists cs' d', BUFCACHE.rep cs' d' (** TODO **)
  >} truncate cs.
Proof.
  unfold truncate, log_rep', log_rep.
  step.
  step.
  step.
  step.
  solve_hash_list_rep.
  econstructor; eauto.
  unfold list_prefix, firstn; auto.
Qed.