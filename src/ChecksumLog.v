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

Set Implicit Arguments.

Definition DataStart : addr := $0.
Definition HashStart : addr := $1.
Definition Interval : addr := $2.
Parameter maxlen : addr.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

(* TODO: Probably need something about how the next hash block on disk
  doesn't match the current values. *)
Definition log_rep vl hl (log_pointer : addr) hm vdisk hdisk :
  @pred addr (@weq addrlen) valuset :=
  (exists unsynced_data unsynced_hashes,
    [[ length vdisk = # (maxlen) /\ length hdisk = # (maxlen) ]] *
    [[ length vl = # (log_pointer) /\ length hl = # (log_pointer) ]] *
    [[ list_prefix (rev vl) vdisk /\ list_prefix (rev hl) hdisk]] *
    array DataStart (combine vdisk unsynced_data) Interval *
    [[ length unsynced_data = length vdisk ]] *
    array HashStart (combine (map hash_to_valu hdisk)
                              unsynced_hashes) Interval *
    [[ length unsynced_hashes = length hdisk ]] *
    [[ hash_list_prefixes vl hl hm ]]
  )%pred.

Definition log_rep' vl hl log_pointer hm cs d : pred :=
  BUFCACHE.rep cs d *
  [[ (exists vdisk hdisk, log_rep vl hl log_pointer hm vdisk hdisk)%pred d ]].

Definition read T i (log_pointer : addr) cs rx : prog T :=
  let^ (cs, v) <- BUFCACHE.read_array DataStart i Interval cs;
  rx ^(cs, log_pointer, v).

Definition append T v log_pointer cs rx : prog T :=
  let^ (cs, h) <- IfRx irx (weq log_pointer $0) {
    h <- Hash default_valu;
    irx ^(cs, h)
  } else {
    let^ (cs, h) <- BUFCACHE.read_array HashStart (log_pointer ^- $1) Interval cs;
    irx ^(cs, valu_to_hash h)
  };
  h <- Hash (Word.combine v h);
  cs <- BUFCACHE.write_array DataStart log_pointer Interval v cs;
  cs <- BUFCACHE.write_array HashStart log_pointer Interval (hash_to_valu h) cs;
  rx ^(cs, log_pointer ^+ $1).

Definition truncate T cs rx : prog T :=
  h <- Hash default_valu;
  cs <- BUFCACHE.write_array HashStart $0 Interval (hash_to_valu h) cs;
  rx (cs, natToWord addrlen 0).

Theorem append_ok : forall log_pointer v cs,
  {< d vl hl,
  PRE:hm
    [[ # (log_pointer) < # (maxlen) ]] *
    log_rep' vl hl log_pointer hm cs d
  POST:hm' RET:^(cs', log_pointer')
    exists d' h,
      log_rep' (v :: vl) (h :: hl) log_pointer' hm' cs' d'
  CRASH:hm'
    exists cs' d',
      (log_rep' vl hl log_pointer hm' cs' d' \/
       exists h,
         log_rep' (v :: vl) (h :: hl) (log_pointer ^+ $1) hm' cs' d')
  >} append v log_pointer cs.
Proof.
Admitted.
