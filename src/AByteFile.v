Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Inode.
Require Import GenSepAuto.
Require Import DiskSet.
Require Import BFile.
Require Import Bytes.
Require Import NEList.

Set Implicit Arguments.

Module ABYTEFILE.

(* Definitions *)
Definition attr := INODE.iattr.
Definition attr0 := INODE.iattr0.

Notation "'byteset'" := (nelist byte).

Record bytefile := mk_bytefile {
  ByFData : list byteset;
  ByFAttr : INODE.iattr
}.
Definition bytefile0 := mk_bytefile nil attr0.
Definition byteset0 := singular byte0.

(* Helper Functions *)
Definition list2byteset (l: list byte): byteset :=
match l with
| nil => byteset0
| h::t => pushdlist t (singular h)
end.

Definition bytes2valubytes sz (b: bytes sz) : bytes valubytes :=
if beq_nat sz valubytes then
(word2bytes valubytes eq_refl (natToWord (valubytes*8)(wordToNat b)))
else
(word2bytes valubytes eq_refl (natToWord (valubytes*8) 0)). (* need to corrrect this so that it returns 0 padding *)

Definition list2valu l: valu :=
bytes2valu (bytes2valubytes (bcombine_list l)).

Definition valu2list v : list byte :=
bsplit_list (valu2bytes v).

Fixpoint make_all_list {A: Type} (l: list A): list (list A):=
match l with
| nil => nil
| h::t => (cons h nil)::(make_all_list t)
end.

Fixpoint elemwise_concat {A: Type} (l1:list A)  (l2: list(list A)): list (list A) :=
match l1 with
| nil => match l2 with
          | nil => nil
          | _ => l2
          end
| h1::t1 => match l2 with
            | nil => make_all_list l1
            | h2::t2 => (h1::h2)::elemwise_concat t1 t2
            end
end.

(* Fixpoint maxlist l: nat :=
match l with
| nil => 0
| h::t => max h (maxlist t)
end. *)

Definition full_list (vs: valuset) := (fst vs)::(snd vs).

Definition valuset2bytesets (vs: valuset): list byteset :=
map list2byteset (fold_right elemwise_concat nil (map valu2list (full_list vs))).

Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A :=
firstn len (skipn off l).
  
Definition rep f fy :=
(ByFData fy) = firstn (# (INODE.ABytes (BFILE.BFAttr f)))
     (flat_map valuset2bytesets (BFILE.BFData f)) /\
ByFAttr fy = BFILE.BFAttr f.

Definition read_first_block T lxp ixp inum fms block_off byte_off read_length rx: prog T :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      rx ^(fms, data_init).
      
      
Definition first_block_match r fy block_off byte_off read_length: Prop :=
let block_size := valubytes in
forall i, (i < read_length) -> selN r i byte0 = 
    fst (selN (ByFData fy) (block_size*block_off + byte_off + i) byteset0).


Definition read_middle_blocks T lxp ixp inum fms block_off num_of_full_blocks rx: prog T :=
let^ (data) <- (ForN_ (fun i =>
        (pair_args_helper (fun data (_:unit) => (fun lrx => 
        
        let^ (fms, block) <- BFILE.read lxp ixp inum (block_off + i) fms; (* get i'th block *)
        lrx ^(data++(valu2list block))%list (* append its contents *)
        
        )))) 1 num_of_full_blocks
      (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
      (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
rx ^(fms, data).

(* let^ ((data:list byte)) <- ForN i < num_of_full_blocks 
            Ghost [ lxp ixp inum fms block_off ] 
            Loopvar [ (data:list byte) ] 
            Continuation lrx
            Invariant [[True]] OnCrash [[True]] 
            Begin
            let^ (fms, block) <- BFILE.read lxp ixp inum (block_off +1 + i) fms; (* get i'th block *)
            lrx ^(data++(valu2list block))%list (* append its contents *) 
            Rof ^((nil:list byte));
rx ^(fms, data). *)

Definition middle_blocks_match r fy block_off num_of_full_blocks: Prop :=
let block_size := valubytes in
forall i, (i < num_of_full_blocks * block_size) -> 
selN r i byte0 = fst (selN (ByFData fy) (block_off*block_size +i) byteset0).


Definition read_last_block  T lxp ixp inum fms block_off read_length rx: prog T :=
let^ (fms, last_block) <- BFILE.read lxp ixp inum block_off fms;   (* get final block *)
let data_last := (get_sublist (valu2list last_block) 0 read_length) in (* get final block data *)
rx ^(fms, data_last).

Definition last_block_match r fy block_off read_length: Prop :=
let block_size := valubytes in
forall i, (i < read_length) -> selN r i byte0 = 
    fst (selN (ByFData fy) (block_size*block_off + i) byteset0).


(*Interface*)
Definition read T lxp ixp inum off len fms rx : prog T :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                    
      let len := min len (flen - off) in
      let block_size := valubytes in            (* get block size *)
      let block_off := off / block_size in              (* calculate block offset *)
      let byte_off := off mod block_size in          (* calculate byte offset *)
      let first_read_length := min (block_size - byte_off) len in (*# of bytes that will be read from first block*)
      
      (*Read first block*)
      let^ (fms, data_first) <- read_first_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
      
      let len_remain := (len - first_read_length) in  (* length of remaining part *)
      let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)

      (*for loop for reading full blocks in between*)
      let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;

      let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
      let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
      
      (*Read last block*)
      let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
      rx ^(fms, data_first++data_middle++data_last)%list                  (* append everything and return *)
  } 
  else                                                 (* if offset is not valid, return nil *)
  {    
    rx ^(fms, nil)
  }
} 
else                                                   (* if read length is not valid, return nil *)
{    
  rx ^(fms, nil)
}.

(* Definition write T lxp ixp inum off data fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
    let len := min (length data) (flen - off) in
    let^ (fms, block0) <- BFILE.read lxp ixp inum 0 fms;        (* get block 0*)
    let block_size := get_block_size block0 in            (* get block size *)
    let block_off := off / block_size in              (* calculate block offset *)
    let byte_off := off mod block_size in          (* calculate byte offset *)
    let first_write_length := min (block_size - byte_off) len in (*# of bytes that will be read from first block*)
    
    let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *) 
    let first_block_list := valu2list first_block in
    let first_block_write := list2valu ((get_sublist first_block_list 0 byte_off)     (* Construct first block*)
                              ++(get_sublist data 0 first_write_length))%list in 
    (*Write first block*)                          
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum block_off ms;
    ms <- LOG.write lxp (# bn) first_block_write ms;
    
    let len_remain := (len - first_write_length) in  (* length of remaining part *)
    let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
    
    (*for loop for writing full blocks in between*)
    let^ (temp) <- (ForN_ (fun i =>
      (pair_args_helper (fun data (_:unit) => (fun lrx => 
      
      let^ (ms, bn) <- INODE.getbnum lxp ixp inum (block_off+i) ms;(* get i'th block number *)
      ms <- LOG.write lxp (# bn) (list2valu (get_sublist data (first_write_length + i*block_size) block_size)) ms;
      lrx ^(nil)
      
      )))) 1 num_of_full_blocks
    (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
    (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
    
    let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
    let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
    
    (*Write last block*)
    let^ (fms, last_block) <- BFILE.read lxp ixp inum off_final fms;   (* get final block *)
    let last_block_write := list2valu ((get_sublist data off_final len_final) 
                            ++ (get_sublist (valu2list last_block) len_final (block_size - len_final)))%list in
                            
    let^ (ms, bn) <- INODE.getbnum lxp ixp inum (off_final) ms;(* get final block number *)
    ms <- LOG.write lxp (# bn) last_block_write ms;
  
    rx ^(BFILE.mk_memstate al ms).
    
  
  
(* same as write except uses LOG.dwrite *)
Definition dwrite T lxp ixp inum off data fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
    let len := min (length data) (flen - off) in
    let^ (fms, block0) <- BFILE.read lxp ixp inum 0 fms;        (* get block 0*)
    let block_size := get_block_size block0 in            (* get block size *)
    let block_off := off / block_size in              (* calculate block offset *)
    let byte_off := off mod block_size in          (* calculate byte offset *)
    let first_write_length := min (block_size - byte_off) len in (*# of bytes that will be read from first block*)
    let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *) 
    let first_block_list := valu2list first_block in
    let first_block_write := list2valu ((get_sublist first_block_list 0 byte_off)     (* Construct first block*)
                              ++(get_sublist data 0 first_write_length))%list in 
    (*Write first block*)                          
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum block_off ms;
    ms <- LOG.dwrite lxp (# bn) first_block_write ms;
    
    let len_remain := (len - first_write_length) in  (* length of remaining part *)
    let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
    
    (*for loop for writing full blocks in between*)
    let^ (temp) <- (ForN_ (fun i =>
      (pair_args_helper (fun data (_:unit) => (fun lrx => 
      
      let^ (ms, bn) <- INODE.getbnum lxp ixp inum (block_off+i) ms;(* get i'th block number *)
      ms <- LOG.dwrite lxp (# bn) (list2valu (get_sublist data (first_write_length + i*block_size) block_size)) ms;
      lrx ^(nil)
      
      )))) 1 num_of_full_blocks
    (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
    (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
    
    let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
    let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
    
    (*Write last block*)
    let^ (fms, last_block) <- BFILE.read lxp ixp inum off_final fms;   (* get final block *)
    let last_block_write := list2valu ((get_sublist data off_final len_final) 
                            ++ (get_sublist (valu2list last_block) len_final (block_size - len_final)))%list in
                            
    let^ (ms, bn) <- INODE.getbnum lxp ixp inum (off_final) ms;(* get final block number *)
    ms <- LOG.dwrite lxp (# bn) last_block_write ms;
  
    rx ^(BFILE.mk_memstate al ms).
 *)

(*Same as BFile*)
 Definition getlen T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    rx ^(BFILE.mk_memstate al ms, n).

  Definition getattrs T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getattrs lxp ixp inum ms;
    rx ^(BFILE.mk_memstate al ms, n).

  Definition setattrs T lxp ixp inum a fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    ms <- INODE.setattrs lxp ixp inum a ms;
    rx (BFILE.mk_memstate al ms).

  Definition updattr T lxp ixp inum kv fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    ms <- INODE.updattr lxp ixp inum kv ms;
    rx (BFILE.mk_memstate al ms).
    

(* Helper length lemmas. Not currently in use. *)

Lemma make_all_list_len: forall (A:Type) (l: list A), length(make_all_list l) = length l.
Proof.
induction l.
reflexivity.
simpl; rewrite IHl; reflexivity.
Qed.

Lemma elemwise_concat_nil_len: forall A (l: list(list A)), length (elemwise_concat nil l) = length l.
Proof. induction l; reflexivity. Qed.

Lemma elemwise_concat_len: forall A (l1: list A) (l2: list(list A)), length (elemwise_concat l1 l2) = max (length l1) (length l2).
Proof.
induction l1; intros.
rewrite elemwise_concat_nil_len; reflexivity.
destruct l2; simpl; auto.
rewrite make_all_list_len; reflexivity.
Qed.

(* Lemma list2byteset_len: forall l, length(snd(list2byteset l)) = length l.
Proof.
induction l.
simpl.
reflexivity.
simpl. unfold list2byteset in *.
rewrite pushdlist_length in *.
auto.
Qed. *)


Lemma valu2list_len : forall v, length(valu2list v) = valubytes.
Proof.
intros.
unfold valu2list.
rewrite bsplit_list_len.
reflexivity.
Qed.

(* Lemma valu2byteset_len: forall v, length(snd(valu2byteset v)) = valubytes.
Proof.
unfold valu2byteset.
intros.
rewrite list2byteset_len.
rewrite bsplit_list_len.
reflexivity.
Qed. *)

(* Lemma maplength_len: forall x l, In x (map make_all_list (map snd (map valu2byteset l))) -> length x = valubytes.
Proof.
induction l.
simpl; intros; contradiction.
simpl; intros.
destruct H.
destruct H.
rewrite make_all_list_len.
rewrite valu2byteset_len.
reflexivity.
apply IHl.
apply H.
Qed. *)

Lemma valuset2bytesets_len: forall vs, length(snd vs) > 0 -> length(valuset2bytesets vs) = valubytes.
Proof. Admitted.
(* intros.
unfold valuset2bytesets.
rewrite map_length.
eapply maplength_len.
SearchAbout In.
apply in_map_iff.
intros.
rewrite foldc_elemwise_len.
induction (snd vs).
inversion H.
simpl.
rewrite make_all_list_len.
rewrite valu2byteset_len.
apply maplength_len.
SearchAbout max.
rewrite Max.max_l.
reflexivity.
rewrite IHl.
reflexivity.
unfold maxlist.
unfold map.
rewrite Max.max_idempotent.
reflexivity.
SearchAbout max. *)

(* helper le-lt lemmas. *)
Lemma le_trans: forall n m k, n <= m -> m <= k -> n <= k.
Proof. intros. omega. Qed.

Lemma le_weaken_l: forall n m k, n + m <= k -> n <= k.
Proof. intros. omega. Qed.

Lemma le_weaken_r: forall n m k, n + m <= k -> m <= k.
Proof. intros. omega. Qed.

Lemma lt_weaken_l: forall n m k, n + m < k -> n < k.
Proof. intros. omega. Qed.

Lemma lt_weaken_r: forall n m k, n + m < k -> m < k.
Proof. intros. omega. Qed.

Lemma le2lt_l: forall n m k, n + m <= k -> m > 0 -> n < k.
Proof. intros. omega. Qed.

Lemma le2lt_r: forall n m k, n + m <= k -> n > 0 -> m < k.
Proof. intros. omega. Qed.

SearchAbout min. 

Lemma le_by_bl: forall f,   (# (INODE.ABytes (BFILE.BFAttr f))) <= length(BFILE.BFData f) * valubytes.
Proof. Admitted.


Lemma iattr_len_eq: forall f fy, rep f fy -> # (INODE.ABytes (BFILE.BFAttr f)) = length(ByFData fy).
Proof. Admitted.
(* unfold rep. intros.
destruct H.
rewrite H.
rewrite firstn_length.
rewrite min_l.
reflexivity.
rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.
apply le_by_bl.
apply Forall_forall.
intros.

SearchAbout In.

apply in_map_iff in H1.
destruct H1; subst.
destruct H1; subst.
apply valuset2bytesets_len.
simpl.
unfold valuset2bytesets.
rewrite map_length.
rewrite foldc_elemwise_len. *)

Lemma fst_preserve: forall A B (v1 v2: A*B), v1 = v2 -> fst v1 = fst v2.
Proof. intros. rewrite H. reflexivity. Qed.

(* Lemma map_some: forall i (A:Type) (l: list A) (v: A) v',
v = selN l i v' -> selN (map (B:= option A) (@Some A)  l) i (Some v') = Some v.
Proof.
intros.
erewrite selN_map.
SearchAbout Some.
symmetry;
apply selN_selNopt.
simpl.
induction i.
intros. *)



Lemma block_content_match: forall f vs block_off def, (exists F, 
(F * block_off|-> vs)%pred (list2nmem(BFILE.BFData f)))-> 
vs = selN (BFILE.BFData f) block_off def.
Proof. Admitted.
(* intros.
destruct H.
unfold valu2list.
apply bsplit_list_preserve.
apply valu2bytes_preserve.
apply fst_preserve.
eapply ptsto_valid' in H.
unfold list2nmem in H.
simpl in H.
unfold map in H.
auto.
unfold  sep_star in H.
unfold ptsto in H.
SearchAbout ptsto.
simpl in H.
unfold selN.
SearchAbout fst. *)
 
Lemma pick_from_block: forall f block_off vs i def def', 
i < valubytes -> (exists F,  (F * block_off |-> vs)%pred (list2nmem (BFILE.BFData f))) ->
selN (valu2list (fst vs)) i def = selN (valu2list (fst (selN (BFILE.BFData f) block_off def'))) i def.
Proof.
intros.
destruct H0.
rewrite block_content_match with (f:=f) (vs:=vs) (block_off:= block_off) (def:= def').
reflexivity.
exists x.
apply H0.
Qed.
 
Lemma concat_hom_selN: forall A (lists: list(list A)) i n k def, 
Forall (fun sublist => length sublist = k) lists ->
i < k ->
selN (concat lists) (n * k + i) def = selN (selN lists n nil) i def.
Proof.
induction lists.
reflexivity.
intros.
rewrite Forall_forall in H.
destruct n.
simpl.
apply selN_app1.
destruct H with (x:= a).
apply in_eq.
apply H0.
destruct H with (x:=a).
apply in_eq.
simpl.
rewrite selN_app2.
replace (length a + n * length a + i - length a) with (n * length a + i).
apply IHlists.
rewrite Forall_forall.
intros.
SearchAbout In.
eapply in_cons in H1.
apply H in H1.
apply H1.
apply H0.
remember (n * length a + i) as x.
replace (length a + n * length a + i - length a) with (length a + x - length a).
omega.
rewrite Heqx.
omega.
SearchAbout le.
unfold ge.
remember (n * length a + i) as x.
replace (length a + n * length a + i) with (length a + x).
apply le_plus_l.
omega.
Qed.

Lemma selN_flat_map: forall f block_off i def def', 
selN (flat_map valuset2bytesets (BFILE.BFData f))  (valubytes * block_off + i) def = 
selN (valuset2bytesets(selN (BFILE.BFData f) block_off def')) i def.
Proof.
intros.
SearchAbout flat_map.
rewrite flat_map_concat_map.
rewrite selN_map.
 
 
 
(*Specs*)
Theorem read_first_block_ok: forall lxp bxp ixp inum fms block_off byte_off read_length,
 {< F Fm Fi Fd m0 m flist ilist frees f fy,
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFILE.BFData f) ::: (Fd * block_off |->?) ]]] * (* May be unnecessary but couldn't prove it without it. *)
           [[ rep f fy ]] *
           [[ 0 < read_length]] * 
           [[ block_off*block_size + byte_off + read_length <= file_length ]]*
           [[ byte_off + read_length <= block_size]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ first_block_match r fy block_off byte_off read_length ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_first_block lxp ixp inum fms block_off byte_off read_length.
Proof.
unfold read_first_block, rep.
step.
rewrite H17 in H5.
rewrite le_by_bl in H5.
apply le2lt_l in H5.
repeat apply lt_weaken_l in H5.
apply Nat.mul_lt_mono_pos_r in H5.
apply H5.
omega.
apply H6.
step.
unfold first_block_match.
intros.
rewrite H15.
rewrite selN_firstn.
SearchAbout concat.
unfold get_sublist.
rewrite <- skipn_firstn_comm.
rewrite skipn_selN.
rewrite selN_firstn.
erewrite pick_from_block with (f:=f) (block_off:=block_off).
unfold valu2list.
SearchAbout flat_map.
rewrite firstn_selN.
SearchAbout skipn.
Admitted.




Theorem read_middle_blocks_ok: forall lxp bxp ixp inum fms block_off num_of_full_blocks,
 {< F Fm Fi m0 m flist ilist frees f fy,
    PRE:hm
          let file_length := (wordToNat (INODE.ABytes (BFILE.BFAttr f))) in
          let block_size := valubytes in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ rep f fy ]] *
           [[ block_off + num_of_full_blocks*block_size < file_length]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ middle_blocks_match r fy block_off num_of_full_blocks]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks.
Proof. Admitted.

Theorem read_last_block_ok: forall lxp bxp ixp inum fms block_off read_length,
 {< F Fm Fi m0 m flist ilist frees f fy,
    PRE:hm
          let file_length := (wordToNat (INODE.ABytes (BFILE.BFAttr f))) in
          let block_size := valubytes in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ rep f fy ]] *
           [[ block_off*block_size + read_length <= file_length ]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ last_block_match r fy block_off read_length ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_last_block lxp ixp inum fms block_off read_length.
Proof. Admitted.


Theorem read_ok : forall lxp bxp ixp inum off len fms block_off byte_off
                   first_read_length
                   last_read_length num_of_full_blocks,
    {< F Fm Fi m0 m flist ilist frees f fy,
    PRE:hm
        let block_size := valubytes in
        let file_length := length (ByFData fy) in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ rep f fy ]] *
           [[ first_read_length + num_of_full_blocks*block_size + last_read_length = len]] *
           [[ byte_off + first_read_length <= block_size ]] *
           [[ off + len <= file_length ]]
    POST:hm' RET:^(fms', r)
          let file_length := length (ByFData fy) in
          let len := min len (file_length - off) in
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ first_block_match r fy block_off byte_off first_read_length ]] *
          [[ middle_blocks_match r fy block_off num_of_full_blocks ]] *
          [[ last_block_match r fy (block_off+num_of_full_blocks) last_read_length ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read lxp ixp inum off len fms.
Proof. Admitted.


  Ltac assignms :=
    match goal with
    [ fms : BFILE.memstate |- LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (BFILE.MSLL ?e) _ ] =>
      is_evar e; eassign (BFILE.mk_memstate (BFILE.MSAlloc fms) ms); simpl; eauto
    end.

  Local Hint Extern 1 (LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (BFILE.MSLL ?e) _) => assignms.
    
    Theorem getlen_ok : forall lxp bxps ixp inum ms,
    {< F Fm Fi m0 m f flist ilist frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxps ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm' *
           [[ r = length (BFILE.BFData f) /\ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm'
    >} getlen lxp ixp inum ms.
  Proof.
    unfold getlen, BFILE.rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    destruct_lift H; eauto.
    simplen.

    cancel.
    eauto.
  Qed.


  Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm' *
           [[ r = BFILE.BFAttr f /\ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm'
    >} getattrs lxp ixp inum ms.
  Proof.
    unfold getattrs, BFILE.rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite.
    subst; eauto.

    cancel.
    eauto.
  Qed.



  Theorem setattrs_ok : forall lxp bxps ixp inum a ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxps ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' f' ilist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxps ixp flist' ilist' frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = BFILE.mk_bfile (BFILE.BFData f) a ]] *
           [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' /\
              let free := BFILE.pick_balloc frees (BFILE.MSAlloc ms') in
              BFILE.ilist_safe ilist free ilist' free ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} setattrs lxp ixp inum a ms.
  Proof.
    unfold setattrs, BFILE.rep.
    safestep.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold BFILE.file_match; cancel.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold BFILE.ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Qed.


  Theorem updattr_ok : forall lxp bxps ixp inum kv ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxps ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' ilist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxps ixp flist' ilist' frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = BFILE.mk_bfile (BFILE.BFData f) (INODE.iattr_upd (BFILE.BFAttr f) kv) ]] *
           [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' /\
              let free := BFILE.pick_balloc frees (BFILE.MSAlloc ms') in
              BFILE.ilist_safe ilist free ilist' free ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} updattr lxp ixp inum kv ms.
  Proof.
    unfold updattr, BFILE.rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold BFILE.file_match; cancel.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold BFILE.ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Qed.
    
    
    
    
          
(*From BFile

  Definition datasync T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    ms <- LOG.dsync_vecs lxp (map (@wordToNat _) bns) ms;
    rx (mk_memstate al ms).

  Definition sync T lxp (ixp : INODE.IRecSig.xparams) fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    ms <- LOG.sync lxp ms;
    rx (mk_memstate (negb al) ms).

  Definition pick_balloc A (a : A * A) (flag : bool) :=
    if flag then fst a else snd a.

  Definition grow T lxp bxps ixp inum v fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, len) <- INODE.getlen lxp ixp inum ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (ms, r) <- BALLOC.alloc lxp (pick_balloc bxps al) ms;
      match r with
      | None => rx ^(mk_memstate al ms, false)
      | Some bn =>
           let^ (ms, succ) <- INODE.grow lxp (pick_balloc bxps al) ixp inum bn ms;
           If (bool_dec succ true) {
              ms <- LOG.write lxp bn v ms;
              rx ^(mk_memstate al ms, true)
           } else {
             rx ^(mk_memstate al ms, false)
           }
      end
    } else {
      rx ^(mk_memstate al ms, false)
    }.

  Definition shrink T lxp bxps ixp inum nr fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    ms <- BALLOC.freevec lxp (pick_balloc bxps (negb al)) l ms;
    ms <- INODE.shrink lxp (pick_balloc bxps (negb al)) ixp inum nr ms;
    rx (mk_memstate al ms).
End*)

End ABYTEFILE.