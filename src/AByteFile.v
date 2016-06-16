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

Record proto_bytefile := mk_proto_bytefile {
  PByFData : list (list byteset)
}.
Definition proto_bytefile0 := mk_proto_bytefile nil.

Record unified_bytefile := mk_unified_bytefile {
  UByFData : list byteset
}.
Definition unified_bytefile0 := mk_unified_bytefile nil.

Record bytefile := mk_bytefile {
  ByFData : list byteset;
  ByFAttr : INODE.iattr
}.
Definition bytefile0 := mk_bytefile nil attr0.
Definition byteset0 := singular byte0.

Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).
Definition valuset0 := singular valu0.

(* Helper Functions *)
Fixpoint chunk_rec A (l : list A) k n : list (list A) := 
match n with
| O => l::nil
| S n' => (firstn k l)::(chunk_rec (skipn k l) k n')
end.

Definition chunk A (l: list A) k: list(list A) :=
  chunk_rec l k ((length l)/k).



Definition bytes2valubytes sz (b: bytes sz) : bytes valubytes :=
(word2bytes valubytes eq_refl (natToWord (valubytes*8)(wordToNat b))).

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

Fixpoint maxlist l: nat :=
match l with
| nil => 0
| h::t => max h (maxlist t)
end.

Definition selN' {A: Type} i def (l: list A): A :=
selN l i def.

Fixpoint valuset2bytesets_rec (vs: list (list byte)) i: list byteset :=
match i with
| O => nil
| S i' => (valuset2bytesets_rec vs i')++((list2nelist byteset0 (map (selN' i' byte0) vs))::nil)
end.

Definition valuset2bytesets (vs: valuset): list byteset :=
valuset2bytesets_rec (map valu2list (nelist2list vs)) valubytes.

(* Definition valuset2bytesets (vs: valuset): list byteset :=
map (list2nelist (A:= byte) byteset0) (fold_right elemwise_concat nil (map valu2list (nelist2list vs))). *)

Definition bytesets2valuset (bs: list byteset) : valuset :=
list2nelist valuset0 (map list2valu (fold_right elemwise_concat nil (map (@nelist2list byte) bs))).

Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A :=
firstn len (skipn off l).

Definition proto_bytefile_valid f pfy: Prop :=
(PByFData pfy) = map valuset2bytesets (BFILE.BFData f).

Definition unified_bytefile_valid pfy ufy: Prop := 
UByFData ufy = concat (PByFData pfy).

Definition bytefile_valid ufy fy: Prop :=
ByFData fy = firstn (length(ByFData fy)) (UByFData ufy).

  
Definition rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f pfy ufy fy :=
(LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
[[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
[[[ flist ::: (Fi * inum |-> f) ]]] *
[[ proto_bytefile_valid f pfy ]] *
[[ unified_bytefile_valid pfy ufy ]] *
[[ bytefile_valid ufy fy ]] * 
[[ # (INODE.ABytes (ByFAttr fy)) = length(ByFData fy)]])%pred .

Definition read_first_block lxp ixp inum fms block_off byte_off read_length :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(fms, data_init).
      


Definition read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks:=
let^ (data) <- (ForN_ (fun i =>
        (pair_args_helper (fun data (_:unit) => 
        
        let^ (fms, block) <- BFILE.read lxp ixp inum (block_off + i) fms; (* get i'th block *)
        Ret ^(data++(valu2list block))%list (* append its contents *)
        
        ))) 1 num_of_full_blocks
      (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
      (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
Ret ^(fms, data).

(* let^ ((data:list byte)) <- ForN i < num_of_full_blocks 
            Ghost [ lxp ixp inum fms block_off ] 
            Loopvar [ (data:list byte) ] 
            Invariant [[True]] OnCrash [[True]] 
            Begin
            let^ (fms, (block: valu)) <- BFILE.read lxp ixp inum (block_off +1 + i) fms; (* get i'th block *)
            Ret ^(data++(valu2list block))%list (* append its contents *) 
            Rof ^((nil:list byte));
Ret ^(fms, data). *)



Definition read_last_block  lxp ixp inum fms block_off read_length :=
let^ (fms, last_block) <- BFILE.read lxp ixp inum block_off fms;   (* get final block *)
let data_last := (get_sublist (valu2list last_block) 0 read_length) in (* get final block data *)
Ret ^(fms, data_last).



(*Interface*)
Definition read lxp ixp inum off len fms :=
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
      If (lt_dec 0 num_of_full_blocks)                        (* if read length > 0 *)
      {  
        (*for loop for reading full blocks in between*)
        let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
        let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        If (lt_dec 0 len_final)
        {
          let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
          Ret ^(fms, data_first++data_middle++data_last)%list  
        }
        else
        {
          Ret ^(fms, data_first++data_middle)%list  
        }
      }
      else
      {
        let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        If (lt_dec 0 len_final)
        {
          let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
          Ret ^(fms, data_first++data_last)%list  
        }
        else
        {
          Ret ^(fms, data_first)%list  
        }
      }
  } 
  else                                                 (* if offset is not valid, return nil *)
  {    
    Ret ^(fms, nil)
  }
} 
else                                                   (* if read length is not valid, return nil *)
{    
  Ret ^(fms, nil)
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
 Definition getlen lxp ixp inum fms :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    Ret ^(BFILE.mk_memstate al ms, n).

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
    

(* Helper length lemmas.*)

Lemma make_all_list_len: forall (A:Type) (l: list A),
 length(make_all_list l) = length l.
Proof.
induction l.
reflexivity.
simpl; rewrite IHl; reflexivity.
Qed.

Lemma elemwise_concat_nil_len: forall A (l: list(list A)), length (elemwise_concat nil l) = length l.
Proof. induction l; reflexivity. Qed.

Lemma elemwise_concat_len_nil: forall A (l: list A), length (elemwise_concat l nil) = length l.
Proof. induction l. reflexivity. simpl. rewrite make_all_list_len. reflexivity. Qed.

Lemma elemwise_concat_len: forall A (l1: list A) (l2: list(list A)),
 length (elemwise_concat l1 l2) = max (length l1) (length l2).
Proof.
induction l1; intros.
rewrite elemwise_concat_nil_len; reflexivity.
destruct l2; simpl; auto.
rewrite make_all_list_len; reflexivity.
Qed.

Lemma elemwise_concat_expand: forall A (l1 l2:list A) (l3: list( list A)) def,
l1<>nil -> elemwise_concat l1 (l2::l3) = 
((selN l1 0 def) :: l2) :: (elemwise_concat (skipn 1 l1) l3).
Proof.
unfold not; induction l1; intros.
destruct H; reflexivity.
reflexivity.
Qed.

Lemma elemwise_concat_hom_len: forall A (l2: list(list A)) (l1: list A) ,
length l1 = length l2 -> 
length (elemwise_concat l1 l2) = length l1.
Proof.
induction l2; intros.
rewrite elemwise_concat_len_nil.
reflexivity.
simpl.
rewrite elemwise_concat_len.
rewrite H.
apply Nat.max_id.
Qed.

Lemma valu2list_len : forall v,
 length(valu2list v) = valubytes.
Proof.
intros.
unfold valu2list.
rewrite bsplit_list_len.
reflexivity.
Qed.

Lemma not_nil_ex: forall A (l: list A),
 l <> nil ->
 exists x, (In x l)%pred.
Proof.
unfold not.
induction l; intros.
destruct H; reflexivity.
exists a.
apply in_eq.
Qed.

Lemma fold_right_elem_len: forall A x (l: list (list A)),
length (fold_right elemwise_concat x l) =
 max (length x) (maxlist (map (@length A) l)).
Proof.
induction l.
simpl.
rewrite Max.max_0_r.
reflexivity.
simpl.
rewrite elemwise_concat_len.
rewrite IHl.
rewrite Max.max_assoc.
replace (Nat.max (length a) (length x))
  with (Nat.max (length x) (length a)).
rewrite <- Max.max_assoc.
reflexivity.
apply Max.max_comm.
Qed.

Lemma maxlist_len: forall l, 
l <> nil -> 
maxlist (map (fun x : valu => length (valu2list x)) l) = valubytes.
Proof.
induction l; intros.
destruct H; reflexivity.
simpl.
rewrite valu2list_len.
destruct l.
simpl.
apply Nat.max_0_r.
rewrite IHl.
apply Nat.max_id.
unfold not.
intros; inversion H0.
Qed.

Lemma valuset2bytesets_rec_len: forall i l, 
length(valuset2bytesets_rec l i) = i.
Proof. intros.
induction i.
reflexivity.
simpl.
rewrite app_length.
rewrite IHi.
simpl;
omega.
Qed.

Lemma valuset2bytesets_len: forall vs, 
length(valuset2bytesets vs) = valubytes.
Proof.
intros.
unfold valuset2bytesets.
apply valuset2bytesets_rec_len.
Qed.

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

Lemma mult_ne_O_l: forall n m p, p * n < p * m -> p > 0.
Proof. 
induction p; intros.
repeat rewrite <- mult_n_O in H; inversion H.
omega.
Qed.

Lemma mult_ne_O_r: forall n m p, n * p < m * p -> p > 0.
Proof. 
induction p; intros.
repeat rewrite <- mult_n_O in H; inversion H.
omega.
Qed.

Lemma plus_lt_compat_rev: forall n m p, p + n < p + m -> n < m.
Proof. intros. omega. Qed.

Lemma lt_mult_weaken: forall p n m, n * p < m * p  -> n < m.
Proof.
assert(A: forall x, 0 * x = 0). intros. omega.
induction n. intros.
destruct m.
rewrite A in H; inversion H.
omega. intros.
destruct m.
rewrite A in H; inversion H.
apply lt_n_S.
apply IHn.
simpl in H.
apply plus_lt_compat_rev in H.
apply H.
Qed.

Lemma some_eq: forall A (x y: A), Some x = Some y <-> x = y.
Proof.
split; intros.
inversion H; reflexivity.
rewrite H; reflexivity.
Qed.


Lemma block_content_match: forall F f vs block_off def, 
(F * block_off|-> vs)%pred (list2nmem(BFILE.BFData f))-> 
vs = selN (BFILE.BFData f) block_off def.
Proof.
intros.
unfold valu2list.
eapply ptsto_valid' in H.
unfold list2nmem in H.
erewrite selN_map in H.
simpl in H.
unfold map in H.
symmetry;
apply some_eq. apply H.
eapply selN_map_some_range.
apply H.
Qed.

Lemma pick_from_block: forall F f block_off vs i def def', 
i < valubytes -> (F * block_off |-> vs)%pred (list2nmem (BFILE.BFData f)) ->
selN (valu2list (fst vs)) i def = selN (valu2list (fst (selN (BFILE.BFData f) block_off def'))) i def.
Proof.
intros.
erewrite block_content_match with (f:=f) (vs:=vs) (block_off:= block_off) (def:= def').
reflexivity.
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
eapply in_cons in H1.
apply H in H1.
apply H1.
apply H0.
remember (n * length a + i) as x.
replace (length a + n * length a + i - length a) with (length a + x - length a).
omega.
rewrite Heqx.
omega.
unfold ge.
remember (n * length a + i) as x.
replace (length a + n * length a + i) with (length a + x).
apply le_plus_l.
omega.
Qed.

Lemma selN_flat_map: forall f block_off i def def', 
block_off < length(BFILE.BFData f) -> i < valubytes ->
selN (flat_map valuset2bytesets (BFILE.BFData f))  (block_off * valubytes  + i) def = 
selN (valuset2bytesets(selN (BFILE.BFData f) block_off def')) i def.
Proof.
intros.
rewrite flat_map_concat_map.
rewrite concat_hom_selN.
erewrite selN_map.
reflexivity.
apply H.
rewrite Forall_forall.
intros.
rewrite in_map_iff in H1.
destruct H1.
destruct H1.
rewrite <- H1.
apply valuset2bytesets_len.
apply H0.
Qed.
 
Lemma fst_list2byteset: forall A (l:list A) def, fst(list2nelist (singular def) l) =  selN l 0 def.
Proof.
induction l.
reflexivity.
simpl.
unfold singular.
rewrite pushdlist_app.
reflexivity.
Qed.

Lemma selN_make_all_list: forall A (l: list A) i def,
 i < length l ->
  selN (make_all_list l) i nil = (selN l i def)::nil.
Proof.
induction l.
intros.
inversion H.
intros.
destruct i.
reflexivity.
simpl.
apply IHl.
simpl in H.
omega.
Qed.

Lemma selN_elemwise_concat: forall A (a: list A) (l: list (list A)) i def',
 i < length a -> selN (elemwise_concat a l) i nil = (selN a i def')::(selN l i nil).
Proof.
induction a; intros.
inversion H.
destruct i.
destruct l;
reflexivity.
destruct l.
simpl.
apply selN_make_all_list.
simpl in H.
omega.
simpl.
apply IHa.
simpl in H.
omega.
Qed.

Lemma selN_fold_elem: forall (A: Type) (l: list(list A)) i k def, 
Forall (fun sublist => length sublist = k) l ->
i < k -> selN (fold_right elemwise_concat nil l) i nil =
map (selN' i def) l.
Proof.
induction l;
intros.
reflexivity.
simpl.
erewrite selN_elemwise_concat.
erewrite IHl.
reflexivity.
rewrite Forall_forall in *.
intros.
apply H.
apply in_cons.
apply H1.
apply H0.
rewrite Forall_forall in *.
rewrite H.
apply H0.
apply in_eq.
Qed.

Lemma flat_map_len: forall vs, length(flat_map valuset2bytesets vs) = length(vs) * valubytes.
Proof.
induction vs.
reflexivity.
simpl.
rewrite app_length.
rewrite IHvs.
rewrite valuset2bytesets_len.
reflexivity.
Qed.

Lemma len_f_fy: forall f fy,
ByFData fy =
     firstn (length(ByFData fy))
       (flat_map valuset2bytesets (BFILE.BFData f))->
 length (ByFData fy) <= length (BFILE.BFData f) * valubytes.
Proof.
intros.
rewrite H.
rewrite firstn_length.
rewrite flat_map_len.
apply Min.le_min_r.
Qed.

Lemma fold_elem_expand: forall A (l: list (list A)) a,
fold_right elemwise_concat nil (a::l) = 
elemwise_concat a (fold_right elemwise_concat nil l).
Proof. intros; reflexivity. Qed.

(* Lemma fold_elem_expand: forall A (l: list (list A)) a,
fold_right elemwise_concat nil (a::l) = 
elemwise_concat a (fold_right elemwise_concat nil l).
Proof. intros; reflexivity. Qed. *)

Lemma valuset2bytesets2valuset: forall vs, bytesets2valuset (valuset2bytesets vs) = vs.
Proof. Admitted.

Lemma bytesets2valuset2bytesets: forall bs, bs <> nil -> valuset2bytesets (bytesets2valuset bs) = bs.
Proof. Admitted.

Lemma addr_id: forall A (l: list A) a def, 
a < length l ->
((diskIs (mem_except (list2nmem l) a)) * a |-> (selN l a def))%pred (list2nmem l).
Proof. Admitted.

Lemma firstn1 : forall A (l:list(list A)),
concat(firstn 1 l) = selN l 0 nil.
Proof.
intros.
induction l.
rewrite firstn_nil.
reflexivity.
simpl.
apply app_nil_r.
Qed.

Lemma concat_hom_O: forall A (l: list(list A)) i k,
Forall (fun sublist : list A => length sublist = k) l ->
i<= k -> 
firstn i (concat l) = firstn i (selN l 0 nil).
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite firstn_app_l.
reflexivity.
rewrite Forall_forall in H.
destruct H with (x:= a).
apply in_eq.
apply H0.
Qed.

Lemma bytefile_unified_byte_len: forall ufy fy, 
bytefile_valid ufy fy -> 
length(ByFData fy) <= length(UByFData ufy).
Proof.
intros.
rewrite H.
rewrite firstn_length.
apply Min.le_min_r.
Qed.

Lemma unified_byte_protobyte_len: forall pfy ufy k,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = k) (PByFData pfy) ->
length(UByFData ufy) = length (PByFData pfy) * k.
Proof.
intros.
rewrite H.
apply concat_hom_length with (k:= k).
apply H0.
Qed.

Lemma byte2unifiedbyte: forall ufy fy F a b,
bytefile_valid ufy fy ->
(F * a|-> b)%pred (list2nmem (ByFData fy)) ->
 (F * (arrayN (ptsto (V:= byteset)) (length(ByFData fy)) 
          (skipn (length(ByFData fy)) (UByFData ufy)))
  * a|->b)%pred (list2nmem (UByFData ufy)).
Proof.
unfold bytefile_valid; intros.
pose proof H0.
rewrite H in H0.
apply list2nmem_sel with (def:= byteset0) in H0.
rewrite H0.
rewrite selN_firstn.
apply sep_star_comm.
apply sep_star_assoc.
replace (list2nmem(UByFData ufy))
    with (list2nmem(ByFData fy ++ skipn (length (ByFData fy)) (UByFData ufy))).
apply list2nmem_arrayN_app.
apply sep_star_comm.
rewrite selN_firstn in H0.
rewrite <- H0.
apply H1.
apply list2nmem_inbound in H1.
apply H1.
rewrite H.
rewrite firstn_length.
rewrite Min.min_l. 
rewrite firstn_skipn.
reflexivity.
apply bytefile_unified_byte_len.
apply H.
apply list2nmem_inbound in H1.
apply H1.
Qed.

Lemma unifiedbyte2protobyte: forall pfy ufy a b F k,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = k) (PByFData pfy) ->
k > 0 ->
(F * a|->b)%pred (list2nmem (UByFData ufy)) ->
(diskIs (mem_except (list2nmem (PByFData pfy)) (a/k))  * 
(a/k) |-> get_sublist (UByFData ufy) ((a/k) * k) k)%pred (list2nmem (PByFData pfy)).
Proof.
unfold get_sublist, unified_bytefile_valid.
intros.
rewrite H.
rewrite concat_hom_skipn with (k:= k).
replace (k) with (1 * k) by omega.
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
simpl.
repeat rewrite <- plus_n_O.
apply addr_id.
apply Nat.div_lt_upper_bound.
unfold not; intros.
rewrite H3 in H1; inversion H1.
rewrite Nat.mul_comm.
rewrite <- unified_byte_protobyte_len with (ufy:= ufy).
apply list2nmem_inbound in H2.
apply H2.
apply H.
apply H0.
simpl;  rewrite <- plus_n_O.
apply forall_skipn.
apply H0.
apply H0.
Qed.

Lemma protobyte2block: forall a b f pfy,
proto_bytefile_valid f pfy ->
(diskIs (mem_except (list2nmem (PByFData pfy)) a) * a|->b)%pred (list2nmem (PByFData pfy)) ->
(diskIs (mem_except (list2nmem (BFILE.BFData f)) a) * a|->(bytesets2valuset b))%pred (list2nmem (BFILE.BFData f)).
Proof.
unfold proto_bytefile_valid; intros.
rewrite H in H0.
pose proof H0.
eapply list2nmem_sel in H0.
erewrite selN_map in H0.
rewrite H0.
rewrite valuset2bytesets2valuset.
apply addr_id.
apply list2nmem_inbound in H1.
rewrite map_length in H1.
apply H1.
apply list2nmem_inbound in H1.
rewrite map_length in H1.
apply H1.
Grab Existential Variables.
apply nil.
apply valuset0.
Qed. 

Lemma bytefile_bfile_eq: forall f pfy ufy fy,
proto_bytefile_valid f pfy -> 
unified_bytefile_valid pfy ufy -> 
bytefile_valid ufy fy ->
ByFData fy = firstn (length (ByFData fy)) (flat_map valuset2bytesets (BFILE.BFData f)).
Proof.
unfold proto_bytefile_valid, 
    unified_bytefile_valid, 
    bytefile_valid.
intros.
destruct_lift H.
rewrite flat_map_concat_map.
rewrite <- H.
rewrite <- H0.
apply H1.
Qed.


Lemma div_eq: forall m n k, k < m -> (n * m + k)/m = n.
Proof.
intros.
rewrite Nat.div_add_l.
apply Nat.div_small in H.
rewrite H; symmetry; apply plus_n_O.
unfold not; intros; rewrite H0 in H; inversion H.
Qed.

Lemma mapfst_maplist2byteset: forall A (l: list (list A)) def, map fst (map (list2nelist (singular def)) l) = map (selN' 0 def) l.
Proof.
intros.
rewrite map_map.
unfold selN'.
replace (fun x : list A => fst (list2nelist (singular def) x)) with
  (fun x : list A => selN x 0 def).
reflexivity.
apply functional_extensionality.
intros; symmetry; apply fst_list2byteset.
Qed.

Lemma elemwise_concat_contr: forall A (l: list (list A)) a,
elemwise_concat a (fold_right elemwise_concat nil l) =
(fold_right elemwise_concat nil (a::l)).
Proof. intros. reflexivity. Qed.

Lemma elemwise_a_nil: forall A (a: list A), 
elemwise_concat a nil = make_all_list a.
Proof. destruct a; reflexivity. Qed.


(* Lemma mapselN_fold_elem: forall A  (l: list (list A)) i def, 
map (selN' i def) (fold_right elemwise_concat nil l) =
selN l i nil.
Proof.
induction l; intros.
reflexivity.
destruct i.
simpl.
rewrite elemwise_concat_expand.
rewrite selN_elemwise_concat.


 Admitted. *)

(*Specs*)
Theorem read_first_block_ok: forall lxp bxp ixp inum fms block_off byte_off read_length,
 {< F Fm Fi Fd m0 m flist ilist frees f pfy ufy fy (data: list byteset),
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f pfy ufy fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * block_size + byte_off) data)) ]]] *
           [[ 0 < read_length]] * 
           [[ length data = read_length ]] *
           [[ byte_off + read_length <= block_size]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = (map fst data) ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_first_block lxp ixp inum fms block_off byte_off read_length.
Proof.
unfold read_first_block, rep.
step.
eapply list2nmem_arrayN_bound in H8.
destruct H8.
rewrite H in H7.
inversion H7.
rewrite len_f_fy with (f:=f) (fy:=fy) in H.
apply le2lt_l in H.
apply lt_weaken_l with (m:= byte_off) in H.
apply lt_mult_weaken in H.
apply H.
apply H7.
eapply bytefile_bfile_eq.
apply H12.
apply H11.
apply H10.

pose proof H12.
eapply protobyte2block with (a:= block_off) in H12.
apply H12.


eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes)in H11.
rewrite div_eq in H11.
apply H11.
omega.
unfold proto_bytefile_valid in H.
apply Forall_forall; intros.
rewrite H in H4.
apply in_map_iff in H4.
destruct H4.
inversion H4.
rewrite <- H6.
apply valuset2bytesets_len.
unfold nelist2list.
unfold not; intros.
omega.

eapply byte2unifiedbyte.
apply H10.
rewrite arrayN_isolate with (i:=0) in H8.
rewrite <- plus_n_O in H8.
apply sep_star_assoc in H8.
apply sep_star_comm in H8.
apply sep_star_assoc in H8.
apply sep_star_assoc in H8.
apply H8.
apply H7.

step.
unfold get_sublist.
pose proof H8.
apply arrayN_list2nmem in H8.
rewrite H10 in H8.
rewrite <- skipn_firstn_comm in H8.
rewrite firstn_firstn in H8.
rewrite Min.min_l in H8.
rewrite skipn_firstn_comm in H8.
rewrite H8.
rewrite firstn_length.
rewrite skipn_length.
rewrite Min.min_l.
rewrite H11.
rewrite concat_hom_skipn.
replace (firstn valubytes (concat (skipn block_off (PByFData pfy))))
  with (firstn (1 * valubytes) (concat (skipn block_off (PByFData pfy)))).
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
rewrite <- firstn_map_comm.
rewrite <- plus_n_O.
rewrite Nat.add_comm.
rewrite <- skipn_skipn with (m:= block_off * valubytes).
rewrite concat_hom_skipn.
rewrite <- skipn_map_comm.
rewrite H12.
rewrite concat_map.
erewrite selN_map.
rewrite valuset2bytesets2valuset.

repeat rewrite skipn_map_comm.
repeat rewrite <- skipn_firstn_comm.
rewrite concat_hom_O with (k:= valubytes).
repeat erewrite selN_map.
erewrite skipn_selN.
rewrite <- plus_n_O.
unfold valuset2bytesets.
unfold byteset0.
rewrite mapfst_maplist2byteset with (def:= byte0).
rewrite mapselN_fold_elem.
erewrite selN_map.
unfold nelist2list.
reflexivity.

unfold nelist2list.
simpl.
omega.

rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl.
eapply list2nmem_arrayN_bound in H4.
destruct H4.
rewrite H4 in H7.
inversion H7.
rewrite len_f_fy with (f:=f) (fy:=fy) in H4.
apply le2lt_l in H4.
apply lt_weaken_l with (m:= byte_off) in H4.
apply lt_mult_weaken in H4.
apply H4.
apply H7.
eapply bytefile_bfile_eq.
apply H12.
apply H11.
apply H10.

rewrite map_length.
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl.
eapply list2nmem_arrayN_bound in H4.
destruct H4.
rewrite H4 in H7.
inversion H7.
rewrite len_f_fy with (f:=f) (fy:=fy) in H4.
apply le2lt_l in H4.
apply lt_weaken_l with (m:= byte_off) in H4.
apply lt_mult_weaken in H4.
apply H4.
apply H7.
eapply bytefile_bfile_eq.
apply H12.
apply H11.
apply H10.

rewrite Forall_forall; intros.
rewrite in_map_iff in H6.
repeat destruct H6.
rewrite in_map_iff in H14.
repeat destruct H14.
repeat destruct H6.
rewrite map_length.
apply valuset2bytesets_len.
unfold not; intros.
inversion H6.

apply H5.

eapply list2nmem_arrayN_bound in H4.
destruct H4.
rewrite H4 in H7.
inversion H7.
rewrite len_f_fy with (f:=f) (fy:=fy) in H4.
apply le2lt_l in H4.
apply lt_weaken_l with (m:= byte_off) in H4.
apply lt_mult_weaken in H4.
apply H4.
apply H7.
eapply bytefile_bfile_eq.
apply H12.
apply H11.
apply H10.

rewrite Forall_forall; intros.
rewrite H12 in H6.
rewrite in_map_iff in H6.
repeat destruct H6.
apply valuset2bytesets_len.
unfold not; intros.
inversion H6.

rewrite Forall_forall; intros.
rewrite H12 in H6.
rewrite skipn_map_comm in H6.
rewrite in_map_iff in H6.
repeat destruct H6.
apply valuset2bytesets_len.
unfold not; intros.
inversion H6.

simpl.
rewrite <- plus_n_O.
reflexivity.

rewrite Forall_forall; intros.
rewrite H12 in H6.
rewrite in_map_iff in H6.
repeat destruct H6.
apply valuset2bytesets_len.
unfold not; intros.
inversion H6.

apply list2nmem_arrayN_bound in H4.
destruct H4.
rewrite H4 in H7; inversion H7.
apply Nat.le_add_le_sub_l.
rewrite bytefile_unified_byte_len in H4.
apply H4.
apply H10.

apply list2nmem_arrayN_bound in H4.
destruct H4.
rewrite H4 in H7; inversion H7.
apply H4.

apply byteset0.

Grab Existential Variables.
apply valuset0.
apply valu0.
apply nil.
apply byteset0.
Qed.


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