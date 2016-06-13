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
Definition list2byteset (l: list byte): byteset :=
match l with
| nil => byteset0
| h::t => pushdlist (rev t) (singular h)
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

Fixpoint maxlist l: nat :=
match l with
| nil => 0
| h::t => max h (maxlist t)
end.

Definition full_list (vs: valuset) := (fst vs)::(snd vs).

Definition valuset2bytesets (vs: valuset): list byteset :=
map list2byteset (fold_right elemwise_concat nil (map valu2list (full_list vs))).

Definition bytesets2valuset (bs: list byteset) : valuset.
Proof. Admitted.

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
      


Definition read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks :=
let^ (data) <- (ForN_ (fun i =>
        (pair_args_helper (fun data (_:unit) => (fun Ret =>
        
        let^ (fms, block) <- BFILE.read lxp ixp inum (block_off + i) fms; (* get i'th block *)
        Ret ^(data++(valu2list block))%list (* append its contents *)
        
        )))) 1 num_of_full_blocks
      (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
      (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
Ret ^(fms, data).

(* let^ ((data:list byte)) <- ForN i < num_of_full_blocks 
            Ghost [ lxp ixp inum fms block_off ] 
            Loopvar [ (data:list byte) ] 
            Invariant [[True]] OnCrash [[True]] 
            Begin
            let^ (fms, block) <- BFILE.read lxp ixp inum (block_off +1 + i) fms; (* get i'th block *)
            Ret ^(data++(valu2list block))%list (* append its contents *)
            Rof ^((nil:list byte));
Ret ^(fms, data). *)

Definition middle_blocks_match r fy block_off num_of_full_blocks: Prop :=
let block_size := valubytes in
forall i, (i < num_of_full_blocks * block_size) -> 
selN r i byte0 = fst (selN (ByFData fy) (block_off*block_size +i) byteset0).


Definition read_last_block lxp ixp inum fms block_off read_length :=
let^ (fms, last_block) <- BFILE.read lxp ixp inum block_off fms;   (* get final block *)
let data_last := (get_sublist (valu2list last_block) 0 read_length) in (* get final block data *)
Ret ^(fms, data_last).

Definition last_block_match r fy block_off read_length: Prop :=
let block_size := valubytes in
forall i, (i < read_length) -> selN r i byte0 = 
    fst (selN (ByFData fy) (block_size*block_off + i) byteset0).


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
<<<<<<< 74e098c93555717e6048b981aca9a1d1f96e2415

      (*for loop for reading full blocks in between*)
      let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;

      let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
      let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
      
      (*Read last block*)
      let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
      Ret ^(fms, data_first++data_middle++data_last)%list                  (* append everything and return *)
=======
      If (lt_dec 0 num_of_full_blocks)                        (* if read length > 0 *)
      {  
        (*for loop for reading full blocks in between*)
        let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
        let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        If (lt_dec 0 len_final)
        {
          let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
          rx ^(fms, data_first++data_middle++data_last)%list  
        }
        else
        {
          rx ^(fms, data_first++data_middle)%list  
        }
      }
      else
      {
        let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        If (lt_dec 0 len_final)
        {
          let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
          rx ^(fms, data_first++data_last)%list  
        }
        else
        {
          rx ^(fms, data_first)%list  
        }
      }
>>>>>>> 471ebe210b171289b1d7500fd2f261f038fbf5b7
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

(* Definition write lxp ixp inum off data fms :=
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
      (pair_args_helper (fun data (_:unit) => (fun Ret =>
      
      let^ (ms, bn) <- INODE.getbnum lxp ixp inum (block_off+i) ms;(* get i'th block number *)
      ms <- LOG.write lxp (# bn) (list2valu (get_sublist data (first_write_length + i*block_size) block_size)) ms;
      Ret ^(nil)
      
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
  
    Ret ^(BFILE.mk_memstate al ms).
    
  
  
(* same as write except uses LOG.dwrite *)
Definition dwrite lxp ixp inum off data fms :=
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
      (pair_args_helper (fun data (_:unit) => (fun Ret =>
      
      let^ (ms, bn) <- INODE.getbnum lxp ixp inum (block_off+i) ms;(* get i'th block number *)
      ms <- LOG.dwrite lxp (# bn) (list2valu (get_sublist data (first_write_length + i*block_size) block_size)) ms;
      Ret ^(nil)
      
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
  
    Ret ^(BFILE.mk_memstate al ms).
 *)

(*Same as BFile*)
 Definition getlen lxp ixp inum fms :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    Ret ^(BFILE.mk_memstate al ms, n).

  Definition getattrs lxp ixp inum fms :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getattrs lxp ixp inum ms;
    Ret ^(BFILE.mk_memstate al ms, n).

  Definition setattrs lxp ixp inum a fms :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    ms <- INODE.setattrs lxp ixp inum a ms;
    Ret (BFILE.mk_memstate al ms).

  Definition updattr lxp ixp inum kv fms :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    ms <- INODE.updattr lxp ixp inum kv ms;
    Ret (BFILE.mk_memstate al ms).
    

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

Lemma valuset2bytesets_len: forall vs, 
full_list vs <> nil -> length(valuset2bytesets vs) = valubytes.
Proof.
intros.
unfold valuset2bytesets.
rewrite map_length.
rewrite fold_right_elem_len.
rewrite map_map.
rewrite maxlist_len.
reflexivity.
apply H.
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
unfold full_list; unfold not; intros.
inversion H3.
apply H0.
Qed.
 
Lemma fst_list2byteset: forall l, fst(list2byteset l) =  selN l 0 byte0.
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

Definition selN' {A: Type} i def (l: list A): A :=
selN l i def.

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
unfold full_list; unfold not; intros.
inversion H.
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

Lemma valuset2bytesets2valuset: forall vs, bytesets2valuset (valuset2bytesets vs) = vs.
Proof. Admitted.

Lemma bytesets2valuset2bytesets: forall bs, valuset2bytesets (bytesets2valuset bs) = bs.
Proof. Admitted.

Lemma addr_id: forall A (l: list A) a def, 
a < length l ->
exists F, (F * a |-> (selN l a def))%pred (list2nmem l).
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


Lemma bytefile_unified_byte_len: forall ufy fy, 
bytefile_valid ufy fy -> 
length(ByFData fy) <= length(UByFData ufy).
Proof.
intros.
rewrite H.
rewrite firstn_length.
Search min le.
apply Min.le_min_r.
Qed.

Lemma byte2unifiedbyte: forall ufy fy F a b,
bytefile_valid ufy fy ->
(F * a|-> b)%pred (list2nmem (ByFData fy)) ->
exists F', (F' * a|->b)%pred (list2nmem (UByFData ufy)).
Proof.
intros.
pose proof H0.
rewrite H in H0.
eapply list2nmem_sel in H0.
rewrite H0.
rewrite selN_firstn.
apply addr_id.
apply list2nmem_inbound in H1. 
eapply Nat.lt_le_trans.
apply H1.
apply bytefile_unified_byte_len.
apply H.
apply list2nmem_inbound in H1.
apply H1.
Grab Existential Variables.
apply byteset0. 
Qed.

Lemma unifiedbyte2protobyte: forall pfy ufy a b F,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (PByFData pfy) ->
(F * a|->b)%pred (list2nmem (UByFData ufy)) ->
exists F', (F' * (a/valubytes) |-> get_sublist (UByFData ufy) ((a/valubytes) * valubytes) valubytes)%pred (list2nmem (PByFData pfy)).
Proof.
intros.
pose proof H1.
rewrite H in H1.
rewrite H.
unfold get_sublist.
erewrite concat_hom_skipn.
Search firstn concat.
replace (firstn valubytes (concat (skipn (a / valubytes) (PByFData pfy))))
  with (firstn (1*valubytes) (concat (skipn (a / valubytes) (PByFData pfy)))).
erewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
replace (a / valubytes + 0) with (a / valubytes) by omega. 
apply addr_id.
unfold unified_bytefile_valid in H.
Search firstn 1.
(* HERE *)
Admitted.

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
eapply protobyte2block with (i:= block_off) in H12.
inversion H12.

rewrite H in H4.
apply H10.
Search arrayN sep_star.
erewrite arrayN_isolate with (i:=0)in H8.
pred_apply.
apply sep_star_comm.
eapply ptsto_byte2block with (i:=block_off).
apply H10.
replace (block_off * valubytes + byte_off + 0) 
  with (block_off * valubytes + byte_off) in H8.
apply H8.
omega.
omega.
eapply block_exists.
apply H10.
replace (block_off * valubytes + byte_off + 0) 
  with (block_off * valubytes + byte_off) in H8.
apply H8.
omega.
omega.
omega.
step.
unfold valu2list, get_sublist.
pose proof H10.
eapply ptsto_byte2block with (i:=block_off) in H10.
apply ptsto_valid in H10.
unfold list2nmem in H10; simpl in H10.
erewrite selN_map in H10.
rewrite some_eq in H10.
rewrite H10.
eapply contents_equal.
apply H8.
apply sep_star_comm.
eapply ptsto_byte2block.
apply H4.

eapply arrayN_extract in H8.
replace (block_off * valubytes + byte_off + 0) 
  with (block_off * valubytes + byte_off) in H8.
apply H8.
omega.
omega.
omega.
eapply block_exists.
apply H4.
eapply arrayN_extract in H8.
replace (block_off * valubytes + byte_off + 0) 
  with (block_off * valubytes + byte_off) in H8.
  apply H8.
  omega.
  omega.
  omega.
  omega.
  
eapply list2nmem_arrayN_bound in H8.
destruct H8.
rewrite H6 in H7.
inversion H7.
rewrite len_f_fy with (f:=f) (fy:=fy) in H6.
apply le2lt_l in H6.
apply lt_weaken_l with (m:= byte_off) in H6.
apply lt_mult_weaken in H6.
apply H6.
apply H7.
apply H4.
eapply arrayN_extract with (j:=0)in H8.
apply sep_star_comm.
replace (block_off * valubytes + byte_off + 0) 
  with (block_off * valubytes + byte_off) in H8.
  apply sep_star_comm.
apply H8.
omega.
omega.
omega.

eapply block_exists.
apply H4.
eapply arrayN_extract in H8.
replace (block_off * valubytes + byte_off + 0) 
  with (block_off * valubytes + byte_off) in H8.
  apply H8.
  omega.
  omega.
  omega.
Grab Existential Variables.
apply byteset0.
apply valuset0.
apply valuset0.
apply byteset0.
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

  Definition datasync lxp ixp inum fms :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    ms <- LOG.dsync_vecs lxp (map (@wordToNat _) bns) ms;
    Ret (mk_memstate al ms).

  Definition sync lxp (ixp : INODE.IRecSig.xparams) fms :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    ms <- LOG.sync lxp ms;
    Ret (mk_memstate (negb al) ms).

  Definition pick_balloc A (a : A * A) (flag : bool) :=
    if flag then fst a else snd a.

  Definition grow lxp bxps ixp inum v fms :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, len) <- INODE.getlen lxp ixp inum ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (ms, r) <- BALLOC.alloc lxp (pick_balloc bxps al) ms;
      match r with
      | None => Ret ^(mk_memstate al ms, false)
      | Some bn =>
           let^ (ms, succ) <- INODE.grow lxp (pick_balloc bxps al) ixp inum bn ms;
           If (bool_dec succ true) {
              ms <- LOG.write lxp bn v ms;
              Ret ^(mk_memstate al ms, true)
           } else {
             Ret ^(mk_memstate al ms, false)
           }
      end
    } else {
      Ret ^(mk_memstate al ms, false)
    }.

  Definition shrink lxp bxps ixp inum nr fms :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    ms <- BALLOC.freevec lxp (pick_balloc bxps (negb al)) l ms;
    ms <- INODE.shrink lxp (pick_balloc bxps (negb al)) ixp inum nr ms;
    Ret (mk_memstate al ms).
End*)

End ABYTEFILE.
