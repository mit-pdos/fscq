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

Set Implicit Arguments.

Module ABYTEFILE.

Record byte_file := mk_byte_file {
  ByFData : list valuset;
  ByFAttr : INODE.iattr
}.

Definition modulo (n m: nat) : nat := n - ((n / m) * m)%nat.

Definition valu_to_list: valu -> list byte.
Proof. Admitted.

Definition get_block_size: valu -> nat.
Proof. Admitted.


Fixpoint get_sublist {A:Type}(l: list A) (off len: nat) : list A :=
  match off with
  | O => match len with 
          | O => nil
          | S len' => match l with
                      | nil => nil
                      | b::l' => b::(get_sublist l' O len')
                      end
          end
  | S off'=> match l with
              | nil => nil
              | b::l' => (get_sublist l' off' len)
              end
  end.

Definition full_read_ok r block_size block_off first_read_length num_of_full_reads m : Prop :=
forall (i:nat), ((num_of_full_reads < i + 1) \/ (*[1]i is out of range OR*)
  (*[2]i'th block you read matches its contents*)
   (exists bl:valuset, (( exists F',(F' * (block_off +i)|-> bl)%pred (list2nmem m)) /\ (*[2.1]Block bl is in the address (block_off +1 + i) AND*)
  (get_sublist r (first_read_length + (i-1)*block_size) block_size (*[2.2]What is read matches the content*)
      = valu_to_list (fst bl))))).

Definition read_bytes {T} lxp ixp inum (off len:nat) fms rx : prog T :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                    
      let^ (fms, block0) <- BFILE.read lxp ixp inum 0 fms;        (* get block 0*)
      let len := min len (flen - off) in
      let block_size := get_block_size block0 in            (* get block size *)
      let block_off := off / block_size in              (* calculate block offset *)
      let byte_off := modulo off block_size in          (* calculate byte offset *)
      let first_read_length := min (block_size - byte_off) len in (*# of bytes that will be read from first block*)
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist                     (* read as much as you can from this block *)
      (valu_to_list first_block) byte_off (block_size - byte_off)) in
      let len_remain := (len - first_read_length) in  (* length of remaining part *)
      let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
        
      (*for loop for reading those full blocks *)
      let^ (data) <- (ForN_ (fun i =>
        (pair_args_helper (fun data (_:unit) => (fun lrx => 
        
        let^ (fms, block) <- BFILE.read lxp ixp inum (block_off + i) fms; (* get i'th block *)
        lrx ^(data++(valu_to_list block))%list (* append its contents *)
        
        )))) 1 num_of_full_blocks
      (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
      (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
      
      let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
      let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
      let^ (fms, last_block) <- BFILE.read lxp ixp inum off_final fms;   (* get final block *)
      let data_final := (get_sublist (valu_to_list last_block) 0 len_final) in (* get final block data *)
      rx ^(fms, data_init++data++data_final)%list                  (* append everything and return *)
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

Theorem read_bytes_ok : forall lxp bxp ixp inum off len ms,
    {< F Fm Fi Fd m0 m flist ilist frees f vs ve,
    PRE:hm
        let block_size := (get_block_size (fst vs)) in
        let block_off := off / block_size in
        let byte_off := modulo off block_size in
        let first_read_length := min (block_size - byte_off) len in
        let num_of_full_reads := (len - first_read_length) / block_size in
        let last_read_length := len - first_read_length - num_of_full_reads * block_size in
        let file_length := length (BFILE.BFData f) in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFILE.BFData f) ::: (Fd * block_off |-> vs * (((off+len)/block_size)|-> ve \/ [[file_length < off + len]]) )]]]*
           [[ off < file_length ]]*
           [[ 0 < len ]]
    POST:hm' RET:^(ms', r)
          let block_size := (get_block_size (fst vs)) in
          let block_off := off / block_size in
          let byte_off := modulo off block_size in
          let first_read_length := min (block_size - byte_off) len in
          let num_of_full_reads := (len - first_read_length) / block_size in
          let last_read_length := len - first_read_length - num_of_full_reads * block_size in
          let file_length := length (BFILE.BFData f) in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm' *
           [[  
           (*[1]You read correctly*)
           ((off + len <= file_length /\        (*[1.1]You read the full length OR*)
               
               (*[1.1.1]You read the first block correctly AND*)
               (get_sublist r 0 first_read_length = get_sublist (valu_to_list (fst vs)) byte_off first_read_length ) /\ 
               
               (*[1.1.2]You read all middle blocks correctly AND*)
              full_read_ok r block_size block_off first_read_length num_of_full_reads m /\
               
               (*[1.1.3]You read the last block correctly*)
               (get_sublist r (len - last_read_length) last_read_length 
                  = get_sublist (valu_to_list (fst ve)) 0 last_read_length))
                  
             \/ (file_length < off + len /\ (*[1.2]You read as much as possible*)
             
                (*[1.2.1]You read the first block correctly AND*)
                (get_sublist r 0 first_read_length = get_sublist (valu_to_list (fst vs)) byte_off first_read_length ) /\
                
                (*[1.2.2]You read remaining blocks correctly*)
                full_read_ok r block_size block_off first_read_length ((file_length - off - first_read_length)/block_size) m))

              (*[2]Memory contents didn't change*)
              /\ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm'
    >} read_bytes lxp ixp inum off len ms.

End ABYTEFILE.