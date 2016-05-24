Require Export BFile.
Require Export Bytes.
Require Export Inode.
Require Export Word.
Require Export AsyncDisk.
Require Export String.
Require Export Rec.
Require Export Log.
Require Export Arith.
Require Export Prog.
Require Import BasicProg.
Require Export List.
Require Export Pred PredCrash.
Require Export Mem.

Set Implicit Arguments.


Definition modulo (n m: nat) : nat := n - ((n / m) * m)%nat.

Definition valu_to_list: valu -> list byte.
Proof. Admitted.

Definition get_block_size: valu -> nat.
Proof. Admitted.


Fixpoint read_from_block (l: list byte) (off len: nat) : list byte :=
  match off with
  | O => match len with 
          | O => nil
          | S len' => match l with
                      | nil => nil
                      | b::l' => b::(read_from_block l' O len')
                      end
          end
  | S off'=> match l with
              | nil => nil
              | b::l' => (read_from_block l' off' len)
              end
  end.
  
(*Ugly but at least compiling*)

Definition read_bytes {T} lxp ixp inum (off len:nat) fms rx : prog T :=
If (lt_dec 0 len) {                                           (* if read length > 0 *)
  let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen) {                                      (* if offset is inside file *)
    If(le_dec (off+len) flen) {                               (* if you can read the whole length *)
      let^ (fms, first_block) <- BFILE.read lxp ixp inum off fms;   (* get first block *)
      let block_size := (get_block_size first_block) in             (* get block size *)
      let relative_off := (modulo off block_size) in          (* calculate block offset *)
      If(le_dec (relative_off + len) block_size) {            (* if whole data is in this block *)
        let data := (read_from_block                          (* read the data and return as list byte *)
        (valu_to_list first_block) relative_off len) in
        rx ^(fms, data)
      } else {                                                (* If data is in more than one block *)
        let data_init := (read_from_block                     (* read as much as you can from this block *)
        (valu_to_list first_block) relative_off         
         (block_size - relative_off)) in
        let off_remain := (off + (block_size - relative_off)) in  (* offset of remaining part *)
        let len_remain := (len - (block_size - relative_off)) in  (* length of remaining part *)
        let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
        
        (* for loop notation can't find implicit arguments*)
        (*let^ (data) <- ForN i <  num_of_full_blocks
        Ghost [ len_remain ]
        Loopvar [data]
        Continuation lrx
        Invariant
         (fun _ => True)
        OnCrash
         (fun _ => True)
        Begin
          let^ (fms, block) <- BFILE.read lxp ixp inum (off_remain + i*block_size) fms;
          lrx ^(data++(read_from_block (valu_to_list block) 0 block_size))
        Rof ^(data_init);*)
        
        (*for loop for reading those full blocks *)
        let^ (data) <- (ForN_ (fun i =>
          (pair_args_helper (fun data (_:unit) => (fun lrx => 
          
          let^ (fms, block) <- BFILE.read lxp ixp inum (off_remain + i*block_size) fms; (* get i'th block *)
          lrx ^(data++(read_from_block (valu_to_list block) 0 block_size)) (* append its contents *)
          
          )))) 0 num_of_full_blocks
        (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
        (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
        
        let off_final := (off_remain + num_of_full_blocks * block_size) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        let^ (fms, last_block) <- BFILE.read lxp ixp inum off_remain fms;   (* get final block *)
        let data_final := (read_from_block (valu_to_list last_block) 0 len_final) in (* get final block data *)
        rx ^(fms, data_init++data++data_final)                  (* append everything and return *)
        }
      } else {                                                  (* If you cannot read the whole length *)
        let len:= (flen - off) in                               (* set length to remaining length of file *)
        let^ (fms, first_block) <- BFILE.read lxp ixp inum off fms;   (* get first block *)
        let block_size := (get_block_size first_block) in             (* get block size *)
        let relative_off := (modulo off block_size) in          (* calculate block offset *)
        If(le_dec (relative_off + len) block_size) {            (* if whole data is in this block *)
          let data := (read_from_block                          (* read the data and return as list byte *)
          (valu_to_list first_block) relative_off len) in
          rx ^(fms, data)
        } else {                                                (* If data is in more than one block *)
            let data_init := (read_from_block                     (* read as much as you can from this block *)
            (valu_to_list first_block) relative_off  
             (block_size - relative_off)) in
            let off_remain := (off + (block_size - relative_off)) in  (* offset of remaining part *)
            let len_remain := (len - (block_size - relative_off)) in  (* length of remaining part *)
            let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
            
            (* for loop notation can't find implicit arguments*)
            (*let^ (data) <- ForN i <  num_of_full_blocks 
            Ghost [ len_remain ]
            Loopvar [data]
            Continuation lrx
            Invariant
             (fun _ => True)
            OnCrash
             (fun _ => True)
            Begin
              let^ (fms, block) <- BFILE.read lxp ixp inum (off_remain + i*block_size) fms;
              lrx ^(data++(read_from_block (valu_to_list block) 0 block_size))
            Rof ^(data_init);*)
            
            (*for loop for reading those full blocks *)
            let^ (data) <- (ForN_ (fun i =>
              (pair_args_helper (fun data (_:unit) => (fun lrx => 
              
              let^ (fms, block) <- BFILE.read lxp ixp inum (off_remain + i*block_size) fms; (* get i'th block *)
              lrx ^(data++(read_from_block (valu_to_list block) 0 block_size)) (* append its contents *)
              
              )))) 0 num_of_full_blocks
            (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
            (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
            
            let off_final := (off_remain + num_of_full_blocks * block_size) in (* offset of final block *)
            let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
            let^ (fms, last_block) <- BFILE.read lxp ixp inum off_remain fms;   (* get final block *)
            let data_final := (read_from_block (valu_to_list last_block) 0 len_final) in (* get final block data *)
            rx ^(fms, data_init++data++data_final)                  (* append everything and return *)
            }
       }
  } else {                                                    (* if offset is not valid, return nil *)
    rx ^(fms, nil)
  }
} else {                                                      (* if read length is not valid, return nil *)
  rx ^(fms, nil)
}.




(**
(* It says syntax error for some reason. I couldn't find why *)
Fixpoint read_bytes {T} lxp ixp inum (off len:nat) fms rx : prog T :=
If (lt_dec 0 len) {                                           (* if read length > 0 *)
  let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen) {                                      (* if offset is inside file *)
    If(le_dec (off+len) flen) {                               (* if you can read the whole length *)
      let^ (fms, block) <- BFILE.read lxp ixp inum off fms;   (* get first block *)
      let block_size := (get_block_size block) in             (* get block size *)
      let relative_off := (modulo off block_size) in          (* calculate block offset *)
      If(le_dec (relative_off + len) block_size) {            (* if whole data is in this block *)
        let data := (read_from_block                          (* read the data and return as list byte *)
        (valu_to_list (fst block)) relative_off len) in
        rx ^(fms, data)
      } else {                                                (* If data is in more than one block *)
        let data:= (read_from_block                           (* read as much as you can from this block *)
        (valu_to_list (fst block)) relative_off  
         (block_size - relative_off)) in
        let^ (fms, data_remaining) <- read_bytes lxp ixp inum (* read remainder from next blocks *)
          (off + (block_size - relative_off)) 
          (len - (block_size - relative_off)) fms;
        rx ^(fms, (data++data_remaining))                     (* concatenate the lists and return *)
      }
    } else {                                                  (* If you cannot read the whole length *)
        let^ (fms, data) <- read_bytes lxp ixp inum           (* read as much as you can and return it *)
            off (flen - off) fms;
        rx ^(fms, data)
    }
  } else {                                                    (* if offset is not valid, return nil *)
    rx ^(fms, nil)
  }
} else {                                                      (* if read length is not valid, return nil *)
  rx ^(fms, nil)
}.
**)