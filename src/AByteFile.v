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


(* It says syntax error for some reason. I couldn't find why *)
Fixpoint read_bytes {T} lxp ixp inum (off:nat) len fms rx : prog T :=
If (lt_dec 0 len) {                                           (* if read length > 0 *)
  let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen) {                                      (* if offset is inside file *)
    If(le_dec (off+len) flen) {                               (* if you can read the whole length *)
      let^ (fms, block) <- BFILE.read lxp ixp inum off fms;   (* get first block *)
      let block_size := (get_block_size block) in             (* get block size *)
      let relative_off := (modulo off block_size) in          (* calculate block offset *)
      If(le_dec (relative_off + len) block_size) {            (* if whole data is in this block *)
        let data := (read_from_block                          (* read the data and return as list byte *)
        (valu_to_list block) relative_off len) in
        rx ^(fms, data::nil)
      } else {                                                (* If data is in more tahn one block *)
        let data:= (read_from_block                           (* read as much as you can from this block *)
        (valu_to_list block) relative_off  
         (block_size - relative_off)) in
        let^ (fms, data_remaining) <- read_bytes lxp ixp inum (* read remainder from next blocks *)
          (off + (block_size - relative_off)) 
          (len - (block_size - relative_off)) fms;
        rx ^(fms, (data::data_remaining))                     (* concatenate the lists and return *)
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
