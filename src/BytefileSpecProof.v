Require Import Word.
Require Import SepAuto.
Require Import BasicProg Prog ProgMonad.
Require Import Hoare.
Require Import GenSepN.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import ListPred.
Require Import AsyncDisk.
Require Import Inode.
Require Import DiskSet.
Require Import BFile.
Require Import Bytes.
Require Import VBConv.
Require Import Fscq.Hashmap.
Require Import Errno.
Require Import Pred PredCrash.
Require Import AByteFile.

Set Implicit Arguments.


Definition getattrs := BFILE.getattrs.
Definition setattrs := BFILE.setattrs.
Definition updattr := BFILE.updattr.
Definition datasync := BFILE.datasync.
Definition sync := BFILE.sync.
Definition sync_noop := BFILE.sync_noop.



(*Specs*)


Definition getlen lxp ixp inum fms:=
    let^ (ms, attr) <- BFILE.getattrs lxp ixp inum fms;
    Ret ^(ms, #(INODE.ABytes attr)).

Theorem getlen_ok : forall lxp bxp ixp inum fms,
{< F Fm Fi m0 m flist ilist frees f fy,
PRE:hm
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
       [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
       [[[ flist ::: (Fi * inum |-> f) ]]] *
       rep f fy
POST:hm' RET:^(fms',r)
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
       [[ r = length (ByFData fy)]] *
       [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
CRASH:hm'  exists fms',
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
>} getlen lxp ixp inum fms.
Proof. Admitted. 

Hint Extern 1 ({{_}} Bind (getlen _ _ _ _) _) => apply getlen_ok : prog.

(* -------------------------------------------------------------------------------- *)

Definition dwrite_to_block lxp ixp inum fms block_off byte_off data :=
    let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get the block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    fms <- BFILE.dwrite lxp ixp inum block_off block_write fms;
  Ret (fms).


Definition dwrite_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash F Fm Fi Ff bxp ilist frees old_data fy]
        Loopvar [ms']
        Invariant 
        exists ds f' fy' flist,
          LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL ms') hm *
          [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f') ]]] *
          rep f' fy' *
          [[[ (ByFData fy')::: (Ff * arrayN ptsto_subset_b ((block_off + i) * valubytes) (skipn (i * valubytes) old_data) *
          			arrayN ptsto_subset_b (block_off * valubytes) (merge_bs (firstn (i*valubytes) data) (firstn (i*valubytes) old_data)))]]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]] *
          [[ subset_invariant_bs Ff ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block lxp ixp inum ms' (block_off + i) 0 write_data;
          Ret ^(fms')) Rof ^(fms);
  Ret (fst ms).


Definition dwrite lxp ixp inum fms off data :=
  let write_length := length data in
  let block_off := off / valubytes in
  let byte_off := off mod valubytes in
  If (lt_dec 0 write_length)                        (* if read length > 0 *)
  { 
      let^ (ms0, file_length) <- getlen lxp ixp inum fms;
      If (lt_dec off file_length)
      {
          If(le_dec write_length (valubytes - byte_off))
          {
              ms1 <- dwrite_to_block lxp ixp inum ms0 block_off byte_off data;
              Ret (ms1)
          }
          else
          {
              let first_write_length := valubytes - byte_off in
              let first_data := firstn first_write_length data in
              
              ms1 <- dwrite_to_block lxp ixp inum ms0 block_off byte_off first_data;
              
              let block_off := block_off + 1 in
              let remaining_data := skipn first_write_length data in
              let write_length := write_length - first_write_length in
              let num_of_full_blocks := write_length / valubytes in
              If(lt_dec 0 num_of_full_blocks)
              {
                  let middle_data := firstn (num_of_full_blocks * valubytes) remaining_data in
                  ms2 <- dwrite_middle_blocks lxp ixp inum ms1 block_off num_of_full_blocks middle_data;
                  
                  let block_off := block_off + num_of_full_blocks in
                  let remaining_data := skipn (num_of_full_blocks * valubytes) remaining_data in
                  let write_length := write_length - (num_of_full_blocks * valubytes) in
                  If (lt_dec 0 write_length)
                  {
                      ms3 <- dwrite_to_block lxp ixp inum ms2 block_off 0 remaining_data;
                      Ret (ms3)
                  }
                  else
                  {
                      Ret (ms2)
                  }
              }
              else
              {
                  If (lt_dec 0 write_length)
                  {
                      ms2 <- dwrite_to_block lxp ixp inum ms1 block_off 0 remaining_data;
                      Ret (ms2)
                  }
                  else
                  {
                      Ret (ms1)
                  }
              }
           }
      }
      else
      {
        Ret (ms0)
      }
  }
  else
  {
    Ret (fms)
  }.

Theorem dwrite_ok : forall lxp bxp ixp inum off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b off old_data)]]] *
           [[ length old_data = length data]] *
           [[ sync_invariant F ]] *
           [[ subset_invariant_bs Fd ]]
     POST:hm' RET:fms'  exists flist' fy' f' ds',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b off (merge_bs data old_data))]]] *
           [[ ByFAttr fy = ByFAttr fy' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'  LOG.intact lxp F ds hm'
    >}  dwrite lxp ixp inum fms off data.
    
Proof. Admitted.

Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _ _) _) => apply dwrite_ok : prog.

Definition read_from_block lxp ixp inum fms block_off byte_off read_length :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(fms, data_init).
     

Definition read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash F Fd m0 m fy data']
        Loopvar [(ms' : BFILE.memstate) (data : list byte)]
        Invariant 
        LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm *
        [[[ (ByFData fy) ::: Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) data']]] *
        [[ data = map fst (firstn (i * valubytes) data')]] *
        [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let^((fms' : BFILE.memstate), (list : list byte)) <- 
                read_from_block lxp ixp inum ms' (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list)) Rof ^(fms, nil);
Ret ^(ms, data).

Definition read lxp ixp inum off len fms :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (fms, flen) <- getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                    
      
      let block_size := valubytes in            (* get block size *)
      let block_off := off / block_size in              (* calculate block offset *)
      let byte_off := off mod block_size in          (* calculate byte offset *)
      If (lt_dec len (flen - off))
      {
        If (lt_dec (block_size - byte_off) len)
        {
          let first_read_length := (block_size - byte_off) in (*# of bytes that will be read from first block*)
          let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
          
          let block_off := S block_off in
          let len_remain := (len - first_read_length) in  (* length of remaining part *)
          let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
          If (lt_dec 0 num_of_full_blocks)
          {
            let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
          
            let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
            let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
            If(lt_dec 0 len_final)
            {
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
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
            let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
            Ret ^(fms, data_first++data_last)%list
          }
        }
        else
        {
           let first_read_length := len in (*# of bytes that will be read from first block*)
           let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
           Ret ^(fms, data_first)
        }
      }
      else
      {
        let len := (flen - off) in
        If (lt_dec (block_size - byte_off) len)
        {
            let first_read_length := (block_size - byte_off) in 
            let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length; 
          
            let block_off := S block_off in
            let len_remain := (len - first_read_length) in  (* length of remaining part *)
            let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
            If (lt_dec 0 num_of_full_blocks)
            {
              let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
            
              let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
              let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
              If(lt_dec 0 len_final)
              {
                let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
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
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
              Ret ^(fms, data_first++data_last)%list

            }
        }
        else
        {
           let first_read_length := len in (*# of bytes that will be read from first block*)
           let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   
           Ret ^(fms, data_first)
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



Theorem read_ok : forall lxp bxp ixp inum off len fms,
    {< F Fm Fi Fd m0 m flist ilist frees f fy data,
    PRE:hm
        let file_length := (# (INODE.ABytes (ByFAttr fy))) in
        let block_size := valubytes in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) off data)) ]]] *
           [[ length data  = min len (file_length - off)]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = map fst data]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read lxp ixp inum off len fms.
Proof. Admitted.

Hint Extern 1 ({{_}} Bind (read _ _ _ _ _ _) _) => apply read_ok : prog.


Definition grow_in_block lxp ixp inum fms n :=
	If (lt_dec 0 n)
	{
		let^ (ms1, bylen) <- getlen lxp ixp inum fms;
		let^ (ms2, data) <- read lxp ixp inum (bylen / valubytes * valubytes) (bylen mod valubytes) ms1;
		ms3 <- BFILE.dwrite lxp ixp inum (bylen / valubytes) 
							      (list2valu (data ++ (list_zero_pad nil (valubytes - (bylen mod valubytes))))) ms2;
		ms4 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms3; 
		Ret (ms4)
	}
	else
	{
		Ret (fms)
	}.
     

Theorem grow_in_block_ok : forall lxp bxp ixp inum ms n,
    {< F Fm Fi Fd m0 flist ilist frees f fy,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m0!!) (BFILE.MSLL ms) hm *
           [[[ m0!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: Fd]]] *
           [[ length (ByFData fy) mod valubytes > 0 ]] *
           [[ n + length (ByFData fy) mod valubytes <= valubytes ]] *
           [[ sync_invariant F ]] *
           [[ subset_invariant_bs Fd ]] *
           [[ goodSize addrlen (length (ByFData fy) + n) ]]
    POST:hm' RET:(ms') [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]] *
			(exists m0' m' flist' ilist' frees' f' fy' garb,
           LOG.rep lxp F (LOG.ActiveTxn m0' m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy'  *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:= byteset))(length (ByFData fy)) (merge_bs (list_zero_pad nil n) garb)) ]]] *
           [[ length garb = n ]] *
           [[ ByFAttr fy' = ($ (length (ByFData fy) + n), snd (ByFAttr fy)) ]])
    XCRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow_in_block lxp ixp inum ms n.
Proof. Admitted.

Hint Extern 1 ({{_}} Bind (grow_in_block _ _ _ _ _) _) => apply grow_in_block_ok : prog.




Definition grow lxp bxp ixp inum fms n :=
	If (lt_dec 0 n)
	{
		let^ (ms1, bylen) <- getlen lxp ixp inum fms;
		let fir_n := valubytes - bylen mod valubytes in
		

	  If (lt_dec 0 (bylen mod valubytes))
	  {
	    If (lt_dec n fir_n)
	    {
	      ms2 <- grow_in_block lxp ixp inum ms1 n;
	      ms3 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms2;
		    Ret ^(ms3, OK tt)
	    }
	    else
	    {
		    ms2 <- grow_in_block lxp ixp inum ms1 fir_n;
		    let rem_n := n - fir_n in
		    let mid_n := rem_n / valubytes in
		    If (lt_dec 0 mid_n)
		    {
			    let^ (ms3, ret) <- BFILE.grown lxp bxp ixp inum (valu0_pad mid_n) ms2;
			    let las_n := rem_n mod valubytes in
			    match ret with
			    | Err e => Ret ^(fms, ret) 
			    | OK _ => If(lt_dec 0 las_n)
								    {
									    let^ (ms4, ret2)<- BFILE.grow lxp bxp ixp inum valu0 ms3;
									    match ret2 with
									    | Err e => Ret ^(fms, ret2)
									    | OK _ => ms5 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms4;
														    Ret ^(ms5, ret2)
									    end
								    }
								    else
								    {
									    ms4 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms3;
									    Ret ^(ms4, ret)
								    }
			    end
		    }
		    else
		    {
			    let las_n := rem_n mod valubytes in
			    If(lt_dec 0 las_n)
			    {
				    let^ (ms3, ret)<- BFILE.grow lxp bxp ixp inum valu0 ms2;
				    match ret with
				    | Err e => Ret ^(fms, ret)
				    | OK _ => ms4 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms3;
									    Ret ^(ms4, ret)
				    end
			    }
			    else
			    {
				    ms3 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms2;
				    Ret ^(ms3, OK tt)
			    }
		    }
	    }
	  }
	  else
	  {
		  let rem_n := n in
		  let mid_n := rem_n / valubytes in
		  If (lt_dec 0 mid_n)
		  {
			  let^ (ms2, ret) <- BFILE.grown lxp bxp ixp inum (valu0_pad mid_n) ms1;
			  let las_n := rem_n mod valubytes in
			  match ret with
			  | Err e => Ret ^(fms, ret) 
			  | OK _ => If(lt_dec 0 las_n)
								  {
									  let^ (ms3, ret2)<- BFILE.grow lxp bxp ixp inum valu0 ms2;
									  match ret2 with
									  | Err e => Ret ^(fms, ret2)
									  | OK _ => ms4 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms3;
														  Ret ^(ms4, ret2)
									  end
								  }
								  else
								  {
									  ms3 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms2;
									  Ret ^(ms3, ret)
								  }
			  end
		  }
		  else
		  {
			  let las_n := rem_n mod valubytes in
			  If(lt_dec 0 las_n)
			  {
				  let^ (ms2, ret)<- BFILE.grow lxp bxp ixp inum valu0 ms1;
				  match ret with
				  | Err e => Ret ^(fms, ret)
				  | OK _ => ms3 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms2;
									  Ret ^(ms3, ret)
				  end
			  }
			  else
			  {
				  ms2 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen + n)) ms1;
				  Ret ^(ms2, OK tt)
			  }
		  }
	  }
	  
	}
	else
	{
		Ret ^(fms, OK tt)
	}.

	
	Definition grow_ok: forall lxp bxp ixp inum ms n,
    {< F Fm Fi Fd m0 flist ilist frees f fy,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m0!!) (BFILE.MSLL ms) hm *
           [[[ m0!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: Fd]]] *
           [[ goodSize addrlen (length (ByFData fy) + n) ]] *
           [[ sync_invariant F ]] *
           [[subset_invariant_bs Fd ]]
    POST:hm' RET:^(ms', r) 
    	[[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]] * (exists m0' m' e, 
    	 LOG.rep lxp F (LOG.ActiveTxn m0' m') (BFILE.MSLL ms') hm' *
    	([[ r = Err e ]] \/ 
			[[ r = OK tt ]] *(exists flist' ilist' frees' f' fy' garb,
           [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy'  *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:= byteset)) (length (ByFData fy)) (merge_bs (list_zero_pad nil n) garb)) ]]] *
           [[ length garb = min n (mod_minus_curb (length (ByFData fy)) valubytes) ]] *
           [[ ByFAttr fy' = ($ (length (ByFData fy) + n), snd (ByFAttr fy)) ]] *
           [[ goodSize addrlen (length (ByFData fy')) ]])))
    XCRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow lxp bxp ixp inum ms n.
    
Proof.
	pose proof valubytes_ne_O as Hv.
	pose proof valubytes_ge_O as Hv'.
	unfold grow, rep.
	step. 
	prestep.
	norm.
	unfold stars, rep; cancel; eauto.
	intuition; eauto.
	step.
	prestep.
	norm.
	unfold stars, rep; cancel; eauto.
	intuition. eauto.
	prestep.
	norm.
	unfold stars, rep; cancel; eauto.
	intuition; eauto.
	unfold rep; step.
	step.
	or_r.
	cancel; eauto.
	rewrite <- H38; auto.
	rewrite H26; reflexivity.
	rewrite Min.min_l.
	reflexivity.
	unfold mod_minus_curb; simpl.
	destruct (length (ByFData fy) mod valubytes); omega.
	rewrite <- H37; rewrite H26; simpl.
	rewrite wordToNat_natToWord_idempotent'; auto.
	
	Focus 2.
	cancel.
	xcrash.
	
	Focus 2.
	prestep.
	norm.
	unfold stars, rep; cancel; eauto.
	intuition; eauto.
	
	rewrite mp_2_3_cancel. 
	apply le_n.
	
	apply mod_upper_bound_le'; auto. 
	eapply goodSize_trans.
	2: apply H7.
	apply plus_le_compat_l.
	apply mod_ne_0 in H22; auto.
	omega.
	step.
	unfold rep; step.
	apply diskIs_id.
	step.
	step.
	step.
	step.
	or_r.
	cancel.

	instantiate (1:= (mk_proto_bytefile ((PByFData pfy0) ++ (map valuset2bytesets (synced_list
                     (valu0_pad
                        ((n - (valubytes - length (ByFData fy) mod valubytes)) /
                         valubytes)))) ++ (valuset2bytesets (valu0, nil))::nil))).
	unfold proto_bytefile_valid; simpl.
	repeat rewrite map_app.
	simpl.
	rewrite H12.
	repeat rewrite app_assoc; reflexivity.
	
	instantiate (1:= mk_unified_bytefile ((UByFData ufy0) ++ concat(map valuset2bytesets
                (synced_list
                   (valu0_pad
                      ((n -
                        (valubytes - length (ByFData fy) mod valubytes)) /
                       valubytes))) ++
              valuset2bytesets (valu0, nil) :: nil))).
  unfold unified_bytefile_valid; simpl.
  repeat rewrite concat_app.
  rewrite H38; reflexivity.
  
  instantiate (1:= mk_bytefile ((ByFData fy') ++ firstn (n - (valubytes - length (ByFData fy) mod valubytes)) (concat
                (map valuset2bytesets
                   (synced_list
                      (valu0_pad
                         ((n -
                           (valubytes -
                            length (ByFData fy) mod valubytes)) /
                          valubytes))) ++
                 valuset2bytesets (valu0, nil) :: nil))) ($ (length (ByFData fy) + n), snd (ByFAttr fy))).
 	unfold bytefile_valid; simpl.
 	repeat rewrite app_length.
 	rewrite firstn_length_l.
 	rewrite firstn_app_le.
 	rewrite H37.
	replace (length (ByFData fy')) with (length (UByFData ufy0)).
	rewrite firstn_exact.
	rewrite pm_1_3_cancel.
	reflexivity.
	
	symmetry; eapply unified_bytefile_bytefile_length_eq; eauto.
	
  eapply bytefile_bfile_minus_lt; eauto.
  eapply bytefile_mod_0; eauto.

	erewrite unified_bytefile_bytefile_length_eq; eauto.
	apply le_plus_l.
	eapply bytefile_bfile_minus_lt; eauto.
  eapply bytefile_mod_0; eauto.
	
	rewrite concat_hom_length with (k:= valubytes).
	rewrite app_length.
	rewrite map_length.
	rewrite synced_list_length.
	rewrite valu0_pad_length.
	simpl.
	rewrite Nat.mul_add_distr_r.
	simpl; rewrite <- plus_n_O.
	apply le_div_mult_add; auto.
  
  
  apply Forall_map_v_app.
	simpl.
	rewrite <- H36; rewrite H26; simpl.
	reflexivity.
	
	simpl.
	repeat rewrite app_length.
	rewrite firstn_length_l.
	rewrite <- H35; rewrite H26; simpl.
	repeat rewrite wordToNat_natToWord_idempotent'.
	rewrite <- Nat.add_assoc.
	rewrite <- le_plus_minus.
	reflexivity.
	
  eapply mod_lt_0_le; eauto.
	eapply goodSize_trans.
	2: apply H7.
	apply plus_le_compat_l.
	eapply mod_lt_0_le; eauto.
	auto.
	
	rewrite concat_hom_length with (k:= valubytes).
	rewrite app_length.
	rewrite map_length.
	rewrite synced_list_length.
	rewrite valu0_pad_length.
	simpl.
	rewrite Nat.mul_add_distr_r.
	simpl; rewrite <- plus_n_O.
	apply le_div_mult_add; auto.
  
  apply Forall_map_v_app.
	
	simpl.
	repeat rewrite app_length.
	rewrite firstn_length_l.
	rewrite synced_list_length.
	rewrite valu0_pad_length.
	simpl.
	rewrite pm_2_3_cancel.
	rewrite Nat.mul_add_distr_r.
	erewrite bfile_bytefile_length_eq; eauto.
	apply plus_lt_compat_l.
	apply Rounding.div_mul_lt; auto.
	instantiate (1:= length (ByFData fy')).
	replace ( length (ByFData fy') mod valubytes) with 0.
	apply minus_n_O.
	symmetry; eapply bytefile_mod_0; eauto.
	eapply bytefile_bfile_minus_lt; eauto.

	rewrite concat_hom_length with (k:= valubytes).
	rewrite app_length.
	rewrite map_length.
	rewrite synced_list_length.
	rewrite valu0_pad_length.
	simpl.
	rewrite Nat.mul_add_distr_r.
	simpl; rewrite <- plus_n_O.
	apply le_div_mult_add; auto.

  apply Forall_map_v_app.
	
	simpl.
  rewrite arrayN_split with (i := (valubytes - length (ByFData fy) mod valubytes)).
  apply sep_star_assoc.
  apply list2nmem_arrayN_app_general; auto.
  rewrite merge_bs_firstn_comm.
	instantiate(1:= garb). rewrite <- H27.
	rewrite firstn_exact; eauto.
	rewrite list_zero_pad_nil_firstn.
	rewrite Nat.min_l.
	rewrite H27; auto.
	rewrite H27; eapply mod_lt_0_le; eauto.

	rewrite <- H35; rewrite H26; simpl.
	rewrite wordToNat_natToWord_idempotent'.
	reflexivity.
	eapply goodSize_trans.
	2: apply H7.
	apply plus_le_compat_l.
	eapply mod_lt_0_le; eauto.
  
  rewrite merge_bs_skipn_comm.
  rewrite <- H27.
  replace (skipn (length garb) garb) with (nil:list byteset).
  rewrite concat_app.
  simpl.
  rewrite app_nil_r.
  
  rewrite list_zero_pad_nil_skipn.
  rewrite firstn_app_le.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  rewrite synced_list_length.
  rewrite valu0_pad_length.
  rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto.
  
  Lemma valuset2bytesets_synced_list_valu0_pad_merge_bs_zero_pad_nil:
  valuset2bytesets (valu0, nil) = merge_bs (list_zero_pad nil valubytes) nil.
  Proof.
  unfold valuset2bytesets; simpl.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  simpl.
  
  Lemma valu2list_valu0:
  valu2list valu0 = list_zero_pad nil valubytes.
  Proof.
    unfold valu0; simpl.
    unfold valu2list.
    rewrite bytes2valu2bytes.
    unfold bsplit_list.
    rewrite valubytes_is; simpl.
  
  
  unfold combine, merge_bs, valuset2bytesets; simpl.
  
  rewrite repeat_map.
    
    
  
  rewrite list_zero_pad_nil_iff.
	
	
	
	
	
	
	
	Admitted.
	
	
	