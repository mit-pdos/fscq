package getsz

import (
	. "gofscq"
	"log"
	"testing"

	"github.com/dterei/gotsc"
)

const cachesize = 100000

func do_read(cs Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_,
	addr Num) Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_ {
	var ret Pair_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct__Pair_ImmutableBuffer_Struct_
	Cache_read(&ret, &addr, &cs)
	return ret.Fst
}

func do_write(cs Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_,
	addr Num) Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_ {
	var new_cs Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_
	var buf ImmutableBuffer
	Cache_write(&new_cs, &addr, &buf, &cs)
	return new_cs
}

func do_sync(cs Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_,
	addr Num) Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_ {
	var new_cs Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_
	Cache_sync(&new_cs, &addr, &cs)
	return new_cs
}

func do_log_read(lxp Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num,
	addr Num,
	mscs Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_) Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_ {
	var ret Pair_Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct__Pair_ImmutableBuffer_Struct_
	Log_read(&ret, &lxp, &addr, &mscs)
	return ret.Fst
}

func init_ams() Pair_Bool_Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_ {
	var mscs Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_
	cache_size := Num_of_i64(cachesize)
	Cache_init(&mscs.Snd, &cache_size)
	return Pair_Bool_Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct_{true /* from AsyncFS.recover */, mscs}
}

/* type log_xparams Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num */

/*
func init_lxp() Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num {
	lxp := New_Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num()
	lxp.Fst.Fst.Fst.Fst.Fst = 1
	lxp.Fst.Fst.Fst.Fst.Snd = 1 + (32768 + 1024 + 1 + 1) + 1
	lxp.Fst.Fst.Fst.Snd = 1 + (32768 + 1024 + 1 + 1) + 1 + 1
	lxp.Fst.Fst.Snd = 1
	lxp.Fst.Snd = 1 + (32768 + 1024 + 1 + 1) + 1 + 1 + 1
	lxp.Snd = 32768 / 64
	return lxp
}
*/

const (
	valulen                         = 1024 * 32
	INODE_IRecSig_items_per_val     = 32
	PaddedLog_DescSig_items_per_val = valulen / 64
)

func compute_xparams(data_bitmaps, inode_bitmaps, log_descr_blocks uint64) Pair_Pair_Pair_Pair_Pair_Pair_Pair_Num_Num_Pair_Num_Num_Pair_Num_Num_Pair_Num_Num_Num_Num_Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num {
	data_blocks := data_bitmaps * valulen
	inode_blocks := inode_bitmaps * valulen / INODE_IRecSig_items_per_val
	inode_base := data_blocks
	balloc_base1 := inode_base + inode_blocks + inode_bitmaps
	balloc_base2 := balloc_base1 + data_bitmaps
	log_hdr := 1 + balloc_base2 + data_bitmaps
	log_descr := log_hdr + 1
	log_data := log_descr + log_descr_blocks
	log_data_size := log_descr_blocks * PaddedLog_DescSig_items_per_val
	max_addr := log_data + log_data_size
	var lxp Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num
	lxp.Fst.Fst.Fst.Fst.Fst = 1
	lxp.Fst.Fst.Fst.Fst.Snd = Num(log_hdr)
	lxp.Fst.Fst.Fst.Snd = Num(log_descr)
	lxp.Fst.Fst.Snd = Num(log_descr_blocks)
	lxp.Fst.Snd = Num(log_data)
	lxp.Snd = Num(log_data_size)
	var ret Pair_Pair_Pair_Pair_Pair_Pair_Pair_Num_Num_Pair_Num_Num_Pair_Num_Num_Pair_Num_Num_Num_Num_Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num /* fs_xparams */
	ret.Snd = lxp
	ret.Fst.Fst.Fst.Fst.Fst.Fst = Pair_Num_Num{Num(inode_base), Num(inode_blocks)}
	ret.Fst.Fst.Fst.Fst.Fst.Snd = Pair_Num_Num{Num(balloc_base1), Num(data_bitmaps)}
	ret.Fst.Fst.Fst.Fst.Snd = Pair_Num_Num{Num(balloc_base2), Num(data_bitmaps)}
	ret.Fst.Fst.Fst.Snd = Pair_Num_Num{Num(inode_base + inode_blocks), Num(inode_bitmaps)}
	ret.Fst.Fst.Snd = 1         /* FSXPRootInum */
	ret.Fst.Snd = Num(max_addr) /* FSXPMaxBlock */
	return ret
}

const usetsc = false

func BenchmarkGetSz(b *testing.B) {
	disk := "disk.img"
	Init_disk(disk)
	ams, fsxp := init_ams(), compute_xparams(1, 1, 256)
	var tsc uint64
	var start uint64
	if usetsc {
		tsc = gotsc.TSCOverhead()
		start = gotsc.BenchStart()
	}
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		var ret Pair_Pair_Bool_Pair_Pair_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_ImmutableBuffer_Slice_Slice_Pair_Num_Buffer_AddrMap_ImmutableBuffer_Pair_Pair_AddrMap_Pair_ImmutableBuffer_Bool_Num_Struct__Pair_ImmutableBuffer_Struct_
		inode := Num(2)
		Asyncfs_file_get_sz(&ret, &fsxp, &inode, &ams)
		if i == 0 {
			log.Printf("out: %d", ret.Snd.Fst)
		}
	}
	if usetsc {
		end := gotsc.BenchEnd()
		avg := (end - start - tsc) / uint64(b.N)
		log.Printf("cycles: %d", avg)
	}
}
