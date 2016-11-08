package dirtree

// TODO: put in FSLayout.go
type log_xparams struct {
	DataStart addr
	LogHeader addr

	LogDescriptor addr
	LogDescLen    addr
	LogData       addr
	LogLen        addr
}

type balloc_xparams struct {
	BmapStart   addr
	BmapNBlocks addr
}

type inode_xparams struct {
	IXStart addr
	IXLen   addr
}

type fs_xparams struct {
	FSXPLog         log_xparams
	FSXPInode       inode_xparams
	FSXPBlockAlloc1 balloc_xparams
	FSXPBlockAlloc2 balloc_xparams
	FSXPInodeAlloc  balloc_xparams
	FSXPRootInum    addr
	FSXPMaxBlock    addr
}

// map from big int to valu
type valumap struct {
	// TODO
}

type entry struct {
	fst addr
	snd valu
}

type MemLog_mstate valumap

type DiskLog_contents []entry

type txnlist []DiskLog_contents

type GroupLog_mstate struct {
	MSVMap *valumap
	MSTxns *txnlist
	MSMLog *MemLog_mstate
}

func MSLL(ms GroupLog_memstate) MemLog_memstate {
	return MemLog_memstate{ms.fst.MSMlog, ms.snd}
}

type Log_mstate struct {
	MSTxn  valumap
	MSGLog GroupLog_mstate
}

type Log_memstate struct {
	fst *Log_mstate
	snd *cachestate
}

// TODO: put in BFile.go
type BFile_memstate struct {
	fst bool
	snd *Log_memstate
}

/*
func MSAlloc(ms BFILE_memstate) bool {
	return ms.fst
}

func MSLL(ms BFILE_memstate) Log_memstate {
	return ms.snd
}*/

type GroupLog_memstate struct{}

type pair_balloc_xparams_balloc_xparams struct {
	fst balloc_xparams
	snd balloc_xparams
}

func FSXPBlockAlloc(fsxp fs_xparams) pair_balloc_xparams_balloc_xparams {
	return pair_balloc_xparams_balloc_xparams{fsxp.FSXPBlockAlloc1, fsxp.FSXPBlockAlloc2}
}

func IAlloc_alloc(lxp log_xparams, xp fs_xparams, ms *MemLog_memstate) *addr {
	panic("not impl")
}

type Errno int

type Err_unit struct {
	// only one non-nil
	OK  *struct{}
	Err *Errno
}
type Err_addr struct {
	// only one non-nil
	OK  *addr
	Err *Errno
}

type addr_bool struct {
	fst addr
	snd bool
}

type option_addr_bool *addr_bool

type Err_addr_bool struct {
	// only one non-nil
	OK  *addr_bool
	Err *Errno
}

// QUESTION: Use pointers more?

func namei(fsxp fs_xparams, dnum addr, fnlist []string, mscs *mscs) Err_addr_bool {
	var lxp log_xparams
	var bxp pair_balloc_xparams_balloc_xparams
	var ibxp fs_xparams
	var ixp inode_xparams
	lxp = fsxp.FSXPLog
	bxp = FSXPBlockAlloc(fsxp)
	ibxp = fsxp
	ixp = fsxp.FSXPInode
	var inum addr
	var isdir bool
	var valid Err_unit
	var fn string
	for fn = range fnlist {
		if valid.Err != nil {
			inum = inum
			isdir = isdir
			valid = Err_unit{nil, &*valid.Err}
		} else {
			if isdir {
				var r option_addr_bool
				r = SDIR_lookup(lxp, ikxp, inum, fn, mscs)
				if r != nil {
					inum = r.fst
					isdir = r.snd
					valid = Err_unit{&struct{}{}, nil}
				}
			} else {
				inum = inum
				isdir = isdir
				valid = Err_unit{nil, &ENOTDIR}
			}
		}
	}
	if valid.OK != nil {
		return Err_addr_bool{addr_bool{inum, isdir}, nil}
	} else {
		return Err_addr_bool{nil, &*valid.Err}
	}
}

func mkfile(fsxp fs_xparams, dnum addr, name string, fms *GroupLog_memstate) Err_addr {
	var lxp log_xparams
	var bxp pair_balloc_xparams_balloc_xparams
	var ibxp fs_xparams
	var ixp inode_xparams
	lxp = fsxp.FSXPLog
	bxp = FSXPBlockAlloc(fsxp)
	ibxp = fsxp
	ixp = fsxp.FSXPInode
	var al bool
	var ms *MemLog_memstate
	al, ms = fms.fst, fms.snd // according to semantics, now fms == (Moved, Moved)
	var oi *addr
	oi = IAlloc_alloc(lxp, ibxp, ms)
	fms.fst, fms.snd = al, ms
	if oi == nil {
		return Err_addr{nil, &ENOSPCINODE}
	} else {
		// etc
	}
}
