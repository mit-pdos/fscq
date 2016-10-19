package cache

import (
	"math/big"
)

// (This stuff should go in other files)

const valubytes = 4096

type nat *big.Int

type addr nat

type valu *[valubytes]byte

func DiskWrite(a addr, v valu) {
	panic("not impl")
}

// Start Cache.v here

type valubool struct {
	fst valu
	snd bool
}

type map_bigint_valubool struct {
	// TODO
}

// nil if not found
func (m *map_bigint_valubool) Get(a addr) *valubool {
	panic("not impl")
}

func (m *map_bigint_valubool) Add(a addr, vb valubool) {
	panic("not impl")
}

func (m *map_bigint_valubool) Remove(a addr) {
	panic("not impl")
}

func (m *map_bigint_valubool) Size() nat {
	panic("not impl")
}

type cachemap map_bigint_valubool

type cachestate struct {
	CSMap      cachemap
	CSMaxCount nat
	// CSEvict eviction_state
}

func writeback(a addr, cs *cachestate) {
	var vb *valubool
	vb = cs.CSMap.Get(a)
	if vb != nil {
		if vb.snd {
			DiskWrite(a, vb.fst)
			cs.CSMap.Add(a, valubool{vb.fst, false})
		}
	}
}

func evict(a addr, cs *cachestate) {
	writeback(a, cs)
	cs.CSMap.Remove(a)
}
