package fscq

import (
	"sort"
)

type AddrMap map[Num]interface{}

type KeyValPair struct {
	key Num
	val interface{}
}

type KeyValPairs []KeyValPair

func (slice KeyValPairs) Len() int {
	return len(slice)
}

func (slice KeyValPairs) Less(i, j int) bool {
	return slice[i].key < slice[j].key
}

func (slice KeyValPairs) Swap(i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}

// Used only for AddrMap_literal
type LiteralKeyValPair struct {
	key Num
	val interface{}
}

func (m AddrMap) Insert(key Num, val interface{}) {
	m[key] = val
}

func (m AddrMap) Find(key Num) (bool, interface{}) {
	val, ok := m[key]
	return ok, val
}

func (m AddrMap) Cardinality() Num {
	return Num(len(m))
}

func (m AddrMap) Elements() []KeyValPair {
	var elements KeyValPairs
	for k, v := range m {
		elements = append(elements, KeyValPair{k, v})
	}
	sort.Sort(elements)
	return elements
}

func (m AddrMap) Remove(key Num) {
	delete(m, key)
}

func AddrMap_literal(vals ...LiteralKeyValPair) AddrMap {
	a := make(AddrMap)
	for _, keyVal := range vals {
		a.Insert(keyVal.key, keyVal.val)
	}
	return a
}
