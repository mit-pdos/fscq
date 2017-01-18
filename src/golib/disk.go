package fscq

import(
	"math/big"
	"fmt"
	)

type DiskBlock struct {
	val big.Int
}

func (d DiskBlock) DeepCopy () *DiskBlock {
	x := new(DiskBlock)
	(*x).val = d.val
	return x
}

func New_DiskBlock() *DiskBlock {
	return new(DiskBlock)
}

func DiskWrite (addr *Num, val *DiskBlock) {
	fmt.Println("DiskWrite %s -> %s", val.val.String(), addr.String())
    // TODO implement this
}