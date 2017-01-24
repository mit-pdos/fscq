package fscq

import(
	"math/big"
	"fmt"
	"bytes"
	)

type Buffer struct {
	sz Num
	val []byte
}

func (d Buffer) DeepCopy () *Buffer {
	x := new(Buffer)
	(*x).sz = d.sz
	copy((*x).val, d.val)
	return x
}

func New_Buffer(sz Num) *Buffer {
	x := new(Buffer)
	x.sz = sz
	return x
}

func DiskWrite (addr *big.Int, buf *Buffer) {
	buffer := bytes.NewBuffer(buf.val)
	fmt.Println("DiskWrite %s -> %s", buffer.String(), addr.String())
    // TODO implement this
}

func DiskSync() {
	fmt.Println("DiskSync")
}