package fscq

import(
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

func DiskWrite (addr *Num, buf *Buffer) {
	buffer := bytes.NewBuffer(buf.val)
	fmt.Println("DiskWrite %v -> %v", buffer, addr)
    // TODO implement this
}

func DiskRead (dst *Buffer, addr *Num) {
	fmt.Println("DiskRead -> %v", addr)
    // TODO implement this
}

func DiskSync() {
	fmt.Println("DiskSync")
}