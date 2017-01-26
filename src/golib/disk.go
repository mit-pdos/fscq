package fscq

import(
	"fmt"
	"bytes"
	"os"
	)

type Buffer struct {
	sz Num
	val []byte
}

const debug = false

var disk_file *os.File

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

func Init_disk(path string) {
	f, err := os.OpenFile(path, os.O_RDWR, 0666)
	if err != nil {
		os.Stderr.WriteString("Couldn't open disk file")
		os.Exit(1)
	}

	disk_file = f
}

func DiskWrite (addr *Num, buf *Buffer) {
	buffer := bytes.NewBuffer(buf.val)
	if debug {
		fmt.Println("DiskWrite %v -> %v", buffer, addr)
	}
    // TODO implement this
}

func DiskRead (dst *Buffer, addr *Num) {
	if debug {
		fmt.Println("DiskRead -> %v", addr)
	}
    // TODO implement this
}

func DiskSync() {
	fmt.Println("DiskSync")
}