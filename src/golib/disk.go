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

type DiskStats struct {
	reads Num
	writes Num
	syncs Num
}

const debug = false

var disk_file *os.File
var disk_stats *DiskStats

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
	disk_stats = new(DiskStats)
}

func DiskWrite (addr *Num, buf *Buffer) {
	buffer := bytes.NewBuffer(buf.val)
	if debug {
		fmt.Println("DiskWrite %v -> %v", buffer, addr)
	}
	off := New_Num()
	*off = Num_of_i64(4096)
	off.Multiply(off, addr)

	disk_file.WriteAt(buffer.val, off.Int64())
	(&disk_stats.writes).Increment()
    // TODO implement this
}

func DiskRead (dst *Buffer, addr *Num) {
	if debug {
		fmt.Println("DiskRead -> %v", addr)
	}
	(&disk_stats.reads).Increment()

    // TODO implement this
}

func DiskSync() {
	fmt.Println("DiskSync")
}