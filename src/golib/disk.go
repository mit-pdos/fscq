package fscq

import(
	"fmt"
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
	x.val = make([]byte, sz.Int64())
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
	if debug {
		fmt.Println("DiskWrite %v -> %v", buf, addr)
	}
	off := New_Num()
	*off = Num_of_i64(4096)
	off.Multiply(off, addr)

	n_bytes, err := disk_file.WriteAt(buf.val, off.Int64())
	(&disk_stats.writes).Increment()

	if n_bytes != 4096 {
		os.Stderr.WriteString(fmt.Sprintf("write_disk: short write: %v @ %v", n_bytes, addr))
	}

	if err != nil {
		os.Stderr.WriteString(fmt.Sprintf("write error: %v", err))
	}
}

func DiskRead (dst *Buffer, addr *Num) {
	if debug {
		fmt.Println("DiskRead -> %v", addr)
	}
	off := New_Num()
	*off = Num_of_i64(4096)
	off.Multiply(off, addr)

	n_bytes, err := disk_file.ReadAt(dst.val, off.Int64())
	(&disk_stats.reads).Increment()

	if n_bytes != 4096 {
		os.Stderr.WriteString(fmt.Sprintf("read_disk: short read: %v @ %v", n_bytes, addr))
	}

	if err != nil {
		os.Stderr.WriteString(fmt.Sprintf("read error: %v", err))
	}
}

func DiskSync() {
	fmt.Println("DiskSync")
}