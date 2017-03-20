package fscq

import (
	"fmt"
	"os"
	"syscall"
)

type Buffer struct {
	sz_bits int64
	data    []byte
}

type ImmutableBuffer Buffer

type DiskStats struct {
	reads  Num
	writes Num
	syncs  Num
}

const debug = true

var disk_file *os.File
var disk_stats *DiskStats

func (d *Buffer) DeepCopy(dst **Buffer) {
	// TODO: don't always allocate
	**dst = Buffer{d.sz_bits, append([]byte{}, d.data...)}
}

func (d ImmutableBuffer) DeepCopy(dst *ImmutableBuffer) {
	// TODO: don't always allocate
	*dst = ImmutableBuffer{d.sz_bits, append([]byte{}, d.data...)}
}

func (d *Buffer) fill_to_size() {
	bytes := (d.sz_bits + 7) / 8

	for i := int64(len(d.data)); i < bytes; i++ {
		d.data = append(d.data, 0)
	}
}

func New_Buffer() *Buffer {
	return &Buffer{}
}

func New_ImmutableBuffer() ImmutableBuffer {
	return ImmutableBuffer{}
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

func DiskWrite(addr Num, buf *Buffer) {
	if debug {
		fmt.Printf("write(%v)\n", addr)
	}
	off := Num_of_i64(4096)
	off.Multiply(off, addr)

	buf.fill_to_size()

	n_bytes, err := disk_file.WriteAt(buf.data, off.Int64())
	(&disk_stats.writes).Increment()

	if n_bytes != 4096 {
		os.Stderr.WriteString(fmt.Sprintf("write_disk: short write: %v @ %v\n", n_bytes, addr))
	}

	if err != nil {
		fmt.Fprintf(os.Stderr, "write error: %v", err)
	}
}

func DiskRead(dst *Buffer, addr Num) {
	if debug {
		fmt.Printf("read(%v)\n", addr)
	}
	off := Num_of_i64(4096)
	off.Multiply(off, addr)

	dst.fill_to_size()

	n_bytes, err := disk_file.ReadAt(dst.data, off.Int64())
	(&disk_stats.reads).Increment()

	if n_bytes != 4096 {
		os.Stderr.WriteString(fmt.Sprintf("read_disk: short read: %v @ %v\n", n_bytes, off))
	}

	if err != nil {
		fmt.Fprintf(os.Stderr, "read error: %v\n", err)
	}
}

func DiskSync() {
	if debug {
		fmt.Println("sync()")
	}

	(&disk_stats.syncs).Increment()
	err := syscall.Fdatasync(int(disk_file.Fd()))

	if err != nil {
		fmt.Fprintf(os.Stderr, "sync error: %v\n", err)
	}
}
