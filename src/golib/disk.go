package fscq

import (
	"log"
	"os"
	"syscall"
)

type Buffer []byte

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
	**dst = append([]byte{}, *d...)
}

func (d ImmutableBuffer) DeepCopy(dst *ImmutableBuffer) {
	// TODO: don't always allocate
	*dst = d
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
		log.Printf("write(%v)\n", addr)
	}
	off := Num_of_i64(4096)
	off.Multiply(off, addr)

	n_bytes, err := disk_file.WriteAt(*buf, off.Int64())
	(&disk_stats.writes).Increment()

	if n_bytes != 4096 {
		log.Panicf("write_disk: short write: %v @ %v\n", n_bytes, addr)
	}

	if err != nil {
		log.Panicf("write error: %v", err)
	}
}

func DiskRead(dst *Buffer, addr Num) {
	if debug {
		log.Printf("read(%v)\n", addr)
	}
	off := Num_of_i64(4096)
	off.Multiply(off, addr)

	*dst = Buffer(make([]byte, 4096))

	n_bytes, err := disk_file.ReadAt(*dst, off.Int64())
	(&disk_stats.reads).Increment()

	if n_bytes != 4096 {
		log.Panicf("read_disk: short read: %v @ %v\n", n_bytes, off)
	}

	if err != nil {
		log.Panicf("read error: %v\n", err)
	}
}

func DiskSync() {
	if debug {
		log.Printf("sync()")
	}

	(&disk_stats.syncs).Increment()
	err := syscall.Fdatasync(int(disk_file.Fd()))

	if err != nil {
		log.Panicf("sync error: %v\n", err)
	}
}
