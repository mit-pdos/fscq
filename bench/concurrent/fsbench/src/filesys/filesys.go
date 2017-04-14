package filesys

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"path"
	"pin"
	"strings"
	"time"
)

type FileSystem struct {
	ident          string
	binary         string
	mntPoint       string
	filenames      []string
	isFuse3        bool
	isHaskell      bool
	parsesOwnFlags bool
	args           []string
}

var fscqMnt = "/tmp/fscq"

func fscqFs(name string) FileSystem {
	var filenames []string
	for num := 1; num < 20; num++ {
		filenames = append(filenames,
			path.Join(fscqMnt, fmt.Sprintf("dir%d/file1", num)))
	}
	return FileSystem{
		ident:     name,
		binary:    name,
		mntPoint:  fscqMnt,
		filenames: filenames,
		isHaskell: true,
		//filenames: []string{
		//	path.Join(fscqMnt, "a/b/c/d/e/f/file"),
		//	path.Join(fscqMnt, "a____/b____/c____/d____/e____/f____/file"),
		//},
		args: []string{"disk.img", fscqMnt},
	}
}

var helloMnt = "/tmp/hellofs"

var fileSystems = []FileSystem{
	fscqFs("fscq"),
	fscqFs("cfscq"),
	{ident: "hfuse",
		binary:    "HelloFS",
		mntPoint:  helloMnt,
		filenames: []string{path.Join(helloMnt, "hello")},
		isHaskell: true,
		args:      []string{helloMnt}},
	{ident: "c-hello",
		binary:    "hello",
		mntPoint:  helloMnt,
		filenames: []string{path.Join(helloMnt, "hello")},
		isFuse3:   true,
		args:      []string{helloMnt}},
	{ident: "fusexmp",
		binary:   "passthrough",
		mntPoint: helloMnt,
		filenames: []string{"/tmp/hellofs/etc/passwd",
			"/tmp/hellofs/usr/bin/true"},
		isFuse3: true,
		args:    []string{helloMnt}},
	{ident: "slowfs",
		binary:         "slowfs",
		mntPoint:       "/tmp/slowfs",
		filenames:      []string{"/tmp/slowfs/default"},
		isHaskell:      true,
		parsesOwnFlags: true,
		args:           []string{"/tmp/slowfs"}},
	{ident: "native",
		binary: "true",
		filenames: []string{"/etc/passwd",
			"/usr/bin/true"},
		args: []string{}},
}

func New(s string) (FileSystem, error) {
	for _, fs := range fileSystems {
		if fs.ident == s {
			return fs, nil
		}
	}
	return FileSystem{}, fmt.Errorf("unknown filesystem identifier %s", s)
}

func (fs FileSystem) Ident() string {
	return fs.ident
}

func (fs FileSystem) isFuse() bool {
	return fs.ident != "native"
}

func (fs FileSystem) MountPoint() string {
	return fs.mntPoint
}

type Options struct {
	NameCache    bool
	AttrCache    bool
	NegNameCache bool
	KernelCache  bool
	ServerCpu    pin.Cpu
	RtsOpts      []string
	FsFlags      []string
}

var DataHeader = []interface{}{
	"name_cache", "attr_cache", "neg_name_cache", "kernel_cache",
	"server-cpu",
	"rts-opts",
}

func (o Options) DataRow() []interface{} {
	return []interface{}{
		o.NameCache, o.AttrCache, o.NegNameCache, o.KernelCache,
		o.ServerCpu,
		fmt.Sprintf("\"%s\"", strings.Join(o.RtsOpts, " ")),
	}
}

func timeoutIfTrue(name string, toggle bool) string {
	if !toggle {
		return fmt.Sprintf("%s=0", name)
	}
	return fmt.Sprintf("%s=1", name)
}

func (o Options) optString() string {
	opts := strings.Join([]string{
		timeoutIfTrue("entry_timeout", o.NameCache),
		timeoutIfTrue("negative_timeout", o.NegNameCache),
		timeoutIfTrue("attr_timeout", o.AttrCache),
	}, ",")
	if o.KernelCache {
		opts += ",kernel_cache"
	}
	return opts
}

func (fs FileSystem) Launch(opts Options) {
	var args []string
	args = append(args, opts.FsFlags...)
	args = append(args, fs.args...)
	if fs.isHaskell {
		args = append(args, "+RTS")
		// GC options:
		// "-A6G", // large initial allocation area (avoids needs for most GC)
		// "-I0",  // disable idle GC (default: idle after 0.3s)
		args = append(args, opts.RtsOpts...)
		args = append(args, "-RTS")
	}
	if fs.isFuse() {
		if fs.parsesOwnFlags {
			args = append(args, "--")
		}
		args = append(args, "-o", opts.optString())
	}
	cmd := opts.ServerCpu.Command(fs.binary, args...)
	cmd.Stderr = os.Stderr
	cmd.Run()
	time.Sleep(10 * time.Millisecond)
	if _, err := os.Stat(fs.filenames[0]); os.IsNotExist(err) {
		log.Fatal(fmt.Errorf("failed to launch %s %s", fs.binary, strings.Join(args, " ")))
	}
}

func (fs FileSystem) Stop() {
	if fs.isFuse() {
		mountCmd := "fusermount"
		if fs.isFuse3 {
			mountCmd = "fusermount3"
		}
		cmd := exec.Command(mountCmd, "-u", fs.mntPoint)
		cmd.Stderr = os.Stderr
		err := cmd.Run()
		if err != nil {
			log.Fatal(fmt.Errorf("could not unmount: %v", err))
		}
	}
}

func (fs FileSystem) Pathname(i int) string {
	return fs.filenames[i%len(fs.filenames)]
}
