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
	ident             string
	binary            string
	filename          string
	disjointFilenames []string
	isFuse3           bool
	args              []string
}

var fscqArgs = []string{"disk.img", "/tmp/fscq"}
var helloArgs = []string{"/tmp/hellofs"}

var fileSystems = []FileSystem{
	{ident: "fscq",
		binary:   "fscq",
		filename: "/tmp/fscq/small-4k",
		disjointFilenames: []string{"/tmp/fscq/dir1/file1",
			"/tmp/fscq/dir2/file2"},
		args: fscqArgs},
	{ident: "cfscq",
		binary:   "cfscq",
		filename: "/tmp/fscq/small-4k",
		disjointFilenames: []string{"/tmp/fscq/dir1/file1",
			"/tmp/fscq/dir2/file2"},
		args: fscqArgs},
	{ident: "hfuse",
		binary:   "HelloFS",
		filename: "/tmp/hellofs/hello",
		args:     helloArgs},
	{ident: "c-hello",
		binary:   "hello",
		filename: "/tmp/hellofs/hello",
		isFuse3:  true,
		args:     helloArgs},
	{ident: "fusexmp",
		binary:   "passthrough",
		filename: "/tmp/hellofs/etc/passwd",
		disjointFilenames: []string{"/tmp/hellofs/etc/passwd",
			"/tmp/hellofs/bin/true"},
		isFuse3: true,
		args:    helloArgs},
	{ident: "native",
		binary:   "true",
		filename: "/etc/passwd",
		disjointFilenames: []string{"/etc/passwd",
			"/bin/true"},
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

func (fs FileSystem) isHaskell() bool {
	return fs.ident == "fscq" || fs.ident == "cfscq" || fs.ident == "hfuse"
}

func (fs FileSystem) SupportsDisjointDirectories() bool {
	return len(fs.disjointFilenames) > 0
}

type Options struct {
	NameCache    bool
	AttrCache    bool
	NegNameCache bool
	KernelCache  bool
	ServerCpu    pin.Cpu
}

var DataHeader = []interface{}{
	"name_cache", "attr_cache", "neg_name_cache", "kernel_cache", "server-cpu",
}

func (o Options) DataRow() []interface{} {
	return []interface{}{
		o.NameCache, o.AttrCache, o.NegNameCache, o.KernelCache, o.ServerCpu,
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
	args = append(args, fs.args...)
	if fs.isFuse() {
		args = append(args, "-o", opts.optString())
	}
	if fs.isHaskell() {
		args = append(args, "+RTS", "-A6G", "-qa", "-I0", "-N2", "-qg", "-RTS")
	}
	cmd := opts.ServerCpu.Command(fs.binary, args...)
	cmd.Stderr = os.Stderr
	cmd.Run()
	time.Sleep(10 * time.Millisecond)
	if _, err := os.Stat(fs.filename); os.IsNotExist(err) {
		log.Fatal(fmt.Errorf("failed to launch %s %s", fs.binary, strings.Join(args, " ")))
	}
}

func (fs FileSystem) Stop() {
	if fs.isFuse() {
		dir := path.Dir(fs.filename)
		if fs.ident == "fusexmp" {
			dir = "/tmp/hellofs"
		}
		mountCmd := "fusermount"
		if fs.isFuse3 {
			mountCmd = "fusermount3"
		}
		cmd := exec.Command(mountCmd, "-u", dir)
		cmd.Stderr = os.Stderr
		err := cmd.Run()
		if err != nil {
			log.Fatal(fmt.Errorf("could not unmount: %v", err))
		}
	}
}

func (fs FileSystem) Pathname() string {
	return fs.filename
}

func (fs FileSystem) DisjointPath(i int) string {
	return fs.disjointFilenames[i]
}
