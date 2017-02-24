package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path"
	"runtime"
	"strconv"
	"strings"
	"time"
)

type FileSystem struct {
	ident    string
	binary   string
	filename string
	isFuse3  bool
	args     []string
}

var fscqArgs = []string{"disk.img", "/tmp/fscq"}
var helloArgs = []string{"/tmp/hellofs"}

var fileSystems = []FileSystem{
	{ident: "fscq",
		binary:   "fscq",
		filename: "/tmp/fscq/small-4k",
		args:     fscqArgs},
	{ident: "cfscq",
		binary:   "cfscq",
		filename: "/tmp/fscq/small-4k",
		args:     fscqArgs},
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
		isFuse3:  true,
		args:     helloArgs},
	{ident: "native",
		binary:   "true",
		filename: "/etc/passwd",
		args:     []string{}},
}

func parseIdent(s string) (FileSystem, error) {
	for _, fs := range fileSystems {
		if fs.ident == s {
			return fs, nil
		}
	}
	return FileSystem{}, fmt.Errorf("unknown filesystem identifier %s", s)
}

func (fs FileSystem) isFuse() bool {
	return fs.ident != "native"
}

func (fs FileSystem) isHaskell() bool {
	return fs.ident == "fscq" || fs.ident == "cfscq" || fs.ident == "hfuse"
}

// A CpuSpec is a specification of CPUs in the form expected by taskset (numerical list,
// separated by commas, including ranges)
type CpuSpec string

type fuseOptions struct {
	nameCache    bool
	attrCache    bool
	negNameCache bool
	kernelCache  bool
	serverCpu    CpuSpec
}

func (id CpuSpec) isPin() bool {
	return id != ""
}

func (id CpuSpec) Command(name string, args ...string) *exec.Cmd {
	if !id.isPin() {
		return exec.Command(name, args...)
	}
	tasksetArgs := []string{"-c", string(id), name}
	args = append(tasksetArgs, args...)
	return exec.Command("taskset", args...)
}

func timeoutIfTrue(name string, toggle bool) string {
	if !toggle {
		return fmt.Sprintf("%s=0", name)
	}
	return fmt.Sprintf("%s=1", name)
}

func (o fuseOptions) optString() string {
	opts := strings.Join([]string{
		timeoutIfTrue("entry_timeout", o.nameCache),
		timeoutIfTrue("negative_timeout", o.negNameCache),
		timeoutIfTrue("attr_timeout", o.attrCache),
	}, ",")
	if o.kernelCache {
		opts += ",kernel_cache"
	}
	return opts
}

func (fs FileSystem) Launch(opts fuseOptions) {
	var args []string
	args = append(args, fs.args...)
	if fs.isFuse() {
		args = append(args, "-o", opts.optString())
	}
	if fs.isHaskell() {
		args = append(args, "+RTS", "-N2", "-RTS")
	}
	cmd := opts.serverCpu.Command(fs.binary, args...)
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

type workloadOptions struct {
	operation    string
	clientCpus   []CpuSpec
	existingPath bool
	kiters       int
}

func (opts workloadOptions) WithKiters(kiters int) workloadOptions {
	opts.kiters = kiters
	return opts
}

func min(a, b int) int {
	if a <= b {
		return a
	}
	return b
}

func max(a, b int) int {
	if a >= b {
		return a
	}
	return b
}

// SearchWorkload runs a workload, varying kiters until the run takes at least targetMs milliseconds.
// The input opts should specify the workload parameters and initial kiters for
// the search. SearchWorkload returns the final duration and modifies the input
// opts to have the final kiters.
func (fs FileSystem) SearchWorkload(opts *workloadOptions, parallel bool, targetMs int) time.Duration {
	targetTime := time.Duration(targetMs) * time.Millisecond
	timeTaken := fs.RunWorkload(*opts, parallel)
	for timeTaken < targetTime {
		last := opts.kiters
		// Predict required iterations
		kiters := int(float64(last) * float64(targetTime) / float64(timeTaken))
		// same policy as Go's testing/benchmark.go (see func (b *B) launch()): //
		// run 1.2x the iterations we estimate, but don't grow by more than 100x last
		// time and run at least one more iteration
		opts.kiters = max(min(kiters+kiters/5, 100*last), last+1)
		timeTaken = fs.RunWorkload(*opts, parallel)
	}
	return timeTaken
}

func (fs FileSystem) RunWorkload(opts workloadOptions, parallel bool) time.Duration {
	path := fs.filename
	if !opts.existingPath {
		path += "x"
	}
	copies := 1
	if parallel {
		copies = 2
	}

	args := []string{opts.operation, path, strconv.Itoa(opts.kiters)}

	done := make(chan float64)
	for i := 0; i < copies; i++ {
		go func(spec CpuSpec) {
			cmd := spec.Command("fsops", args...)
			output, err := cmd.Output()
			if err != nil {
				log.Fatal(fmt.Errorf("could not run fsops: %v", err))
			}
			outputNum := strings.TrimRight(string(output), "\n")
			elapsedNs, err := strconv.ParseFloat(outputNum, 64)
			if err != nil {
				log.Fatal(fmt.Errorf("could not parse fsops output %s", outputNum))
			}
			done <- elapsedNs
		}(opts.clientCpus[i])
	}
	var elapsedTime float64
	for i := 0; i < copies; i++ {
		timing := <-done
		if timing > elapsedTime {
			elapsedTime = timing
		}
	}
	return time.Duration(int64(elapsedTime))
}

func printTsv(args ...interface{}) {
	for i, arg := range args {
		fmt.Print(arg)
		if i != len(args)-1 {
			fmt.Print("\t")
		}
	}
	fmt.Print("\n")
}

func toSec(d time.Duration) float64 {
	return float64(d) / float64(time.Second)
}

type DataPoint struct {
	fsIdent string
	fuseOptions
	workloadOptions
	parallel       bool
	elapsedTimeSec float64
	seqTimeSec     float64
}

func (p DataPoint) ParallelSpeedup() float64 {
	return 2 * p.seqTimeSec / p.elapsedTimeSec
}

func (p DataPoint) MicrosPerOp() float64 {
	return p.elapsedTimeSec / float64(p.kiters) * 1000
}

func (p DataPoint) SeqPoint() DataPoint {
	return DataPoint{
		p.fsIdent,
		p.fuseOptions,
		p.workloadOptions,
		false,
		p.seqTimeSec,
		p.seqTimeSec,
	}
}

var DataRowHeader = []interface{}{
	"fs", "name_cache", "attr_cache", "neg_name_cache", "kernel_cache", "server-cpu",
	"operation", "client-cpus", "exists", "kiters",
	"parallel",
	"timeSec", "seqTimeSec", "speedup", "usPerOp",
}

func (p DataPoint) DataRow() []interface{} {
	return []interface{}{
		p.fsIdent, p.nameCache, p.attrCache, p.negNameCache, p.kernelCache, p.serverCpu,
		p.operation, serializeCpuSpecs(p.clientCpus), p.existingPath, p.kiters,
		p.parallel,
		p.elapsedTimeSec, p.seqTimeSec, p.ParallelSpeedup(), p.MicrosPerOp(),
	}
}

// parseCpuSpecs parses pipe-separated CPU specs
func parseCpuSpecs(specsString string) []CpuSpec {
	specs := strings.SplitN(specsString, "/", 2)
	if len(specs) == 1 {
		spec := CpuSpec(specs[0])
		return []CpuSpec{spec, spec}
	}
	return []CpuSpec{CpuSpec(specs[0]), CpuSpec(specs[1])}
}

func serializeCpuSpecs(specs []CpuSpec) string {
	var specStrings []string
	for _, spec := range specs {
		specStrings = append(specStrings, string(spec))
	}
	return strings.Join(specStrings, "/")
}

func main() {
	print_header := flag.Bool("print-header", false, "just print a data header")
	operation := flag.String("op", "stat", "operation to perform (stat or open)")
	existingPath := flag.Bool("exists", false, "operate on an existing file")
	parallel := flag.Bool("parallel", false, "run operation in parallel")
	kiters := flag.Int("kiters", 1, "thousands of iterations to run the operation")
	targetMs := flag.Int("target-ms", 0,
		"search for iterations to run for at least this many ms (0 to disable search)")
	attr_cache := flag.Bool("attr-cache", false, "enable fuse attribute cache")
	name_cache := flag.Bool("name-cache", false, "enable fuse entry (name) cache")
	neg_name_cache := flag.Bool("neg-cache", false, "enable fuse negative (deleted) name cache")
	kernel_cache := flag.Bool("kernel-cache", false, "enable kernel cache")

	server_cpu := flag.String("server-cpu", "", "pin server to a cpu (empty string to not pin)")
	client_cpus := flag.String("client-cpus", "",
		"pin clients to cpus (when running in parallel, separate cpus with a slash\n"+
			"or provide a single spec)")

	flag.Parse()

	if *print_header {
		dataHeader := len(DataRowHeader)
		dataRow := len(DataPoint{}.DataRow())
		if dataRow != dataHeader {
			log.Fatal(fmt.Errorf("data header len != data row len (%d != %d)",
				dataHeader, dataRow))
		}
		printTsv(DataRowHeader...)
		return
	}

	if flag.NArg() == 0 {
		log.Fatal(fmt.Errorf("missing file system choice"))
	}

	fsident := flag.Arg(0)
	fs, err := parseIdent(fsident)
	if err != nil {
		log.Fatal(err)
	}

	if !(*operation == "stat" || *operation == "open") {
		log.Fatal(fmt.Errorf("invalid operation %s: expected stat or open", *operation))
	}

	if *parallel {
		runtime.GOMAXPROCS(2)
	}

	fuseOpts := fuseOptions{
		nameCache:    *name_cache,
		negNameCache: *neg_name_cache,
		attrCache:    *attr_cache,
		kernelCache:  *kernel_cache,
		serverCpu:    CpuSpec(*server_cpu),
	}

	fs.Launch(fuseOpts)

	opts := workloadOptions{
		operation:    *operation,
		clientCpus:   parseCpuSpecs(*client_cpus),
		existingPath: *existingPath,
		kiters:       *kiters,
	}

	// warmup
	fs.RunWorkload(opts.WithKiters(1), false)

	var elapsed time.Duration
	if *targetMs > 0 {
		elapsed = fs.SearchWorkload(&opts, *parallel, *targetMs)
	} else {
		elapsed = fs.RunWorkload(opts, *parallel)
	}
	var seqTime time.Duration
	if *parallel {
		seqTime = fs.RunWorkload(opts, false)
	} else {
		seqTime = elapsed
	}

	fs.Stop()

	p := DataPoint{
		fsIdent:         fs.ident,
		fuseOptions:     fuseOpts,
		workloadOptions: opts,
		parallel:        *parallel,
		elapsedTimeSec:  toSec(elapsed),
		seqTimeSec:      toSec(seqTime),
	}

	printTsv(p.DataRow()...)
	if *parallel {
		printTsv(p.SeqPoint().DataRow()...)
	}
	return
}
