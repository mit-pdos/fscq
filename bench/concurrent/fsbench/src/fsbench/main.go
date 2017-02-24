package main

import (
	"filesys"
	"flag"
	"fmt"
	"log"
	"pin"
	"runtime"
	"strconv"
	"strings"
	"time"
)

type workloadOptions struct {
	operation           string
	clientCpus          []pin.Cpu
	existingPath        bool
	disjointDirectories bool
	kiters              int
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

type runResult struct {
	totalNs    float64
	iterStddev float64
}

type WorkloadResult struct {
	elapsed time.Duration
	// stddev of per operation time
	stddev time.Duration
}

func (opts workloadOptions) RunWorkload(fs filesys.FileSystem, parallel bool) WorkloadResult {
	copies := 1
	if parallel {
		copies = 2
	}
	var paths []string
	for i := 0; i < copies; i++ {
		var path string
		if opts.disjointDirectories {
			path = fs.DisjointPath(i)
		} else {
			path = fs.Pathname()
		}
		if !opts.existingPath {
			path += "x"
		}
		paths = append(paths, path)
	}

	args := func(i int) []string {
		return []string{opts.operation, paths[i], strconv.Itoa(opts.kiters)}
	}

	done := make(chan runResult)
	for i := 0; i < copies; i++ {
		go func(i int) {
			cmd := opts.clientCpus[i].Command("fsops", args(i)...)
			outputBytes, err := cmd.Output()
			if err != nil {
				log.Fatal(fmt.Errorf("could not run fsops: %v", err))
			}
			output := strings.TrimRight(string(outputBytes), "\n")
			nums := strings.Split(output, " ")
			if len(nums) != 2 {
				log.Fatal(fmt.Errorf("unexpected fsops output %s", output))
			}
			elapsedNs, err := strconv.ParseFloat(nums[0], 64)
			if err != nil {
				log.Fatal(fmt.Errorf("could not parse fsops mean from %s", output))
			}
			iterStddev, err := strconv.ParseFloat(nums[1], 64)
			if err != nil {
				log.Fatal(fmt.Errorf("could not parse fsops stddev from %s", output))
			}
			done <- runResult{elapsedNs, iterStddev}
		}(i)
	}
	var elapsedTime float64
	var iterStddev float64
	for i := 0; i < copies; i++ {
		timing := <-done
		if timing.totalNs > elapsedTime {
			elapsedTime = timing.totalNs
		}
		// combine stddev by taking maximum, just to get a safe estimate
		// (as opposed to correctly computing the stddev of all the samples)
		if timing.iterStddev > iterStddev {
			iterStddev = timing.iterStddev
		}
	}
	return WorkloadResult{
		time.Duration(int64(elapsedTime)),
		time.Duration(int64(iterStddev)),
	}
}

func (opts workloadOptions) Warmup(fs filesys.FileSystem) {
	opts.kiters = 1
	parallel := false
	if opts.disjointDirectories {
		parallel = true
	}
	opts.RunWorkload(fs, parallel)
}

// SearchWorkload runs a workload, varying kiters until the run takes at least targetMs milliseconds.
// The input opts should specify the workload parameters and initial kiters for
// the search. SearchWorkload returns the final duration and modifies the input
// opts to have the final kiters.
func (opts *workloadOptions) SearchWorkload(fs filesys.FileSystem, parallel bool, targetMs int) WorkloadResult {
	targetTime := time.Duration(targetMs) * time.Millisecond
	result := opts.RunWorkload(fs, parallel)
	for result.elapsed < targetTime {
		last := opts.kiters
		// Predict required iterations
		kiters := int(float64(last) * float64(targetTime) / float64(result.elapsed))
		// same policy as Go's testing/benchmark.go (see func (b *B) launch()): //
		// run 1.2x the iterations we estimate, but don't grow by more than 100x last
		// time and run at least one more iteration
		opts.kiters = max(min(kiters+kiters/5, 100*last), last+1)
		result = opts.RunWorkload(fs, parallel)
	}
	return result
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

func toMicros(d time.Duration) float64 {
	return float64(d) / float64(time.Microsecond)
}

type DataPoint struct {
	fsIdent string
	filesys.Options
	workloadOptions
	parallel  bool
	result    WorkloadResult
	seqResult WorkloadResult
}

func (p DataPoint) ParallelSpeedup() float64 {
	return float64(2*p.seqResult.elapsed) / float64(p.result.elapsed)
}

func (p DataPoint) MicrosPerOp() float64 {
	return float64(p.result.elapsed.Nanoseconds()) / 1000 / float64(p.kiters*1000)
}

func (p DataPoint) SeqPoint() DataPoint {
	return DataPoint{
		p.fsIdent,
		p.Options,
		p.workloadOptions,
		false,
		p.result,
		p.result,
	}
}

var DataRowHeader = []interface{}{
	"fs", "name_cache", "attr_cache", "neg_name_cache", "kernel_cache", "server-cpu",
	"operation", "client-cpus", "exists", "disjoint-directories", "kiters",
	"parallel",
	"timeSec", "opStdMicros", "seqTimeSec", "seqOpStdMicros",
	"speedup", "usPerOp",
}

func (p DataPoint) DataRow() []interface{} {
	clientCpuSpec := fmt.Sprintf("\"%s\"", pin.CpuSpec(p.clientCpus))
	return []interface{}{
		p.fsIdent, p.NameCache, p.AttrCache, p.NegNameCache, p.KernelCache, p.ServerCpu,
		p.operation, clientCpuSpec, p.existingPath, p.disjointDirectories, p.kiters,
		p.parallel,
		toSec(p.result.elapsed), toMicros(p.result.stddev), toSec(p.seqResult.elapsed), toMicros(p.seqResult.stddev),
		p.ParallelSpeedup(), p.MicrosPerOp(),
	}
}

func main() {
	print_header := flag.Bool("print-header", false, "just print a data header")
	operation := flag.String("op", "stat", "operation to perform (stat or open)")
	existingPath := flag.Bool("exists", true, "operate on an existing file")
	disjointDirectories := flag.Bool("disjoint-dirs", false,
		"operate on disjoint directories (ignored if unsupported)")
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

	readable_output := flag.Bool("readable", false, "produce verbose, readable output")

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
	fs, err := filesys.New(fsident)
	if err != nil {
		log.Fatal(err)
	}

	if !(*operation == "stat" || *operation == "open") {
		log.Fatal(fmt.Errorf("invalid operation %s: expected stat or open", *operation))
	}

	if *disjointDirectories && !fs.SupportsDisjointDirectories() {
		*disjointDirectories = false
	}

	if *parallel {
		runtime.GOMAXPROCS(2)
	}

	fsOpts := filesys.Options{
		NameCache:    *name_cache,
		NegNameCache: *neg_name_cache,
		AttrCache:    *attr_cache,
		KernelCache:  *kernel_cache,
		ServerCpu:    pin.Cpu(*server_cpu),
	}

	fs.Launch(fsOpts)

	opts := workloadOptions{
		operation:           *operation,
		clientCpus:          pin.NewCpus(*client_cpus),
		existingPath:        *existingPath,
		disjointDirectories: *disjointDirectories,
		kiters:              *kiters,
	}

	opts.Warmup(fs)

	var result WorkloadResult
	if *targetMs > 0 {
		result = opts.SearchWorkload(fs, *parallel, *targetMs)
	} else {
		result = opts.RunWorkload(fs, *parallel)
	}
	var seqResult WorkloadResult
	if *parallel {
		seqResult = opts.RunWorkload(fs, false)
	} else {
		seqResult = result
	}

	fs.Stop()

	p := DataPoint{
		fsIdent:         fs.Ident(),
		Options:         fsOpts,
		workloadOptions: opts,
		parallel:        *parallel,
		result:          result,
		seqResult:       seqResult,
	}

	if *readable_output {
		row := p.DataRow()
		for i, hdr := range DataRowHeader {
			value := row[i]
			fmt.Printf("%-20s %v\n", hdr, value)
		}
	} else {
		printTsv(p.DataRow()...)
		if *parallel {
			printTsv(p.SeqPoint().DataRow()...)
		}
	}
	return
}
