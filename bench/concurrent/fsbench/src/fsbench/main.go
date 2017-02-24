package main

import (
	"filesys"
	"flag"
	"fmt"
	"log"
	"pin"
	"runtime"
	"time"
	"workload"
)

type DataPoint struct {
	fsIdent   string
	fs        filesys.Options
	work      workload.Options
	parallel  bool
	result    workload.Result
	seqResult workload.Result
}

func (p DataPoint) ParallelSpeedup() float64 {
	return float64(2*p.seqResult.Elapsed) / float64(p.result.Elapsed)
}

func (p DataPoint) MicrosPerOp() float64 {
	return float64(p.result.Elapsed.Nanoseconds()) / 1000 / float64(p.work.Kiters*1000)
}

func (p DataPoint) SeqPoint() DataPoint {
	p.parallel = false
	return p
}

func toSec(d time.Duration) float64 {
	return float64(d) / float64(time.Second)
}

func toMicros(d time.Duration) float64 {
	return float64(d) / float64(time.Microsecond)
}

var DataRowHeader = []interface{}{
	"fs", "name_cache", "attr_cache", "neg_name_cache", "kernel_cache", "server-cpu",
	"operation", "client-cpus", "exists", "disjoint-directories", "kiters",
	"parallel",
	"timeSec", "opStdMicros", "seqTimeSec", "seqOpStdMicros",
	"speedup", "usPerOp",
}

func (p DataPoint) DataRow() []interface{} {
	clientCpuSpec := fmt.Sprintf("\"%s\"", pin.CpuSpec(p.work.ClientCpus))
	return []interface{}{
		p.fsIdent, p.fs.NameCache, p.fs.AttrCache, p.fs.NegNameCache, p.fs.KernelCache, p.fs.ServerCpu,
		p.work.Operation, clientCpuSpec, p.work.ExistingPath, p.work.DisjointDirectories, p.work.Kiters,
		p.parallel,
		toSec(p.result.Elapsed), toMicros(p.result.Stddev), toSec(p.seqResult.Elapsed), toMicros(p.seqResult.Stddev),
		p.ParallelSpeedup(), p.MicrosPerOp(),
	}
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

	opts := workload.Options{
		Operation:           *operation,
		ClientCpus:          pin.NewCpus(*client_cpus),
		ExistingPath:        *existingPath,
		DisjointDirectories: *disjointDirectories,
		Kiters:              *kiters,
	}

	opts.Warmup(fs)

	var result workload.Result
	if *targetMs > 0 {
		result = opts.SearchWorkload(fs, *parallel, *targetMs)
	} else {
		result = opts.RunWorkload(fs, *parallel)
	}
	var seqResult workload.Result
	if *parallel {
		seqResult = opts.RunWorkload(fs, false)
	} else {
		seqResult = result
	}

	fs.Stop()

	p := DataPoint{
		fsIdent:   fs.Ident(),
		fs:        fsOpts,
		work:      opts,
		parallel:  *parallel,
		result:    result,
		seqResult: seqResult,
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
