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

type DataPoints struct {
	fsIdent  string
	fs       filesys.Options
	work     workload.Options
	parallel bool
	result   workload.Results
}

func (p DataPoints) SpeedupOver(other DataPoints) float64 {
	return float64(other.result.Elapsed()) / float64(p.result.Elapsed())
}

func (p DataPoints) MicrosPerOp() float64 {
	return float64(p.result.Elapsed().Nanoseconds()) / 1000 / float64(p.work.Kiters*1000)
}

func toSec(d time.Duration) float64 {
	return float64(d) / float64(time.Second)
}

func toMicros(d time.Duration) float64 {
	return float64(d) / float64(time.Microsecond)
}

func concat(lists ...[]interface{}) []interface{} {
	var flat []interface{}
	for _, list := range lists {
		flat = append(flat, list...)
	}
	return flat
}

var DataHeader = concat(
	[]interface{}{"fs"},
	filesys.DataHeader,
	workload.DataHeader,
	[]interface{}{
		"parallel",
		"timeSec",
	},
)

var ReadableDataHeader = concat(
	DataHeader,
	[]interface{}{
		"us/op",
	},
)

func (p DataPoints) dataRowPrefix() []interface{} {
	return concat(
		[]interface{}{p.fsIdent},
		p.fs.DataRow(),
		p.work.DataRow(),
		[]interface{}{
			p.parallel,
		},
	)
}

func (p DataPoints) DataRow(i int) []interface{} {
	return concat(
		p.dataRowPrefix(),
		[]interface{}{
			toSec(p.result.IterTimes[i]),
		},
	)
}

func (p DataPoints) ReadableDataRow() []interface{} {
	return concat(
		p.dataRowPrefix(),
		[]interface{}{
			toSec(p.result.Elapsed()), // add average time
			p.MicrosPerOp(),
		},
	)
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
		dataHeader := len(DataHeader)
		dataRow := len(DataPoints{result: workload.Results{
			IterTimes: []time.Duration{0},
		}}.DataRow(0))
		if dataRow != dataHeader {
			log.Fatal(fmt.Errorf("data header len != data row len (%d != %d)",
				dataHeader, dataRow))
		}
		printTsv(DataHeader...)
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

	data := DataPoints{
		fsIdent:  fs.Ident(),
		fs:       fsOpts,
		work:     opts,
		parallel: *parallel,
	}

	if *targetMs > 0 {
		data.result = opts.SearchWorkload(fs, *parallel, *targetMs)
	} else {
		data.result = opts.RunWorkload(fs, *parallel)
	}

	var seqData DataPoints
	if *parallel {
		seqData = DataPoints{
			fsIdent:  fs.Ident(),
			fs:       fsOpts,
			work:     opts,
			parallel: false,
		}
		seqData.result = opts.RunWorkload(fs, false)
	}

	fs.Stop()

	if *readable_output {
		row := data.ReadableDataRow()
		for i, hdr := range ReadableDataHeader {
			value := row[i]
			fmt.Printf("%-20s %v\n", hdr, value)
		}
		if *parallel {
			fmt.Printf("%-20s %v\n", "speedup", 2*data.SpeedupOver(seqData))
		}
	} else {
		for i := range data.result.IterTimes {
			printTsv(data.DataRow(i)...)
		}
		if *parallel {
			for i := range seqData.result.IterTimes {
				printTsv(seqData.DataRow(i)...)
			}
		}
	}
	return
}
