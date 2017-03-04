package main

import (
	"filesys"
	"flag"
	"fmt"
	"log"
	"pin"
	"strings"
	"time"
	"workload"

	"github.com/montanaflynn/stats"
)

type DataPoints struct {
	fsIdent  string
	fs       filesys.Options
	work     workload.Options
	workIdx  int
	parallel int
	result   workload.Results
}

func (p DataPoints) SpeedupOver(other DataPoints) float64 {
	return float64(other.result.Elapsed()) / float64(p.result.Elapsed())
}

func (p DataPoints) MicrosPerOp() float64 {
	return float64(p.result.Elapsed().Nanoseconds()) / 1000 / float64(p.work.NumOperations())
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
		"work_idx",
		"parallel",
		"run_idx",
		"timeSec",
	},
)

var ReadableDataHeader = concat(
	DataHeader,
	[]interface{}{
		"us/op",
	},
)

// produce data row from beginning until parallel (excluding information for a
// particular row, namely idx and time)
func (p DataPoints) dataRowPrefix() []interface{} {
	return concat(
		[]interface{}{p.fsIdent},
		p.fs.DataRow(),
		p.work.DataRow(),
		[]interface{}{
			p.workIdx,
			p.parallel,
		},
	)
}

func (p DataPoints) DataRow(i int) []interface{} {
	return concat(
		p.dataRowPrefix(),
		[]interface{}{
			i,
			toSec(p.result.IterTimes[i]),
		},
	)
}

func (p DataPoints) ReadableDataRow() []interface{} {
	return concat(
		p.dataRowPrefix(),
		[]interface{}{
			0, // run index
			toSec(p.result.Elapsed()), // add average time
			p.MicrosPerOp(),
		},
	)
}

func summarizeDataPoints(ps []DataPoints) (header []interface{}, data []interface{}) {
	header = concat(
		[]interface{}{
			"work_iters",
			"us/op std",
			"us/op mean",
			"us/op min",
			"us/op median",
		},
	)

	var times []float64
	for _, p := range ps {
		times = append(times, p.MicrosPerOp())
	}
	timeMean, _ := stats.Mean(times)
	timeMedian, _ := stats.Median(times)
	timeMin, _ := stats.Min(times)
	timeStd, _ := stats.StandardDeviationPopulation(times)
	data = append(data, len(ps), timeStd, timeMean, timeMin, timeMedian)

	return
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
	parallel := flag.Int("parallel", 1, "number of parallel clients")
	reps := flag.Int("reps", 1000, "repetitions to use per iteration")
	iters := flag.Int("iters", 1, "number of iterations (of reps) to run the operation")
	work_iters := flag.Int("work_iters", 1, "repetitions of the entire workload")
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
	rts_opts := flag.String("rts-opts", "",
		"space-separated arguments to pass to fuse server in +RTS -RTS")
	warmup := flag.Bool("warmup", true, "warmup file system with 1000 untimed iterations")

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

	var rtsOpts []string
	if *rts_opts != "" {
		rtsOpts = strings.Split(*rts_opts, " ")
	}

	fsOpts := filesys.Options{
		NameCache:    *name_cache,
		NegNameCache: *neg_name_cache,
		AttrCache:    *attr_cache,
		KernelCache:  *kernel_cache,
		ServerCpu:    pin.Cpu(*server_cpu),
		RtsOpts:      rtsOpts,
	}

	opts := workload.Options{
		Operation:           *operation,
		ClientCpus:          pin.NewCpus(*client_cpus, *parallel),
		ExistingPath:        *existingPath,
		DisjointDirectories: *disjointDirectories,
		Reps:                *reps,
		Iters:               *iters,
	}

	var data_iters []DataPoints

	for i := 0; i < *work_iters; i++ {
		fs.Launch(fsOpts)
		if *warmup {
			opts.Warmup(fs)
		}

		var results workload.Results

		if *targetMs > 0 {
			results = opts.SearchWorkload(fs, *parallel, *targetMs)
		} else {
			results = opts.RunWorkload(fs, *parallel)
		}

		data := DataPoints{
			fsIdent:  fs.Ident(),
			fs:       fsOpts,
			work:     opts,
			workIdx:  i,
			parallel: *parallel,
			result:   results,
		}

		fs.Stop()
		data_iters = append(data_iters, data)
	}

	if *readable_output {
		data := data_iters[0]
		var header []interface{}
		header = append(header, ReadableDataHeader...)
		row := data.ReadableDataRow()
		if *work_iters > 1 {
			extraHeader, extraRow := summarizeDataPoints(data_iters)
			header = append(header, extraHeader...)
			row = append(row, extraRow...)
		}
		for i, hdr := range header {
			value := row[i]
			fmt.Printf("%-20s %v\n", hdr, value)
		}
		if *parallel > 1 {
			fs.Launch(fsOpts)
			opts.Warmup(fs)
			seqData := DataPoints{
				fsIdent:  data.fsIdent,
				fs:       data.fs,
				work:     data.work,
				parallel: 1,
				result:   opts.RunWorkload(fs, 1),
			}
			fmt.Printf("%-20s %v\n", "seq us/op", seqData.MicrosPerOp())
			fmt.Printf("%-20s %v\n", "speedup", (float64(*parallel) * data.SpeedupOver(seqData)))
			fs.Stop()
		}
	} else {
		for _, data := range data_iters {
			for i := range data.result.IterTimes {
				printTsv(data.DataRow(i)...)
			}
		}
	}

	return
}
