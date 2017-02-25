package workload

import (
	"filesys"
	"fmt"
	"log"
	"pin"
	"strconv"
	"strings"
	"time"
)

type Options struct {
	Operation           string
	ClientCpus          []pin.Cpu
	ExistingPath        bool
	DisjointDirectories bool
	Kiters              int
}

var DataHeader = []interface{}{
	"operation",
	"client-cpus",
	"exists",
	"disjoint-directories",
	"kiters",
}

func (opts Options) DataRow() []interface{} {
	clientCpuSpec := fmt.Sprintf("\"%s\"", pin.CpuSpec(opts.ClientCpus))
	return []interface{}{
		opts.Operation, clientCpuSpec, opts.ExistingPath, opts.DisjointDirectories, opts.Kiters,
	}
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

type Results struct {
	IterTimes []time.Duration
}

func (r Results) Elapsed() time.Duration {
	elapsed := time.Duration(0)
	for _, time := range r.IterTimes {
		elapsed += time
	}
	return elapsed
}

func (r *Results) Merge(other Results) {
	if other.Elapsed() > r.Elapsed() {
		r.IterTimes = other.IterTimes
	}
}

func (opts Options) RunWorkload(fs filesys.FileSystem, parallel bool) Results {
	copies := 1
	if parallel {
		copies = 2
	}
	var paths []string
	for i := 0; i < copies; i++ {
		var path string
		if opts.DisjointDirectories {
			path = fs.DisjointPath(i)
		} else {
			path = fs.Pathname()
		}
		if !opts.ExistingPath {
			path += "x"
		}
		paths = append(paths, path)
	}

	args := func(i int) []string {
		return []string{opts.Operation, paths[i], strconv.Itoa(opts.Kiters)}
	}

	done := make(chan Results)
	for i := 0; i < copies; i++ {
		go func(i int) {
			cmd := opts.ClientCpus[i].Command("fsops", args(i)...)
			outputBytes, err := cmd.Output()
			if err != nil {
				log.Fatal(fmt.Errorf("could not run fsops: %v", err))
			}
			output := strings.TrimRight(string(outputBytes), "\n")
			nums := strings.Split(output, "\n")
			var r Results
			for _, num := range nums {
				iterNs, err := strconv.ParseInt(num, 10, 64)
				if err != nil {
					log.Fatal(fmt.Errorf("could not parse iteration time %s", num))
				}
				r.IterTimes = append(r.IterTimes, time.Duration(iterNs))
			}
			done <- r
		}(i)
	}
	var r Results
	for i := 0; i < copies; i++ {
		r = <-done
	}
	return r
}

func (opts Options) Warmup(fs filesys.FileSystem) {
	opts.Kiters = 1
	parallel := false
	if opts.DisjointDirectories {
		parallel = true
	}
	opts.RunWorkload(fs, parallel)
}

// SearchWorkload runs a workload, varying kiters until the run takes at least targetMs milliseconds.
// The input opts should specify the workload parameters and initial kiters for
// the search. SearchWorkload returns the final duration and modifies the input
// opts to have the final kiters.
func (opts *Options) SearchWorkload(fs filesys.FileSystem, parallel bool, targetMs int) Results {
	targetTime := time.Duration(targetMs) * time.Millisecond
	result := opts.RunWorkload(fs, parallel)
	for result.Elapsed() < targetTime {
		last := opts.Kiters
		// Predict required iterations
		kiters := int(float64(last) * float64(targetTime) / float64(result.Elapsed()))
		// same policy as Go's testing/benchmark.go (see func (b *B) launch()): //
		// run 1.2x the iterations we estimate, but don't grow by more than 100x last
		// time and run at least one more iteration
		opts.Kiters = max(min(kiters+kiters/5, 100*last), last+1)
		result = opts.RunWorkload(fs, parallel)
	}
	return result
}
