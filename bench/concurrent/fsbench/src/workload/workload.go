package workload

import (
	"filesys"
	"fmt"
	"log"
	"os"
	"pin"
	"strconv"
	"strings"
	"time"
)

type Options struct {
	Operation           string
	ClientCpus          pin.CpuSpecs
	ExistingPath        bool
	DisjointDirectories bool
	Reps                int
	Iters               int
}

func (opts Options) NumOperations() int {
	return opts.Iters * opts.Reps
}

var DataHeader = []interface{}{
	"operation",
	"client-cpus",
	"exists",
	"disjoint-directories",
	"reps",
	"iters",
}

func (opts Options) DataRow() []interface{} {
	clientCpuSpec := fmt.Sprintf("\"%s\"", opts.ClientCpus.Spec())
	return []interface{}{
		opts.Operation, clientCpuSpec, opts.ExistingPath, opts.DisjointDirectories,
		opts.Reps, opts.Iters,
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

func (opts Options) RunWorkload(fs filesys.FileSystem, parallel int) Results {
	var paths []string
	for i := 0; i < parallel; i++ {
		var path string
		if opts.DisjointDirectories {
			path = fs.Pathname(i)
		} else {
			path = fs.Pathname(0)
		}
		if !opts.ExistingPath {
			path += "x"
		}
		paths = append(paths, path)
	}

	args := func(i int) []string {
		pwd := fs.MountPoint()
		path := strings.TrimPrefix(paths[i], pwd+"/")
		return []string{opts.Operation, pwd, path, strconv.Itoa(opts.Reps), strconv.Itoa(opts.Iters)}
	}

	done := make(chan Results)
	for i := 0; i < parallel; i++ {
		go func(i int) {
			cmd := opts.ClientCpus.Cpu(i).Command("fsops", args(i)...)
			cmd.Stderr = os.Stderr
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
	for i := 0; i < parallel; i++ {
		r = <-done
	}
	return r
}

func (opts Options) Warmup(fs filesys.FileSystem) {
	opts.Reps = 5
	opts.Iters = 1
	// TODO: really should go through all the filenames in fs and warm each
	// individually
	parallel := 1
	opts.RunWorkload(fs, parallel)
}

// SearchWorkload runs a workload, varying iters until the run takes at least targetMs milliseconds.
// The input opts should specify the workload parameters and initial kiters for
// the search. SearchWorkload returns the final duration and modifies the input
// opts to have the final iters.
func (opts *Options) SearchWorkload(fs filesys.FileSystem, parallel int, targetMs int) Results {
	targetTime := time.Duration(targetMs) * time.Millisecond
	result := opts.RunWorkload(fs, parallel)
	for result.Elapsed() < targetTime {
		last := opts.Iters
		// Predict required iterations
		iters := int(float64(last) * float64(targetTime) / float64(result.Elapsed()))
		// same policy as Go's testing/benchmark.go (see func (b *B) launch()): //
		// run 1.2x the iterations we estimate, but don't grow by more than 100x last
		// time and run at least one more iteration
		opts.Iters = max(min(iters+iters/5, 100*last), last+1)
		result = opts.RunWorkload(fs, parallel)
	}
	return result
}
