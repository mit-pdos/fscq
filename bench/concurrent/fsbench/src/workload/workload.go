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

type Result struct {
	Elapsed time.Duration
	// stddev of per operation time
	Stddev time.Duration
}

func (opts Options) RunWorkload(fs filesys.FileSystem, parallel bool) Result {
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

	done := make(chan runResult)
	for i := 0; i < copies; i++ {
		go func(i int) {
			cmd := opts.ClientCpus[i].Command("fsops", args(i)...)
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
	return Result{
		time.Duration(int64(elapsedTime)),
		time.Duration(int64(iterStddev)),
	}
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
func (opts *Options) SearchWorkload(fs filesys.FileSystem, parallel bool, targetMs int) Result {
	targetTime := time.Duration(targetMs) * time.Millisecond
	result := opts.RunWorkload(fs, parallel)
	for result.Elapsed < targetTime {
		last := opts.Kiters
		// Predict required iterations
		kiters := int(float64(last) * float64(targetTime) / float64(result.Elapsed))
		// same policy as Go's testing/benchmark.go (see func (b *B) launch()): //
		// run 1.2x the iterations we estimate, but don't grow by more than 100x last
		// time and run at least one more iteration
		opts.Kiters = max(min(kiters+kiters/5, 100*last), last+1)
		result = opts.RunWorkload(fs, parallel)
	}
	return result
}
