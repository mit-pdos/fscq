package pin

import (
	"fmt"
	"os/exec"
	"strings"
)

// A Cpu is a specification of CPUs in the form expected by taskset (numerical
// list, separated by commas, including ranges)
type Cpu string

func (spec Cpu) String() string {
	return fmt.Sprintf("\"%s\"", string(spec))
}

func (id Cpu) isPin() bool {
	return id != ""
}

func (id Cpu) Command(name string, args ...string) *exec.Cmd {
	if !id.isPin() {
		return exec.Command(name, args...)
	}
	tasksetArgs := []string{"-c", string(id), name}
	args = append(tasksetArgs, args...)
	return exec.Command("taskset", args...)
}

// NewCpus parses pipe-separated CPU specs
func NewCpus(specsString string, parallel int) []Cpu {
	specs := strings.SplitN(specsString, "/", parallel)
	var cpus []Cpu
	for i := 0; i < parallel; i++ {
		cpus = append(cpus, Cpu(specs[i%len(specs)]))
	}
	return cpus
}

func CpuSpec(specs []Cpu) string {
	var specStrings []string
	for _, spec := range specs {
		specStrings = append(specStrings, string(spec))
	}
	return strings.Join(specStrings, "/")
}
