package pin

import (
	"fmt"
	"os/exec"
	"strings"
)

// A Cpu is a specification of CPUs in the form expected by taskset (numerical
// list, separated by commas, including ranges)
type Cpu string

type CpuSpecs struct {
	specsString string
	parsed      []Cpu
}

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
func NewCpus(specsString string, parallel int) CpuSpecs {
	specs := strings.Split(specsString, "/")
	var cpus []Cpu
	for i := 0; i < parallel; i++ {
		cpus = append(cpus, Cpu(specs[i%len(specs)]))
	}
	return CpuSpecs{specsString, cpus}
}

func (specs CpuSpecs) Spec() string {
	return specs.specsString
}

func (specs CpuSpecs) Cpu(i int) Cpu {
	return specs.parsed[i]
}
