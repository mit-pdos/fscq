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
func NewCpus(specsString string) []Cpu {
	specs := strings.SplitN(specsString, "/", 2)
	if len(specs) == 1 {
		spec := Cpu(specs[0])
		return []Cpu{spec, spec}
	}
	return []Cpu{Cpu(specs[0]), Cpu(specs[1])}
}

func CpuSpec(specs []Cpu) string {
	var specStrings []string
	for _, spec := range specs {
		specStrings = append(specStrings, string(spec))
	}
	return strings.Join(specStrings, "/")
}
