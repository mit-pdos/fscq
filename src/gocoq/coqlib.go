package gocoq

type CoqT interface{}

var CoqDummy CoqT = nil

func CoqApply(f CoqT, arg CoqT) CoqT {
  return f.(func (CoqT) CoqT)(arg)
}
