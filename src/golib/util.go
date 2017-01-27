package fscq

import ()

type Bool bool

type Empty struct{}

func (x Empty) DeepCopy() Empty {
	return x
}

func New_Bool() Bool {
	return false
}

func New_Empty() Empty {
	var e Empty
	return e
}

func test_eq_Bool(l Bool, r Bool) Bool {
	return Bool(bool(l) == bool(r))
}

func test_ne_Bool(l Bool, r Bool) Bool {
	return Bool(bool(l) != bool(r))
}
