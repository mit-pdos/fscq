package fscq

type Empty struct{}

func (x Empty) DeepCopy() *Empty {
	return &x
}

func New_bool() bool {
	return false
}

func New_Empty() Empty {
	var e Empty
	return e
}