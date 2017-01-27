package fscq

import (
	"strconv"
)

type Num uint64

func (n Num) String() string {
	return strconv.FormatUint(uint64(n), 10)
}

func New_Num() Num {
	return 0
}

func test_eq_Num(l Num, r Num) Bool {
	return Bool(l == r)
}

func test_ne_Num(l Num, r Num) Bool {
	return Bool(l != r)
}

func test_lt_Num(l Num, r Num) Bool {
	return Bool(l < r)
}

func test_le_Num(l Num, r Num) Bool {
	return Bool(l <= r)
}

func (num Num) DeepCopy() Num {
	return num
}

func Num_of_i64(num int64) Num {
	return Num(num)
}

func Num_of_string(str string) Num {
	n, err := strconv.ParseUint(str, 10, 64)
	if err != nil {
		panic(err)
	}
	return Num(n)
}

func (n Num) Cmp(x Num) int {
	if n < x {
		return -1
	} else if n > x {
		return 1
	} else {
		return 0
	}
}

func (n *Num) Add(x Num, y Num) {
	*n = x + y
	if *n < x {
		panic("overflow")
	}
}

func (n *Num) Multiply(x Num, y Num) {
	*n = x * y
	if x != 0 && y != 0 && *n/x != y {
		panic("overflow")
	}
}

func (n *Num) Increment() {
	*n += 1
	if *n == 0 {
		panic("overflow")
	}
}

func (n *Num) Decrement() {
	if *n == 0 {
		panic("overflow")
	}
	*n -= 1
}

func (n *Num) Int64() int64 {
	return int64(*n)
}
