package fscq

import(
	"math/big"
	)

type Num big.Int

func (n Num) String () string {
	return ((*big.Int) (&n)).String()
}

func New_Num() *Num {
	return new(Num)
}

func (n Num) DeepCopy () *Num {
	x := new(Num)
	*x = n
	return x
}

func (n Num) SetInt64(v int64) {
	((*big.Int) (&n)).SetInt64(v)
}

func test_eq_Num(l Num, r Num) Bool {
	return Bool((&l).Cmp(&r) == 0)
}

func test_ne_Num(l Num, r Num) Bool {
	return Bool((&l).Cmp(&r) != 0)
}

func test_lt_Num(l Num, r Num) Bool {
	return Bool((&l).Cmp(&r) < 0)
}

func test_le_Num(l Num, r Num) Bool {
	return Bool((&l).Cmp(&r) <= 0)
}

func big_of_i64 (num int64) Num {
	var x big.Int
	x.SetInt64(num)
	return Num(x)
}

func big_of_string (v string) Num {
	n := new(big.Int)
	n.SetString(v, 10)
	return Num(*n)
}

func (n *Num) Cmp (x *Num) int {
	return (*big.Int)(n).Cmp((*big.Int)(x))
}

func (n *Num) Add (x *Num, y *Num) {
	(*big.Int)(n).Add((*big.Int)(x), (*big.Int)(y))
}

func (n *Num) Increment() {
	one := big.Int(big_of_i64(1))
	(*big.Int)(n).Add((*big.Int)(n), &one)
}

func (n *Num) Decrement() {
	one := big.Int(big_of_i64(1))
	(*big.Int)(n).Sub((*big.Int)(n), &one)
}