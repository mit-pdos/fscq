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