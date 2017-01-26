package main

import (
	"gofscq"
	"fmt"
)

// Just for testing currently

func main() {
	a := fscq.New_Num()
	b := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty()
	c := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty()
	fmt.Println("Running fscq.Writeback(%v, %v, %v)", a, b, c)
	fscq.Writeback(&c, &a, &b)
	fmt.Println("Finished running fscq.Writeback")
}