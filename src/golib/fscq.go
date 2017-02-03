package main

import (
	"fmt"
	"gofscq"
)

// Just for testing currently

func main() {
	a := fscq.New_Num()
	b := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	c := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	fmt.Printf("Running fscq.Writeback(%v, %v, %v)\n", a, b, c)
	fscq.Writeback(&c, &a, &b)
	fmt.Println("Finished running fscq.Writeback")
}
