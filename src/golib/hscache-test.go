package main

import (
	"bufio"
	"fmt"
	"gofscq"
	"os"
	"strings"
)

const cachesize = 100000

var valulen = fscq.Num_of_i64(4096)

func do_read(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	addr fscq.Num) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	ret := fscq.New_Pair_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct__Pair_Buffer_Struct_()
	fscq.Read(&ret, &addr, &cs)
	return ret.Fst
}

func do_write(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	addr fscq.Num) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	new_cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	buf := fscq.New_Buffer(valulen)
	fscq.Write(&new_cs, &addr, &buf, &cs)
	return new_cs
}

func do_sync(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	addr fscq.Num) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	new_cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	fscq.Sync(&new_cs, &addr, &cs)
	return new_cs
}

func exec_line(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	line string) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	split := strings.Split(line, " ")
	switch split[0] {
	case "write":
		addr := fscq.Num_of_string(split[1])
		return do_write(cs, addr)
	case "read":
		addr := fscq.Num_of_string(split[1])
		return do_read(cs, addr)
	case "sync":
		addr := fscq.Num_of_string(split[1])
		return do_sync(cs, addr)
	}
	return cs
}

func exec_input(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	scanner := bufio.NewScanner(os.Stdin)
	for scanner.Scan() {
		line := scanner.Text()
		cs = exec_line(cs, line)
	}
	return cs
}

func run_test(disk string) {
	fscq.Init_disk(disk)
	cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	cache_size := fscq.Num_of_i64(cachesize)
	fscq.Init(&cs, &cache_size)
	cs = exec_input(cs)
}

func main() {
	if len(os.Args) >= 2 {
		run_test(os.Args[1])
	} else {
		fmt.Println("Usage: hscache_test disk")
	}
}
