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

func do_read(cs *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty,
	addr fscq.Num) *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty {
	ret := fscq.New_Pair_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty_Pair_Buffer_Empty()
	fscq.Read(&ret, &addr, &cs)
	return ret.Fst
}

func do_write(cs *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty,
	addr fscq.Num) *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty {
	new_cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty()
	buf := fscq.New_Buffer(valulen)
	fscq.Write(&new_cs, &addr, &buf, &cs)
	return new_cs
}

func do_sync(cs *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty,
	addr fscq.Num) *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty {
	new_cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty()
	fscq.Sync(&new_cs, &addr, &cs)
	return new_cs
}

func exec_line(cs *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty,
	line string) *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty {
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

func exec_input(cs *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty) *fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty {
	scanner := bufio.NewScanner(os.Stdin)
	for scanner.Scan() {
		line := scanner.Text()
		cs = exec_line(cs, line)
	}
	return cs
}

func run_test(disk string) {
	fscq.Init_disk(disk)
	cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Empty()
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
