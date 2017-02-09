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
	fscq.Cache_read(&ret, &addr, &cs)
	return ret.Fst
}

func do_write(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	addr fscq.Num) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	new_cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	buf := fscq.New_Buffer(valulen)
	fscq.Cache_write(&new_cs, &addr, &buf, &cs)
	return new_cs
}

func do_sync(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	addr fscq.Num) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	new_cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	fscq.Cache_sync(&new_cs, &addr, &cs)
	return new_cs
}

func do_log_read(lxp fscq.Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num,
	addr fscq.Num,
	mscs fscq.Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_) fscq.Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	ret := fscq.New_Pair_Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct__Pair_Buffer_Struct_()
	fscq.Log_read(&ret, &lxp, &addr, &mscs)
	return ret.Fst
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

func exec_line_log(lxp fscq.Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num,
	mscs fscq.Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_,
	line string) fscq.Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	split := strings.Split(line, " ")
	switch split[0] {
	case "log_read":
		addr := fscq.Num_of_string(split[1])
		return do_log_read(lxp, addr, mscs)
	}
	return mscs
}

func exec_input(cs fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_) fscq.Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	scanner := bufio.NewScanner(os.Stdin)
	for scanner.Scan() {
		line := scanner.Text()
		cs = exec_line(cs, line)
	}
	return cs
}

func exec_input_log(lxp fscq.Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num, mscs fscq.Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_) fscq.Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_ {
	scanner := bufio.NewScanner(os.Stdin)
	for scanner.Scan() {
		line := scanner.Text()
		mscs = exec_line_log(lxp, mscs, line)
	}
	return mscs
}

func run_test(disk string) {
	fscq.Init_disk(disk)
	cs := fscq.New_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	cache_size := fscq.Num_of_i64(cachesize)
	fscq.Cache_init(&cs, &cache_size)
	cs = exec_input(cs)
}

func run_test_log(disk string) {
	fscq.Init_disk(disk)
	mscs := fscq.New_Pair_Pair_AddrMap_Buffer_Pair_Pair_AddrMap_Buffer_Slice_Slice_Pair_Num_Buffer_AddrMap_Buffer_Pair_Pair_AddrMap_Pair_Buffer_Bool_Num_Struct_()
	cache_size := fscq.Num_of_i64(cachesize)
	fscq.Cache_init(&mscs.Snd, &cache_size)
	lxp := fscq.New_Pair_Pair_Pair_Pair_Pair_Num_Num_Num_Num_Num_Num()
	lxp.Fst.Fst.Fst.Fst.Fst = 1
	lxp.Fst.Fst.Fst.Fst.Snd = 1 + (32768 + 1024 + 1 + 1) + 1
	lxp.Fst.Fst.Fst.Snd = 1 + (32768 + 1024 + 1 + 1) + 1 + 1
	lxp.Fst.Fst.Snd = 1
	lxp.Fst.Snd = 1 + (32768 + 1024 + 1 + 1) + 1 + 1 + 1
	lxp.Snd = 32768 / 64
	mscs = exec_input_log(lxp, mscs)
}

func main() {
	if len(os.Args) >= 2 {
		// run_test(os.Args[1])
		run_test_log(os.Args[1])
	} else {
		fmt.Println("Usage: hscache_test disk")
	}
}
