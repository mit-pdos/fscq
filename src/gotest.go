package main

import . "gocoq"
import "codegen/Word"
import "codegen/Prog"
import "codegen/FS"
import "codegen/Datatypes"
import "codegen/Nat"
import "fmt"

var tt CoqT = &Datatypes.Coq_Coq_tt{}

func run_dprog(p CoqT) CoqT {
  switch t := p.(type) {
  case *Prog.Coq_Done:
    return t.A0

  case *Prog.Coq_Read:
    read_addr := t.A0
    rx := t.A1
    fmt.Printf("Read (%v)..\n", read_addr)

    // XXX synthesizing garbage..
    data := CoqApply(Word.Coq_natToWord, Nat.Uint2nat(0))

    return run_dprog(CoqApply(rx, data))

  case *Prog.Coq_Write:
    write_addr := t.A0
    write_data := t.A1
    rx := t.A2
    fmt.Printf("Write (%v, %v)..\n", write_addr, write_data)
    return run_dprog(CoqApply(rx, tt))

  case *Prog.Coq_Sync:
    sync_addr := t.A0
    rx := t.A1
    fmt.Printf("Sync (%v)..\n", sync_addr)
    return run_dprog(CoqApply(rx, tt))

  default:
    panic("bad type")
  }
}

func rx_done(arg CoqT) CoqT {
  return &Prog.Coq_Done{arg}
}

func main() {
  fmt.Println("Hello world!")

  var data_bitmaps CoqT = CoqApply(Word.Coq_wone, Prog.Coq_addrlen)
  var inode_bitmaps CoqT = CoqApply(Word.Coq_wone, Prog.Coq_addrlen)

  run_dprog(CoqApply(CoqApply(CoqApply(FS.Coq_mkfs, data_bitmaps),
                              inode_bitmaps), rx_done))
}
