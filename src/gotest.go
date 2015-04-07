package main

import . "gocoq"
import "codegen/Datatypes"
import "codegen/Word"
import "codegen/Prog"
import "codegen/FS"
import "fmt"

func run_dprog(p CoqT) CoqT {
  switch t := p.(type) {
  case *Prog.Coq_Done:
    return t.A0
  case *Prog.Coq_Read:
    fmt.Println("Read..")
    return nil
  case *Prog.Coq_Write:
    fmt.Println("Write..")
    return nil
  case *Prog.Coq_Sync:
    fmt.Println("Sync..")
    return nil
  default:
    panic("bad type")
  }
}

func int2nat(n int) CoqT {
  if (n <= 0) {
    return &Datatypes.Coq_O{}
  } else {
    return &Datatypes.Coq_S{int2nat(n-1)}
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
