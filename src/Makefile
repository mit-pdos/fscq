OCAMLBUILD := ocamlbuild \
	      -lib str -lib nums
MODULES    := Lock Nomega Word WordAuto WordZ Bytes Rounding \
	      Mem AsyncDisk Pred Prog ProgMonad PredCrash Hoare \
	      Hashmap HashmapProg \
	      SepAuto Idempotent Errno \
	      BasicProg ListUtils MapUtils Array Rec RecArrayUtils \
	      MemPred Cache \
	      FSLayout AsyncRecArray DiskLogHash \
	      LogReplay MemLog ListPred GenSepN \
	      NEList DiskSet GroupLog Log LogRecArray \
	      Balloc BlockPtr GenSepAuto Inode BFile MemMatch FileRecArray \
	      Dir DirName StringUtils TreeUtils DirTree TreeCrash \
	      SuperBlock AsyncFS AsyncFSRecover VBConv ADestructPair DestructVarname ExtrHaskellPrelude \
	      DirSep TreeSeq \
				MoreMapFacts StringMap VerdiTactics Gensym GoSemantics GoFacts \
				GoTactics1 GoHoare GoTactics2 GoSepAuto GoCompilationLemmas GoExtraction GoExamples
VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
VS_VIO	   := $(patsubst %.v,coqbuild/%.vio,$(VS))

EXTRACT_MODULES := ExtractCache \
					ExtractGOcaml GoExtracted
EXTRACT_VS 		:= $(EXTRACT_MODULES:%=Extract/%.v)
EXTRACT_BUILD   := $(patsubst %.v,coqbuild/%.v,$(EXTRACT_VS))
EXTRACT_VIO     := $(patsubst %.v,coqbuild/%.vio,$(EXTRACT_VS))

J	   ?= 1

GOCAML_MOD := Ascii BinInt BinNat BinNums BinPos Datatypes \
	            FMapAVL FMapList Int List0 Nat0 OrderedTypeEx OrderedType \
              Orders OrdersTac PeanoNat Specif String0 \
				 StringMap

GOCAML_ML := $(GOCAML_MOD:%=codegen/%.ml)

.PHONY: coq proof clean

all: codegen/fscq2go # this is just so "make" rebuilds the .vio files and is temporary

codegen/%.ml: %.ml
	ln -s ../$< $@

$(GOCAML_ML): $(VS_VIO) $(EXTRACT_VIO)
	mkdir -p codegen/Extract
	( cd coqbuild && coqc -q -R . Fscq Extract/ExtractGOcaml )

$(GOPATH)/src/gobuild/cache.go:
	true

codegen/fscq2go: $(GOCAML_ML) codegen/big.ml codegen/fscq2go.ml
	rm -f $@ $@.native
	(cd codegen && ocamlbuild -cflag -g -lib nums -lib str fscq2go.native)
	test -f $@.native && ln -s fscq2go.native $@

$(VS_JSON): $(VS_VIO) coqbuild/ExtractJSON.v
	( cd coqbuild && coqc -q -R . Fscq ExtractJSON )

$(VS_VIO): coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -j $(J) -f Makefile.coq quick )
	@touch coqbuild/*.vio

checkproofs: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq checkproofs J=$(J) )

proof: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq )

parproof: $(VS_VIO)
	( cd coqbuild && $(MAKE) -f Makefile.coq vio2vo J=$(J) )

coqbuild/%.v: %.v
	@mkdir -p $(dir $@)
	ln -s $(abspath $<) $@

coqbuild/Makefile.coq: Makefile $(VS_BUILD) $(EXTRACT_BUILD)
	@mkdir -p codegen
	@mkdir -p coqbuild
	@ln -sf ../coqbuild codegen
	( cd coqbuild && coq_makefile -R . Fscq $(VS) $(EXTRACT_VS) -o Makefile.coq )


clean:
	rm -rf codegen coqbuild _build fstest hstest gotest disk.img \
	       fuse mkfs *.o *.hi ocamlfuse/*.d ocamlfuse/*.di \
	       ocamlfuse/*.cmi ocamlfuse/*.cmx ocamlfuse/*.cmo \
	       ocamlfuse/*.o ocamlfuse/Fuse_bindings_stubs.c \
	       ocamlfuse/Fuse_bindings.h ocamlfuse/Fuse_bindings.ml \
	       ocamlfuse/libFuse_stubs.a

.PRECIOUS: hscgen/%.hs %_stubs.c
