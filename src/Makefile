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

EXTRACT_MODULES := Wrappers \
					ExtractCache ExtractDiskLogHash \
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

GO_LIB_MOD	:= disk map map_test num util
GO_LIB		:= $(GO_LIB_MOD:%=golib/%.go)
GO_LIB_INST := $(patsubst golib/%.go,codegen/src/gofscq/%.go,$(GO_LIB))

GO_EX		:= golib/fscq.go
GO_EX_INST	:= $(patsubst golib/%.go,codegen/src/fscq/%.go,$(GO_EX))

.PHONY: coq proof clean

 # this is just so "make" rebuilds the .vio files and is temporary
all: fscq

fscq: $(GO_LIB_INST) $(GO_EX_INST) codegen/src/gofscq/fscq.go
	go install ./codegen/src/gofscq
	go install ./codegen/src/fscq
	cp codegen/bin/fscq fscq

codegen/%.ml: %.ml
	ln -s ../$< $@

$(GOCAML_ML): $(VS_VIO) $(EXTRACT_VIO)
	mkdir -p codegen/Extract
	( cd coqbuild && coqc -q -R . Fscq Extract/ExtractGOcaml )

codegen/src/gofscq/%.go : golib/%.go
	@mkdir -p $(dir $@)
	ln -s $(abspath $<) $@

codegen/src/fscq/%.go: golib/%.go
	@mkdir -p $(dir $@)
	ln -s $(abspath $<) $@

codegen/src/gofscq/fscq.go: codegen/fscq2go.native
	@mkdir -p $(dir $@)
	$< > $@.tmp
	mv $@.tmp $@
	gofmt $@ > $@.fmt
	mv $@.fmt $@

codegen/fscq2go.native: $(GOCAML_ML) codegen/big.ml codegen/fscq2go.ml
	rm -f $@
	(cd codegen && ocamlbuild -cflag -g -lib nums -lib str -no-links fscq2go.native)
	cp codegen/_build/fscq2go.native $@

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
