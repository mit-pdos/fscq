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
	      GoTactics1 GoHoare GoTactics2 GoSepAuto GoCompilationLemmas GoOfWord GoExtraction GoExamples
VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
VS_VIO	   := $(patsubst %.v,coqbuild/%.vio,$(VS))

EXTRACT_MODULES := Wrappers \
	        EnvBuild \
		ExtractCache \
		ExtractBalloc \
		ExtractBFile \
		ExtractDirTree \
		ExtractAsyncFS \
		ExtractInode \
		ExtractInodeGetLen \
		ExtractLog \
		ExtractGroupLog \
		ExtractMemLog \
		GoExtracted
EXTRACT_VS 		:= $(EXTRACT_MODULES:%=Extract/%.v)
EXTRACT_BUILD   := $(patsubst %.v,coqbuild/%.v,$(EXTRACT_VS))
EXTRACT_VIO     := $(patsubst %.v,coqbuild/%.vio,$(EXTRACT_VS))

VS_HS      := codegen/AsyncFS.hs
GHC 	   := ghc
HSC2HS	   := hsc2hs
ifeq (,$(shell $(GHC) --version | grep 'version 8.0' 2>/dev/null))
	GHC := /opt/ghc/8.0.1/bin/ghc
	HSC2HS := /opt/ghc/8.0.1/bin/hsc2hs
endif

J	   ?= 1
GHCARGS    := -O2 -threaded
		# -prof -fprof-auto -rtsopts
		# -eventlog
HSLIB_FUSE := hscgen/Fuse.hs
HSLIB_PRE  := hslib/Word.hs hslib/Evict.hs hslib/Profile.hs
HSLIB_POST := hslib/Disk.hs hslib/Interpreter.hs

GOCAML_MOD := Ascii BinInt BinNat BinNums BinPos Datatypes \
	            FMapAVL FMapList Int List0 Nat0 OrderedTypeEx OrderedType \
              Orders OrdersTac PeanoNat Specif String0 \
				 StringMap

GOCAML_ML := $(GOCAML_MOD:%=codegen/%.ml)

GO_LIB_MOD	:= disk map map_test num util
GO_LIB		:= $(GO_LIB_MOD:%=golib/%.go)
GO_LIB_INST := $(patsubst golib/%.go,codegen/src/gofscq/%.go,$(GO_LIB))

GO_EX		:= golib/fscq.go golib/hscache-test.go
GO_EX_INST	:= $(patsubst golib/%.go,codegen/src/fscq/%.go,$(GO_EX))

GO := GOPATH=`pwd`/codegen/ go

.PHONY: coq proof clean

 # this is just so "make" rebuilds the .vio files and is temporary
all: fscq

fscq: $(GO_LIB_INST) $(GO_EX_INST) codegen/src/gofscq/fscq.go
	$(GO) install ./codegen/src/gofscq
	$(GO) build codegen/src/fscq/fscq.go

go_hscache_test: $(GO_LIB_INST) $(GO_EX_INST) codegen/src/gofscq/fscq.go
	$(GO) install ./codegen/src/gofscq
	$(GO) build codegen/src/fscq/hscache-test.go
	mv hscache-test go_hscache_test

codegen/%.ml: %.ml
	ln -s ../$< $@

$(GOCAML_ML): $(VS_VIO) $(EXTRACT_VIO) coqbuild/Extract/ExtractGOcaml.v
	mkdir -p codegen/Extract
	( cd coqbuild && coqc -q -R . Fscq Extract/ExtractGOcaml )

codegen/src/gofscq/%.go : golib/%.go
	@mkdir -p $(dir $@)
	ln -s $(abspath $<) $@

codegen/src/fscq/%.go: golib/%.go
	@mkdir -p $(dir $@)
	ln -s $(abspath $<) $@

codegen/src/gofscq/fscq.go: codegen/fscq2go.byte
	@mkdir -p $(dir $@)
	$< > $@.tmp
	mv $@.tmp $@
	gofmt $@ > $@.fmt
	mv $@.fmt $@

codegen/fscq2go.native: $(GOCAML_ML) codegen/big.ml codegen/fscq2go.ml
	rm -f $@
	(cd codegen && ocamlbuild -cflag -g -lib nums -lib str -no-links fscq2go.native)
	cp codegen/_build/fscq2go.native $@

codegen/fscq2go.byte: $(GOCAML_ML) codegen/big.ml codegen/fscq2go.ml
	rm -f $@
	(cd codegen && ocamlbuild -cflag -g -tag debug -lib nums -lib str -no-links fscq2go.byte)
	cp codegen/_build/fscq2go.byte $@

$(VS_JSON): $(VS_VIO) coqbuild/ExtractJSON.v
	( cd coqbuild && coqc -q -R . Fscq ExtractJSON )

hscgen/%.hs: hslib/%.hsc
	@mkdir -p $(@D)
	$(HSC2HS) $< -o $@ --cflag=-D_FILE_OFFSET_BITS=64

%: %.hs $(VS_HS) $(HSLIB_FUSE)
	test ! -f codegen/Word.hs || mv codegen/Word.hs codegen/.Word.hs
	$(GHC) $(GHCARGS) $(HSLIB_FUSE)
	$(GHC) $(GHCARGS) -Wall $(HSLIB_PRE)
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py codegen/*.hs -ihslib
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $(HSLIB_POST) -ihslib -icodegen
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $< -ihslib -icodegen -ihscgen -optl -lfuse -o $@

$(VS_HS): $(VS_VIO) coqbuild/ExtractHaskell.v
	( cd coqbuild && coqc -q -R . Fscq ExtractHaskell )

$(VS_VIO) $(EXTRACT_VIO): coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -j $(J) -f Makefile.coq quick )
	@touch coqbuild/*.vio
	@touch coqbuild/Extract/*.vio

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
