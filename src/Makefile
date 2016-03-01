OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Nomega Word WordAuto WordZ Bytes Rounding \
	      Mem Pred Prog PredCrash Hoare \
	      SepAuto SepAuto2 Idempotent Errno \
	      BasicProg Array AddrMap Rec RecArray \
	      GenSep GenSepN ListPred Cache FSLayout \
	      Log Balloc Inode BFile BFileRec Dir \
	      MemMatch DirName DirTree ByteFile FS Testprog \
	      Hlist HlistMem Star RelationCombinators Variables EventCSL EventCSLauto \
	      Locking Preservation Automation MemCache ForwardChaining \
	      Bank MemCache ConcurrentCache TwoBlockExample \
	      ExtrHaskellPrelude Extraction
VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
GHC 	   := ghc
ifeq (,$(shell $(GHC) --version | grep 'version 7.10' 2>/dev/null))
	GHC := /opt/ghc/7.10.2/bin/ghc
endif

GHCARGS    := -O2 -threaded
		# -prof -fprof-auto -rtsopts
		# -eventlog
HSLIB_PRE  := hslib/Word.hs hslib/Evict.hs hslib/Profile.hs
HSLIB_POST := hslib/Disk.hs hslib/Interpreter.hs hslib/ConcurInterp.hs
J ?= 4

.PHONY: coq proof clean

all: hstest

%: %.ml coq
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@.native
	ln -s $(CURDIR)/_build/$@.native $@

%: %.hs coq
	test ! -f codegen/Word.hs || mv codegen/Word.hs codegen/.Word.hs
	$(GHC) $(GHCARGS) -Wall $(HSLIB_PRE)
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py codegen/*.hs -ihslib
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $(HSLIB_POST) -ihslib -icodegen
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $< -ihslib -icodegen -o $@

coq: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq quick )

checkproofs: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq checkproofs J=$(J) )

proof: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq )

parproof: coq
	( cd coqbuild && $(MAKE) -f Makefile.coq vio2vo J=$(J) )

coqbuild/%.v: %.v
	@mkdir -p coqbuild
	ln -s ../$< $@

coqbuild/Makefile.coq: Makefile $(VS_BUILD)
	@mkdir -p codegen
	@mkdir -p coqbuild
	@ln -sf ../coqbuild codegen
	( cd coqbuild && coq_makefile -R . Fscq $(VS) -o Makefile.coq )

%/main.go: %.json coq2go.py
	@mkdir -p $(@D)
	./coq2go.py $< > $(patsubst %/main.go,%/temp.go,$@)
	go fmt $(patsubst %/main.go,%/temp.go,$@)
	mv $(patsubst %/main.go,%/temp.go,$@) $@

gotest: $(patsubst %.json,%/main.go,$(wildcard codegen/*.json))
	GOPATH=$(shell cd .. && pwd):${GOPATH} go build gotest.go

clean:
	rm -rf codegen coqbuild _build fstest hstest gotest disk.img
