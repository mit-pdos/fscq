OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Lock Nomega Word WordAuto WordZ Bytes \
	      Prog Pred Hoare SepAuto SepAuto2 Idempotent \
	      BasicProg Array AddrMap Rec RecArray \
	      GenSep GenSepN ListPred Cache FSLayout \
	      Log Balloc Inode BFile BFileRec Dir \
	      MemMatch DirName DirTree FS Testprog \
	      ExtrHaskellPrelude Extraction ExtractJSON
VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
GHC        := /opt/ghc/7.10.1/bin/ghc
GHCARGS    := -O2 -threaded
		# -prof -fprof-auto -rtsopts
		# -eventlog
HSLIB_PRE  := hslib/Word.hs hslib/Evict.hs hslib/Profile.hs
HSLIB_POST := hslib/Disk.hs hslib/Interpreter.hs

.PHONY: coq proof clean

all: hstest fuse mkfs

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

coq: Makefile.coq
	$(MAKE) -f Makefile.coq quick

checkproofs: Makefile.coq
	$(MAKE) -f Makefile.coq checkproofs J=$(J)

proof: Makefile.coq
	$(MAKE) -f Makefile.coq

parproof: coq
	$(MAKE) -f Makefile.coq vio2vo J=$(J)

coqbuild/%.v: %.v
	@mkdir -p coqbuild
	ln -s ../$< $@

Makefile.coq: Makefile $(VS_BUILD)
	@mkdir -p codegen
	@ln -sf ../coqbuild codegen
	coq_makefile -R coqbuild Fscq $(VS_BUILD) -o Makefile.coq

%/main.go: %.json coq2go.py
	@mkdir -p $(@D)
	./coq2go.py $< > $(patsubst %/main.go,%/temp.go,$@)
	go fmt $(patsubst %/main.go,%/temp.go,$@)
	mv $(patsubst %/main.go,%/temp.go,$@) $@

gotest: $(patsubst %.json,%/main.go,$(wildcard codegen/*.json))
	GOPATH=$(shell cd .. && pwd):${GOPATH} go build gotest.go

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf codegen coqbuild _build fstest hstest gotest disk.img
