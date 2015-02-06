OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Nomega Word WordAuto \
	      Prog Pred Hoare SepAuto Idempotent \
	      BasicProg Array AddrMap Rec RecArray \
	      GenSep ListPred \
	      MemLog Balloc Inode BFile BFileRec Dir \
	      FS Testprog \
	      ExtrHaskellPrelude Extraction
	      # TxnWrap Scratch
VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
VS_PROOF   := $(patsubst %.v,coqproof/%.v,$(VS))
GHC        := /opt/ghc/7.8.4/bin/ghc
GHCARGS    := -O2 -prof -fprof-auto -rtsopts
HSLIB_PRE  := hslib/Word.hs
HSLIB_POST := hslib/Disk.hs hslib/Interpreter.hs

.PHONY: coq proof clean

all: hstest fuse

%: %.ml coq
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@.native
	ln -s $(CURDIR)/_build/$@.native $@

%: %.hs coq
	test ! -f codegen/Word.hs || mv codegen/Word.hs codegen/.Word.hs
	$(GHC) $(GHCARGS) -Wall $(HSLIB_PRE)
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py codegen/*.hs -ihslib
	$(GHC) $(GHCARGS) -Wall $(HSLIB_POST) -ihslib -icodegen
	$(GHC) $(GHCARGS) -Wall $< -ihslib -icodegen -o $@

coqbuild/%.v: %.v strip-proofs.py
	@mkdir -p coqbuild
	python2 strip-proofs.py < $< > $@
	@touch -r $< $@

coqproof/%.v: %.v
	@mkdir -p coqproof
	cat < $< > $@
	@touch -r $< $@

coq: Makefile.coq
	@mkdir -p codegen
	@ln -sf ../coqbuild codegen
	$(MAKE) -f Makefile.coq

proof: Makefile.coqproof
	@mkdir -p codegen
	@ln -sf ../coqproof codegen
	$(MAKE) -f Makefile.coqproof

Makefile.coq: Makefile $(VS_BUILD)
	coq_makefile -R coqbuild Fscq $(VS_BUILD) -o Makefile.coq

Makefile.coqproof: Makefile $(VS_PROOF)
	coq_makefile -R coqproof Fscq $(VS_PROOF) -o Makefile.coqproof

clean:: Makefile.coq Makefile.coqproof
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.coqproof clean
	rm -f Makefile.coq
	rm -rf codegen coqbuild coqproof _build fstest hstest disk.img
