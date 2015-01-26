OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Nomega Word WordAuto \
	      Prog Pred Hoare SepAuto Idempotent \
	      BasicProg Array AddrMap Rec RecArray \
	      GenSep ListPred \
	      Log Balloc Inode File Dir \
	      Testprog \
	      ExtrHaskellPrelude Extraction
	      # MemLog TxnWrap Scratch
VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
VS_PROOF   := $(patsubst %.v,coqproof/%.v,$(VS))

.PHONY: coq proof clean

all: hstest

%: %.ml coq
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@.native
	ln -s $(CURDIR)/_build/$@.native $@

%: %.hs coq
	mv codegen/Word.hs codegen/.Word.hs
	ghc -Wall -O2 hslib/*.hs
	ghc -O2 codegen/*.hs -ihslib
	ghc -Wall -O2 $< -ihslib -icodegen -o $@

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
