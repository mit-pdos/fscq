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
VS_XFORM   := $(patsubst %.v,coqbuild/%.v,$(VS))

.PHONY: coq clean

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
	python strip-proofs.py < $< > $@
	@touch -r $< $@

coq: Makefile.coq
	@mkdir -p codegen
	@ln -sf ../coqbuild codegen
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS_XFORM)
	coq_makefile -R coqbuild Fscq $(VS_XFORM) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf codegen coqbuild _build fstest hstest disk.img
