OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Nomega Word \
	      Prog Pred Hoare SepAuto BasicProg \
	      Log \
	      ExtrHaskellPrelude Extraction
	      # MemLog TxnWrap Scratch
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

all: hstest

%: %.ml coq
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@.native
	ln -s $(CURDIR)/_build/$@.native $@

%: %.hs coq
	ghc -F -pgmF ./fix_extraction.py codegen/*.hs $< -o $@

coq: Makefile.coq
	@mkdir -p codegen
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Fscq $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf codegen _build fstest hstest disk.img
