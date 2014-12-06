OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Nomega Word WordAuto \
	      Prog Pred Hoare SepAuto Idempotent \
	      BasicProg Array AddrMap Rec Pack RecArray \
	      Log Balloc Inode File Dir \
	      Testprog \
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
	mv codegen/Word.hs codegen/.Word.hs
	ghc -Wall -O2 hslib/*.hs
	ghc -O2 codegen/*.hs -ihslib
	ghc -Wall -O2 $< -ihslib -icodegen -o $@

coq: Makefile.coq
	@mkdir -p codegen
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Fscq $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf codegen _build fstest hstest disk.img
