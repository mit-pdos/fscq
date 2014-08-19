OCAMLBUILD := ocamlbuild -lib str
OCAMLINC   := -I codegen
MODULES    := Prog Pred Hoare SepAuto BasicProg Log TxnWrap Extraction Scratch
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

all: fstest.native

%.native: %.ml coq
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@
	ln -s $(CURDIR)/_build/$@ $@

coq: Makefile.coq
	@mkdir -p codegen
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf codegen _build *.native disk.img
