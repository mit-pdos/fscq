COQINC = -I .
COQEXE = coqtop $(COQINC) -batch -load-vernac-source
COQC = coqc $(COQINC)
COQDEP = coqdep $(COQINC)

OCAMLBUILD = ocamlbuild -lib str
OCAMLINC   = \
    -I codegen -I compcert/extraction \
    -I compcert/lib -I compcert/common

FILES = CpdtTactics.v \
	FsTactics.v \
	Storage.v \
	Closures.v \
	Bank.v \
	Trans.v \
	DiskLog.v

PROOFFILES = 

all:	tests/fs.native

tests/%.native: tests/%.ml codegen/extraction.vo
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@
	ln -s $(CURDIR)/_build/$@ $@

codegen/extraction.vo: $(FILES:.v=.vo)

proof: $(PROOFFILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

depend: $(FILES)
	$(COQDEP) $^ \
	> .depend

clean:
	rm -rf _build *.vo *.glob build/*.native
	cd codegen && rm -f *.ml *.mli *.mlo *.glob *.vo

include .depend
