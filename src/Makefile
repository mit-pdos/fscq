OCAMLBUILD := env OCAMLPATH=$(shell pwd) ocamlbuild \
	      -tag thread -tag debug -use-ocamlfind \
	      -lib str -lib nums \
	      -I codegen -I mllib -X ocamlfuse \
	      -package extunix -package zarith -package ocamlfuse
MODULES    := Lock Nomega Word WordAuto WordZ Bytes Rounding \
	      Mem Pred DestructVarname ADestructPair \
	      Errno \
	      ListUtils MapUtils Rec \
	      FSLayout \
	      ListPred FMapMem \
	      NEList \
	      \
	      PermAsyncDisk PermPredCrash \
	      PermArray PermRecArrayUtils PermAsyncRecArray \
	      PermProg PermHashmap PermBlockmem \
	      PermProgAuto PermSec \
	      PermProgMonad PermHoare PermSepAuto \
	      PermMemPred \
	      PermInstr PermProgLoop PermProgList \
              PermCacheDef PermCacheLemmas PermCacheSec PermCacheRangeSec \
	      PermDiskLogHdr PermDiskLogPadded PermDiskLog \
	      PermGenSepN PermLogReplay PermMemLog PermDiskSet

VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
VS_VIO	   := $(patsubst %.v,coqbuild/%.vio,$(VS))
VS_HS      := codegen/AsyncFS.hs
VS_ML      := codegen/AsyncFS.ml
VS_JSON    := codegen/AsyncFS.json
GHC 	   := ghc
HSC2HS	   := hsc2hs
ifeq (,$(shell $(GHC) --version 2>/dev/null | grep 'version 8.0' 2>/dev/null))
	GHC := /opt/ghc/8.0.1/bin/ghc
	HSC2HS := /opt/ghc/8.0.1/bin/hsc2hs
endif

J	   ?= 1
GHCARGS    := -j$(J) -O2 -threaded -rtsopts
		# -ticky -ticky-dyn-thunk -ticky-allocd
		# -prof -fprof-auto
		# -eventlog
HSLIB_FUSE := hscgen/Fuse.hs hslib/libopfuse.a
HSLIB_PRE  := hslib/Word.hs hslib/Evict.hs hslib/Profile.hs
HSLIB_POST := hslib/Disk.hs hslib/Interpreter.hs

OCAMLFUSE_ML	:= ocamlfuse/Result.ml \
		   ocamlfuse/Unix_util.ml \
		   ocamlfuse/Fuse_bindings.ml \
		   ocamlfuse/Fuse_lib.ml \
		   ocamlfuse/Fuse.ml
OCAMLFUSE_MLI	:= ocamlfuse/Fuse.mli \
		   ocamlfuse/Fuse_bindings.mli

OCAMLFUSE_CMX	:= $(patsubst %.ml,%.cmx,$(OCAMLFUSE_ML))
OCAMLFUSE_DEP	:= $(patsubst %.ml,%.d,$(OCAMLFUSE_ML)) \
		   $(patsubst %.mli,%.di,$(OCAMLFUSE_MLI))
OCAMLFUSE	:= ocamlfuse/Fuse.a ocamlfuse/Fuse.cmxa

.PHONY: coq proof clean

all: fscq mkfs

-include $(OCAMLFUSE_DEP)

%.mli %.ml %_stubs.c: %.idl
	camlidl -header $<

%.d: %.ml
	ocamldep $< > $@

%.di: %.mli
	ocamldep $< > $@

ocamlfuse/%.o: ocamlfuse/%.c
	ocamlc -c -ccopt '-fPIC -D_FILE_OFFSET_BITS=64 -I. -pthread -DPIC -DNATIVE_CODE -o $@' $<

ocamlfuse/libFuse_stubs.a: ocamlfuse/Fuse_bindings_stubs.o ocamlfuse/Unix_util_stubs.o ocamlfuse/Fuse_util.o
	ar rcs $@ $^

%.cmx: %.ml
	ocamlopt -I ocamlfuse -c -thread $<

%.cmi: %.mli
	ocamlopt -I ocamlfuse -c -thread $<

ocamlfuse/Fuse.cmxa ocamlfuse/Fuse.a: $(OCAMLFUSE_CMX) ocamlfuse/libFuse_stubs.a
	ocamlopt -a -thread -linkall -cclib -lFuse_stubs -cclib -lfuse -cclib -lcamlidl -o $@ $(OCAMLFUSE_CMX)

%: %.ml $(VS_ML) $(wildcard */*.ml) $(OCAMLFUSE)
	rm -f $@
	-mv codegen/Word.ml codegen/WordCoq.ml
	-mv codegen/Word.mli codegen/WordCoq.mli
	$(OCAMLBUILD) -no-links $@.native
	ln -s $(CURDIR)/_build/$@.native $@

hscgen/%.hs: hslib/%.hsc
	@mkdir -p $(@D)
	$(HSC2HS) $< -o $@ --cflag=-D_FILE_OFFSET_BITS=64 -Ihslib

%: %.hs $(VS_HS) $(HSLIB_PRE) $(HSLIB_POST) $(HSLIB_FUSE) fiximports.py
	test ! -f codegen/Word.hs || mv codegen/Word.hs codegen/.Word.hs
	$(GHC) $(GHCARGS) $(HSLIB_FUSE)
	$(GHC) $(GHCARGS) -Wall $(HSLIB_PRE)
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py codegen/*.hs -ihslib
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $(HSLIB_POST) -ihslib -icodegen
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $< -ihslib -icodegen -ihscgen -optl -lfuse -lopfuse -Lhslib -o $@

$(VS_HS): $(VS_VIO) coqbuild/ExtractHaskell.v
	( cd coqbuild && coqc -q -R . Fscq ExtractHaskell )

$(VS_ML): $(VS_VIO) coqbuild/ExtractOcaml.v
	( cd coqbuild && coqc -q -R . Fscq ExtractOcaml )

$(VS_JSON): $(VS_VIO) coqbuild/ExtractJSON.v
	( cd coqbuild && coqc -q -R . Fscq ExtractJSON )

$(VS_VIO): coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -j $(J) -f Makefile.coq quick ) #quick was here
	@touch coqbuild/*.vio

checkproofs: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq checkproofs J=$(J) )

proof: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -f Makefile.coq )

parproof: $(VS_VIO)
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

hslib/%.o: hslib/%.c
	$(CC) $^ -c -o $@ -O2 -Wall -Werror -D_FILE_OFFSET_BITS=64

hslib/libopfuse.a: hslib/opqueue.o hslib/opfuse.o
	ar rcs $@ $^

clean:
	rm -rf codegen coqbuild _build fstest hstest gotest disk.img \
	       fscq mkfs *.o *.hi ocamlfuse/*.d ocamlfuse/*.di \
	       ocamlfuse/*.cmi ocamlfuse/*.cmx ocamlfuse/*.cmo \
	       ocamlfuse/*.o ocamlfuse/Fuse_bindings_stubs.c \
	       ocamlfuse/Fuse_bindings.h ocamlfuse/Fuse_bindings.ml \
	       ocamlfuse/libFuse_stubs.a hslib/*.o hscgen

.PRECIOUS: hscgen/%.hs %_stubs.c
