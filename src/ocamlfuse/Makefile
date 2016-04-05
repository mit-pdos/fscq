OCAMLMAKEFILE=../OCamlMakefile

SOURCES=Result.ml Unix_util.ml Unix_util_stubs.c Fuse_bindings.idl Fuse_util.c Fuse_lib.ml Fuse.ml
RESULT=Fuse
LIBS=bigarray
CLIBS=fuse
OCAMLLDFLAGS=-linkall
THREADS=threads
TRASH=*~ \\\#*
CFLAGS+=-D_FILE_OFFSET_BITS=64 -I. -pthread

LIBINSTALL_FILES=Fuse.a Fuse.cma Fuse.cmi Fuse.cmxa Fuse_bindings.cmi Fuse_lib.cmi Unix_util.cmi dllFuse_stubs.so libFuse_stubs.a
ifndef OCAML_LIB_INSTALL
	OCAML_LIB_INSTALL=$(OCAMLLIBPATH)/site-packages/ocamlfuse
endif

all: native-code-library byte-code-library

install: rawinstall
uninstall: rawuninstall

-include $(OCAMLMAKEFILE)
