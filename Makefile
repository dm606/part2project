.PHONY: all clean debug test
DEFAULT: all

OCAMLBUILD_FLAGS = -use-ocamlfind $(shell find src -type d -printf "-I %p ")

src/syntax/AbsConcrete.ml: src/syntax/Concrete.cf
	cd src/syntax/; bnfc --ocaml Concrete.cf

all: src/syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) main.native

prof: src/syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) main.p.native

debug: src/syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) main.d.byte

test: src/syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) -I tests -package oUnit -package quickcheck all_tests.native
	./all_tests.native

clean:
	ocamlbuild -clean
	rm -f src/syntax/LexConcrete.* src/syntax/ParConcrete.*
	rm -f src/syntax/LayoutConcrete.* src/syntax/SkelConcrete.*
	rm -f src/syntax/PrintConcrete.* src/syntax/ShowConcrete.*
	rm -f src/syntax/TestConcrete.* src/syntax/AbsConcrete.*
	rm -f src/syntax/BNFC_Util.ml
