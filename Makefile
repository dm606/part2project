.PHONY: all clean debug test
DEFAULT: all

OCAMLBUILD_FLAGS = -use-ocamlfind $(shell find src -type d -printf "-I %p ")

src/Syntax/AbsConcrete.ml: src/Syntax/Concrete.cf
	cd src/Syntax/; bnfc --ocaml Concrete.cf

all: src/Syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) main.native

debug: src/Syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) main.d.byte

test: src/Syntax/AbsConcrete.ml
	ocamlbuild $(OCAMLBUILD_FLAGS) -I tests -package oUnit all_tests.native
	./all_tests.native

clean:
	ocamlbuild -clean
	rm -f src/Syntax/LexConcrete.* src/Syntax/ParConcrete.*
	rm -f src/Syntax/LayoutConcrete.* src/Syntax/SkelConcrete.*
	rm -f src/Syntax/PrintConcrete.* src/Syntax/ShowConcrete.*
	rm -f src/Syntax/TestConcrete.* src/Syntax/AbsConcrete.*
	rm -f src/Syntax/BNFC_Util.ml
