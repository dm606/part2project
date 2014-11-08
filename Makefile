.PHONY: all clean debug

all:
	cd src/Syntax/; bnfc --ocaml Concrete.cf
	ocamlbuild -Is src,src/Syntax Main.native

debug:
	cd src/Syntax/; bnfc --ocaml Concrete.cf
	ocamlbuild -Is src,src/Syntax Main.d.byte

clean:
	ocamlbuild -clean
	rm -f src/Syntax/LexConcrete.* src/Syntax/ParConcrete.*
	rm -f src/Syntax/LayoutConcrete.* src/Syntax/SkelConcrete.*
	rm -f src/Syntax/PrintConcrete.* src/Syntax/ShowConcrete.*
	rm -f src/Syntax/TestConcrete.* src/Syntax/AbsConcrete.*
	rm -f src/Syntax/BNFC_Util.ml
