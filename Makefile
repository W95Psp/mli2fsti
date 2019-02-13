#  This file is part of the ppx_tools package.  It is released
#  under the terms of the MIT license (see LICENSE file).
#  Copyright 2013  Alain Frisch and LexiFi

OCAMLC = ocamlfind ocamlc -package compiler-libs ocamlcommon.cma str.cma ocamlbytecomp.cma


all: mliConverter
	mv a.out mliConverter

customprint:
	$(OCAMLC) customprint.ml
miscTools:
	$(OCAMLC) miscTools.ml
MFCore: miscTools
	$(OCAMLC) miscTools.cmo MFCore.ml
mliConverter: MFCore customprint miscTools
	$(OCAMLC) customprint.cmo miscTools.cmo MFCore.cmo mliConverter.ml

clean:
	rm -f *.cmo *.cmi mliConverter a.out
