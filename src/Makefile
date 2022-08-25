default: genlambda

genlambda: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

genclean: clean
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak

cleanall: genclean
	rm -f *.mll *.mly *LambdaQs.ml bnfc.mk BNFC_Util.ml

sinclude bnfc.mk
