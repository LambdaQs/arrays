.PHONY: elab genclean cleanall genhaskell

AbsLambdaQs.ml: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

AbsQSharp.ml: QSharp.cf
	bnfc -mbnfc.mk --ocaml-menhir QSharp.cf && make all

elab: AbsLambdaQs.ml AbsQSharp.ml Elab.ml
	ocamlc -o TestElab BNFC_Util.ml AbsLambdaQs.ml SkelLambdaQs.ml ShowLambdaQs.ml PrintLambdaQs.ml ParLambdaQs.mli ParLambdaQs.ml LexLambdaQs.ml AbsQSharp.ml SkelQSharp.ml ShowQSharp.ml PrintQSharp.ml ParQSharp.mli ParQSharp.ml LexQSharp.ml Elab.ml

genclean: clean
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak

cleanall: genclean
	rm -f *.mll *.mly *LambdaQs.ml *QSharp.ml bnfc.mk BNFC_Util.ml

genhaskell: QSharp.cf
	bnfc -mbnfc.mk QSharp.cf && make all

sinclude bnfc.mk
