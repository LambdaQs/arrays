default: genlambda

genlambda: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

genqsharp: QSharp.cf
	bnfc -mbnfc.mk --ocaml-menhir QSharp.cf && make all

genclean: clean
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak

elab: Elab.ml genqsharp genlambda
	ocamlc -o TestElab BNFC_Util.ml AbsLambdaQs.ml SkelLambdaQs.ml ShowLambdaQs.ml PrintLambdaQs.ml ParLambdaQs.mli ParLambdaQs.ml LexLambdaQs.ml AbsQSharp.ml SkelQSharp.ml ShowQSharp.ml PrintQSharp.ml ParQSharp.mli ParQSharp.ml LexQSharp.ml Elab.ml

cleanall: genclean
	rm -f *.mll *.mly *LambdaQs.ml *QSharp.ml bnfc.mk BNFC_Util.ml

sinclude bnfc.mk
