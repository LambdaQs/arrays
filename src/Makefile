.PHONY: elab genclean cleanall genhaskell

AbsLambdaQs.ml: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

AbsQSharp.ml: QSharp.cf
	bnfc -mbnfc.mk --ocaml-menhir QSharp.cf && make all

elab: AbsLambdaQs.ml AbsQSharp.ml Elab.ml
	ocamlc -o TestElab BNFC_Util.ml AbsLambdaQs.ml SkelLambdaQs.ml ShowLambdaQs.ml PrintLambdaQs.ml ParLambdaQs.mli ParLambdaQs.ml LexLambdaQs.ml AbsQSharp.ml SkelQSharp.ml ShowQSharp.ml PrintQSharp.ml ParQSharp.mli ParQSharp.ml LexQSharp.ml Elab.ml

elab_native: AbsLambdaQs.ml AbsQSharp.ml Elab.ml
	ocamlfind ocamlopt -thread -package z3 -linkpkg -c BNFC_Util.ml AbsLambdaQs.ml SkelLambdaQs.ml ShowLambdaQs.ml PrintLambdaQs.ml ParLambdaQs.ml LexLambdaQs.ml AbsQSharp.ml SkelQSharp.ml ShowQSharp.ml PrintQSharp.ml ParQSharp.ml LexQSharp.ml Elab.ml

# Elab.cmx: Elab.ml
# 	ocamlfind ocamlopt -thread -package z3 -linkpkg -c Elab.ml

clonecheck: elab_native Clonecheck1.ml
	ocamlfind ocamlopt -thread -package z3 -linkpkg -o Clonecheck1 BNFC_Util.cmx AbsLambdaQs.cmx SkelLambdaQs.cmx ShowLambdaQs.cmx PrintLambdaQs.cmx ParLambdaQs.cmx LexLambdaQs.cmx AbsQSharp.cmx SkelQSharp.cmx ShowQSharp.cmx PrintQSharp.cmx ParQSharp.cmx LexQSharp.cmx Elab.cmx Clonecheck1.ml

genclean: clean
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak *.cmx *.o

cleanall: genclean
	rm -f *.mll *.mly *LambdaQs.ml *QSharp.ml bnfc.mk BNFC_Util.ml

cleangrammars: 
	rm -f Abs* Lex* Par* Print* Skel* Show* Test*

genhaskell: QSharp.cf
	bnfc -mbnfc.mk QSharp.cf && make all

sinclude bnfc.mk
