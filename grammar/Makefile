all:
	happy -gca -i ParGrammar.y
	alex -g LexGrammar.x
	
test:
	ghc --make TestGrammar.hs -o TestGrammar

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocGrammar.* LexGrammar.* ParGrammar.* LayoutGrammar.* SkelGrammar.* PrintGrammar.* TestGrammar.* AbsGrammar.* TestGrammar ErrM.* SharedString.* ComposOp.* Grammar.dtd XMLGrammar.* Makefile*
	
