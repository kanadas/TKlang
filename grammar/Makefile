all: grammar test

grammar: ParGrammar.hs LexGrammar.hs

ParGrammar.hs: ParGrammar.y
	happy -gca -i ParGrammar.y

LexGrammar.hs: LexGrammar.x
	alex -g LexGrammar.x
	
test: ParGrammar.hs LexGrammar.hs
	ghc --make TestGrammar.hs -o TestGrammar

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocGrammar.* LexGrammar.* ParGrammar.* LayoutGrammar.* SkelGrammar.* PrintGrammar.* TestGrammar.* AbsGrammar.* TestGrammar ErrM.* SharedString.* ComposOp.* Grammar.dtd XMLGrammar.* Makefile*
	
