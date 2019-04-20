#!/bin/bash
bnfc -haskell Grammar.cf
mv DocGrammar.* ../doc
make all
make clean
