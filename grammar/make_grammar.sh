#!/bin/bash
bnfc -haskell Grammar.cf
mv DocGrammar.txt ../doc
make all
make clean
mv TestGrammar ../test


