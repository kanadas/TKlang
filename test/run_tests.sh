#!/bin/bash
for file in Expr/*; do
    cat $file
    ./TestGrammar $file
    read -p "Press enter to continue"
done

