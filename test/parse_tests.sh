#!/bin/bash
for file in parse/*.in; do
    ./TestGrammar $file > ${file%.in}.tmp
    if diff "${file%.in}.tmp" "${file%.in}.out" ; then
        echo "$file OK"
        rm ${file%.in}.tmp
    else
        echo "$file WRONG ANSWER"
        exit 1
    fi

    #cat $file
    #echo ""
    #cat ${file%.in}.out
    #read -p "Press enter to continue"
done

