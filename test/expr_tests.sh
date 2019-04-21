#!/bin/bash
for file in expr/*.in; do
    stack run $file > ${file%.in}.out
    #if diff "${file%.in}.tmp" "${file%.in}.out" ; then
    #    echo "$file OK"
    #    rm ${file%.in}.tmp
    #else
    #    echo "$file WRONG ANSWER"
    #    exit 1
    #fi

    cat $file
    echo ""
    cat ${file%.in}.out
    read -p "Press enter to continue"
done

