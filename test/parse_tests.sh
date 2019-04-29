#!/bin/bash
for file in parse/*.in; do
    ./TestGrammar $file > ${file%.in}.tmp
    if diff "${file%.in}.tmp" "${file%.in}.out" >> /dev/null ; then
        echo "$file OK"
        rm ${file%.in}.tmp
    else
        echo "$file WRONG ANSWER"
        echo -e "Input: \n" 
        cat $file
        echo -e "\nOutput: \n"
        cat ${file%.in}.tmp
        echo -e "\nShould be: \n"
        cat ${file%.in}.out
        echo ""
        read -p "Do you want to replace correct answer? " -n 1 -r
        if [[ $REPLY =~ ^[Yy]$ ]]
        then
            mv ${file%.in}.tmp ${file%.in}.out
        fi
        echo ""
    fi

    #cat $file
    #echo ""
    #cat ${file%.in}.out
    #read -p "Press enter to continue"
done

