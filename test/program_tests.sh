#!/bin/bash
for file in program/*.prog; do
    stack run $file < ${file%.prog}.in  > ${file%.prog}.tmp
    if diff "${file%.prog}.tmp" "${file%.prog}.out" >> /dev/null ; then
        echo "$file OK"
        rm ${file%.prog}.tmp
    else
        echo "$file WRONG ANSWER"
        echo -e "Input: \n"
        cat $file
        echo -e "\nOutput: \n"
        cat ${file%.prog}.tmp
        echo -e "\nShould be: \n"
        cat ${file%.prog}.out
        echo ""
        read -p "Do you want to replace correct answer? " -n 1 -r
        if [[ $REPLY =~ ^[Yy]$ ]]
        then
            mv ${file%.prog}.tmp ${file%.prog}.out
        fi
        echo ""
    fi
    #echo ""
    #cat ${file%.prog}.out
    #read -p "Press enter to continue"
done

