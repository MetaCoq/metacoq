#!/bin/bash

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

for i in `ls *.ml *.mli`; do
    # echo $i
    j=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'`; # the first letter of file name is put in lowercase
    k=`echo $i | cut -b 2-`; # the rest is untouched
    if [ "$i" != "$j$k" ]; then
        mv -f $i $j$k
    fi
done
