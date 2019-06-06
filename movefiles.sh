#!/usr/bin/env bash

cd template-coq

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

for i in *.ml*; do
    j=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'`; # the first letter of file name is put in lowercase
    k=`echo $i | cut -b 2-`; # the rest is untouched
    mv $i ../checker/src/$j$k;
done
