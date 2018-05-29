#!/bin/bash

cd template-coq

shopt -s nullglob # make the for loop doing nothnig when there is no *.ml* files

for i in *.ml*; do
    j=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'`;
    k=`echo $i | cut -b 2-`;
    mv $i ../checker/src/$j$k;
done
