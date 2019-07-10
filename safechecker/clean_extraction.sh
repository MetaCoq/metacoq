#!/bin/bash

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

echo "Cleaning result of extraction"

if [ ! -d "src" ]
then
    mkdir src
fi

cd src

# Move extracted modules to build the certicoq compiler plugin
# Uncapitalize modules to circumvent a bug of coqdep with mllib files
if [ -f "PCUICAst.ml" ]
then
    for i in *.ml*
      do
      newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
      echo "Moving " $i "to" $newi;
      mv $i $newi;
    done
else
    echo "No files to extract"
fi
