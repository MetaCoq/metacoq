#!/bin/bash

SED=`which gsed || which sed`

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

echo "Cleaning result of extraction"

files=`cat ../template-coq/_PluginProject ../checker/_PluginProject.in | grep "^[^#].*mli\?$" | $SED -e s/gen-src/src/`

cd src
# Move extracted modules to build the certicoq compiler plugin
# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
do
  newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Moving " $i "to" $newi;
  mv $i $newi;
done
cd ..

# Remove extracted modules already linked in metacoq_template_plugin and checker.
echo "Removing:" $files

rm -f $files
