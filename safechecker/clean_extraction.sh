#!/bin/bash

SED=`which gsed || which sed`

echo "Cleaning result of extraction"

if [ ! -d "src" ]
then
    mkdir src
fi

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

files=`cat ../template-coq/_PluginProject | grep "^[^#].*mli\?$" | $SED -e s/gen-src/src/`

if [[ ! -f "src/metacoq_safechecker_plugin.cmxs" ||
           "src/metacoq_safechecker_plugin.cmxs" -ot "theories/Extraction.vo" ]]
then
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

    # Remove extracted modules already linked in template_coq_plugin, checker and pcuic.
    echo "Removing:" $files
    rm -f $files
else
    echo "Extraction up-to date"
fi
