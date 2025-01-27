#!/usr/bin/env bash

SED=`which gsed | which sed`

echo "Cleaning result of extraction"

if [ ! -d "src" ]
then
    mkdir src
fi

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

files=`cat ../template-coq/_PluginProject.in | grep "^[^#].*mli\?$" | sed -e s/gen-src/src/`

if [[ ! -f "src/metacoq_safechecker_plugin.cmxs" ||
           "src/metacoq_safechecker_plugin.cmxs" -ot "theories/Extraction.vo" ]]
then
    cd src
    # Move extracted modules to build the certicoq compiler plugin
    # Uncapitalize modules to circumvent a bug of coqdep with mllib files
    for i in *.ml*
      do
      newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
      if [ $i != $newi ]
      then
          # echo "Moving " $i "to" $newi;
          mv $i tmp;
          mv tmp $newi;
      fi
    done
    cd ..

    # confusion between Init.Wf and Program.Wf
    if [ -f src/wf.ml ]; then mv src/wf.ml src/wf0.ml; fi;
    if [ -f src/wf.mli ]; then mv src/wf.mli src/wf0.mli; fi;
    ${SED} -i -e "s/open Wf/open Wf0/" src/pCUICSafeChecker.ml

    # Remove extracted modules already linked in the template_coq plugin.
    echo "Removing:" $files
    rm -f $files
else
    echo "Extraction up-to date"
fi
