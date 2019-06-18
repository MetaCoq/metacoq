#!/bin/bash
TEMPLATE_LIB=../template-coq

if [ "src" -ot "${TEMPLATE_LIB}/gen-src" ]
then
    echo "${TEMPLATE_LIB} is younger than src"
    cp -r ${TEMPLATE_LIB}/gen-src/to-lower.sh src
    (cd src; ./to-lower.sh)
    cp -r ${TEMPLATE_LIB}/gen-src/*.ml ${TEMPLATE_LIB}/gen-src/*.mli src
else
    echo "Extracted code is up-to-date"
fi