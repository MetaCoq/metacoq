#!/bin/bash
TEMPLATE_LIB=../template-coq

if [[ "src" -ot "${TEMPLATE_LIB}/gen-src" || ! -f "src/metacoq_safechecker_plugin.cmxa" \
    || "src/metacoq_safechecker_plugin.cmxa" -ot "gen-src/Extract.v" ]]
then
    echo "Regenerating extracted files"
    cp -r ${TEMPLATE_LIB}/gen-src/*.ml ${TEMPLATE_LIB}/gen-src/*.mli src
    (cd src; ./to-lower.sh)
else
    echo "Extracted code is up-to-date"
fi