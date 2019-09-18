#!/bin/bash
TEMPLATE_LIB=../template-coq

if [[ "src" -ot "${TEMPLATE_LIB}/gen-src" || ! -f "src/metacoq_checker_plugin.cmxa" \
    || "src/metacoq_checker_plugin.cmxa" -ot "gen-src/Extract.v" ]]
then
    echo "Renaming extracted files"
    cp -r ${TEMPLATE_LIB}/gen-src/to-lower.sh src
    (cd src; ./to-lower.sh)
else
    echo "Extracted code is up-to-date"
fi