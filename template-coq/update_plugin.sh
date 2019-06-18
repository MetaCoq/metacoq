#!/bin/bash

TOCOPY="ast_denoter.ml ast_quoter.ml denote.ml denoter.ml plugin_core.ml plugin_core.mli quoted.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml"

# Test is gen-src is older than src
if [[ "gen-src" -ot "src" || ! -f "gen-src/denote.ml" ]]
then
    echo "Updating gen-src from src"
    mkdir -p build
    cp src/template_coq.cmx src/template_coq.cmxa src/template_coq.cmxs build
    echo "Copying from src to gen-src"
    for x in ${TOCOPY}; do rm -f gen-src/$x; cp src/$x gen-src/$x; done
    echo "Renaming files to camelCase"
    (cd gen-src; ./to-lower.sh)
else
    echo "Extracted code is up-to-date"
fi