#!/usr/bin/env bash
SED=`which gsed || which sed`
TOCOPY="ast_denoter.ml ast_quoter.ml denoter.ml plugin_core.ml plugin_core.mli reification.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml \
  caml_nat.mli caml_nat.ml caml_byte.ml caml_byte.mli caml_bytestring.ml"
SED=`which gsed || which sed`

# Test if gen-src is older than src
if [[ ! -f "gen-src/denoter.ml" ||
  "theories/Extraction.vo" -nt "gen-src/denoter.ml" || "$1" = "force" ]]
then
    echo "Updating gen-src from src"
    echo "Copying from src to gen-src"
    for x in ${TOCOPY}; do rm -f gen-src/$x; cp -a src/$x gen-src/$x; done
    echo "Renaming files to camelCase"
    (cd gen-src; ./to-lower.sh)
    rm -f gen-src/*.d gen-src/*.cm*
    # Fix an extraction bug: wrong type annotation on eq_equivalence
    ${SED} -i.bak 's/\r//g' gen-src/cRelationClasses.mli
    patch -N -p0 < extraction.patch
    patch -N -p0 < specFloat.patch
    exit 0
else
    echo "Extracted code is up-to-date"
fi
