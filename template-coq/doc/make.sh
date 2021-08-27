#!/usr/bin/env bash

rm -rf _build
mkdir _build

exec alectryon.py --traceback \
    --backend webpage \
    --copy-assets copy \
    --frontend coqdoc \
    -Q /Volumes/Dev/coq/metacoq-v8.11/template-coq/theories "MetaCoq.Template" \
    --output-directory _build/ \
    ../theories/*.v

# cp alectryon.sty _build
#    -I /Volumes/Dev/coq/metacoq-v8.11/template-coq/gen-src \
