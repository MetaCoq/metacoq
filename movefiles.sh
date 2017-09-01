#/bin/bash

mv Ast.ml src/template_AST.ml
mv Ast.mli src/template_AST.mli
for i in *.ml*; do
  mv $i src/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
done
