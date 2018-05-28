#/bin/bash

cd template-coq
for i in *.ml*; do
  mv $i ../checker/src/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
done
