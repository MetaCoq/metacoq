#/bin/bash

for i in *.ml*; do
  mv $i src/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
done
