#/bin/bash
SED = `which gsed || which sed`

${SED} -i -e s/$1/$2/g */*/*.v