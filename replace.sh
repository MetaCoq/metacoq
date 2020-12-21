#/bin/bash
SED=`which gsed || which sed`
echo $1
echo $2
${SED} -i -e "s/$1/$2/g" */*/*.v