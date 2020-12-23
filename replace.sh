#/bin/bash
SED=`which gsed || which sed`
echo $1
echo $2

${SED} -i -E -e \
    "s/declared_constructor ((\(.*\))|[^ ]*) ((\(.*\))|[^ ]*) ((\(.*\))|[^ ]*) ((\(.*\))|[^ ]*)([\)| ->])/declared_constructor \1 \7 \3 \5\9/g" \
    */*/*.v

# ${SED} -i -e "s/${1}/${2}/g" */*/*.v