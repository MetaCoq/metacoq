#/bin/bash
SED=`which gsed || which sed`
echo $1
echo $2

${SED} -i -E -e \
    "s/declared_inductive ((\(.*\))|[^ ]*) ((\(.*\))|[^ ]*) ((\(.*\))|[^ ]*) ((\(.*\))|[^ ]*)([\)| ->])/declared_inductive \1 \5 \3 \7\9/g" \
    */*/*.v

# ${SED} -i -e "s/${1}/${2}/g" */*/*.v