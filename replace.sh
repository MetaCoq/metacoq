#/bin/bash
SED=`which gsed || which sed`
echo $1
echo $2

${SED} -i -E -e \
    "s/declared_inductive (((\.*\))|([^ _]*)) ([^ ]*) ([^ ]*) ([^ ]*)([\(| ->])/declared_inductive \1 \5 \3 \6\7/g" \
    */*/*.v

# ${SED} -i -e "s/${1}/${2}/g" */*/*.v