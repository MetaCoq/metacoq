TEMPLATE_LIB=../template-coq

a=`stat -f "%m" ${TEMPLATE_LIB}/gen-src`
b=`stat -f "%m" src`
if [ "$a" -gt "$b" ]
then
    echo "${TEMPLATE_LIB} is younger than gen-src"

    cp -r ${TEMPLATE_LIB}/gen-src/to-lower.sh src
    (cd src; ./to-lower.sh)
    cp -r ${TEMPLATE_LIB}/gen-src/*.ml ${TEMPLATE_LIB}/gen-src/*.mli src
else
    echo "Extracted code is up-to-date"
fi