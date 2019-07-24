#env /bin/sh

SED=`which gsed || which sed`

echo "Cleaning result of extraction"

if [ ! -d "src" ]
then
    mkdir src
fi

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

files=`cat ../template-coq/_PluginProject ../checker/_PluginProject.in ../pcuic/_PluginProject.in | grep "^[^#].*mli\?$" | $SED -e s/gen-src/src/`

cd src

# Move extracted modules to build the certicoq compiler plugin
# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Moving " $i "to" $newi;
  mv $i $newi;
done

cd ..

# Remove extracted modules already linked in template_coq_plugin, checker and pcuic.
echo "Removing:" $files

rm -f $files
