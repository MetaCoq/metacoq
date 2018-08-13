#env /bin/sh

echo "Cleaning result of extraction"

if [ ! -d "src" ]
then
    mkdir src
fi

# Move extracted modules to build the certicoq compiler plugin
# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=src/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Moving " $i "to" $newi;
  mv $i $newi;
done

# Remove extracted modules already linked in template_coq_plugin.
cd src
rm -f ast0.* specif.* peanoNat.* list0.* datatypes.* decimal.* ascii.* univ0.* binPosDef.* binPos.* binNat.* binNums.* binInt.* binIntDef.* bool.* nat0.* string0.* basics.* liftSubst.*
cd ..
