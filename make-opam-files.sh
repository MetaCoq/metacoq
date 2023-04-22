#/usr/bin/env bash

if (($# < 3))
then
    echo "Usage: make-opam-files.sh ../opam/released/packages <version> <package-url>"
    exit 0
fi

echo "Target directory: " $1
echo "Target version: " $2
echo "Releases package: " $3

wget $3
archive=`basename $3`
hash=`shasum -a 512 $archive | cut -f 1 -d " "`

echo "Shasum = " $hash

for f in *.opam;
do
    opamf=${f/.opam/};
    target=$1/$opamf/$opamf.$2/opam;
    echo $opamf;
    mkdir $1/$opamf/$opamf.$2
    gsed -e "/^version:.*/d" $f > $target
    echo url { >> $target
    echo "  src:" \"$3\" >> $target
    echo "  checksum:" \"sha512=$hash\" >> $target
    echo } >> $target
done