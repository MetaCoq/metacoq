#/usr/bin/env bash

if (($# < 3))
then
    echo "Usage: make-opam-files.sh ../opam/released/packages <version> <package-url>"
    exit 0
fi

archive=`basename $3`
tag=${archive/.tar.gz/}

echo "Target directory: " $1
echo "Target version: " $2
echo "Releases package: " $3
echo "Archive:" $archive
echo "Tag:" $tag

if [ -f $archive ]
then
    echo "Removing existing archive!"
    rm $archive
fi

wget $3

hash=`shasum -a 512 $archive | cut -f 1 -d " "`

echo "Shasum = " $hash

echo "Uploading to release assets"

gh release upload $tag $archive

release=https://github.com/MetaCoq/metacoq/releases/download/$tag/$archive

skipline=""

for f in *.opam;
do
    opamf=${f/.opam/};
    target=$1/$opamf/$opamf.$2/opam;
    echo $opamf;
    mkdir -p $1/$opamf/$opamf.$2
    skipline="$skipline $opamf.$2"
    gsed -e "/^version:.*/d" $f > $target
    echo url { >> $target
    echo "  src:" \"$release\" >> $target
    echo "  checksum:" \"sha512=$hash\" >> $target
    echo } >> $target
done

echo "ci-skip:" $skipline