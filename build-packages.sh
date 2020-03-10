DESTDIR=~/dev/coq/opam-coq-archive/released/packages

BASE="coq-metacoq"

PACKAGES=" -template -checker -pcuic -safechecker -erasure -translations"

VERSION=1.0~alpha2+8.11

ADD="url {
  src: \"https://github.com/MetaCoq/metacoq/archive/1.0-alpha2+8.11.tar.gz\"
  checksum: \"sha256=8f1d2b42ad97d7c8660a57aabe53ddcc7b1645ced43386a1d2bef428b20d6b42\"
}"

for f in "" ${PACKAGES}
do
  pack="$BASE$f"
  echo $pack
  dir="$DESTDIR/$pack/$pack.$VERSION"
  mkdir $dir
  echo $dir
  cp $pack.opam $dir/opam
  echo "${ADD}" >> $dir/opam
done
