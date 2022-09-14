#! /usr/bin/bash

cd .github/workflows

for f in $(find . -name 'nix-action*.yml')
do
  name=${f%.yml}
  sed 's/ubuntu/macos/g' $f > "$name-macos.yml"
  mv $f "$name-ubuntu.yml"
done
