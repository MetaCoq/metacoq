#!/usr/bin/env bash

###############################################################
#
# Usage:
# In the dependency-graph folder, [generate-dpegraph.sh myname]
# produces [myname.dot], [myname.png] and [myname.svg].
#
# Example:
# cd dependency-graph
# ./generate-depgraph.sh depgraph-2020-09-24
#
# Requires: graphviz for .dot to .png/.svg generation,
# a recent bash (not the one shipped with OS X Catalina for example)
###############################################################


filename=$1
dot_file=$filename.dot

# Associative arrays of the folders together with a color
declare -A folders
folders[template-coq]=aquamarine
folders[checker]=seagreen3
folders[pcuic]=lemonchiffon1
folders[safechecker]=paleturquoise1
folders[erasure]=tan

# Two first lines
echo "digraph dependencies {" > $dot_file
echo "node[style=filled]" >> $dot_file
for folder in "${!folders[@]}"
do
    cd ../$folder
    echo `pwd`
    coqdep -f _CoqProject -dumpgraph ../dependency-graph/$folder.dot > /dev/null
    cd ../dependency-graph
    # remove the first and last lines
    sed '1d' $folder.dot > $folder.dottmp && mv -f $folder.dottmp $folder.dot
    sed '$d' $folder.dot > $folder.dottmp && mv -f $folder.dottmp $folder.dot
    # change a bit the names of the nodes
    for otherfolder in "${!folders[@]}"
    do
	sed "s@../$otherfolder/theories@$otherfolder@g" $folder.dot > $folder.dottmp && mv -f $folder.dottmp $folder.dot
    done
    sed "s/theories/$folder/g" $folder.dot > $folder.dottmp && mv -f $folder.dottmp $folder.dot
    # change the color of the nodes
    sed "s/]/, color=${folders[$folder]}]/g" $folder.dot > $folder.dottmp && mv -f $folder.dottmp $folder.dot
    # concatenate
    cat $folder.dot >> $dot_file
    rm -f $folder.dot
done

# remove duplicate lines
awk '!a[$0]++' $dot_file > $dot_file.tmp && mv -f $dot_file.tmp $dot_file

# last line
echo "}" >> $dot_file

# produce the svg file
dot -Tsvg $dot_file -o $filename.svg
dot -Tpng $dot_file -o $filename.png
