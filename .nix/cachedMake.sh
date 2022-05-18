#! /usr/bin/bash

# USAGE: To be run from the top directory of metacoq

# This whole file is a hack around coq-nix-toolbox to manage the
# structure of metacoq directories

export currentDir=$PWD
export configDir=$currentDir/.nix

#There should be a way to ask nix directly
coq_version='8.14'

my-nix-build-with-target (){
    target=$1
    shift
    env -i PATH=$PATH NIX_PATH=$NIX_PATH nix-build -A $target \
        --argstr bundle "$selectedBundle" --no-out-link\
        --option narinfo-cache-negative-ttl 0 $*
}

my-cachedMake (){
    cproj=$currentDir/$coqproject
    cprojDir=$(dirname $cproj)
    nb_dry_run=$(my-nix-build-with-target $1 --dry-run 2>&1 > /dev/null)
    if echo $nb_dry_run | grep -q "built:"; then
        echo "The compilation result is not in cache."
        echo "Either it is not in cache (yet) or your must check your cachix configuration."
        kill -INT $$
    else
        build=$(my-nix-build-with-target $1)
        realpath=$2
        namespace=$3
        logpath=${namespace/.//}
        vopath="$build/lib/coq/$coq_version/user-contrib/$logpath"
        dest=$cprojDir/$realpath
        if [[ -d $vopath ]]
        then echo "Compiling/Fetching and copying vo from $vopath to $realpath"
                cp -nr --no-preserve=mode,ownership  $vopath/* $dest
        else echo "Error: cannot find compiled $logpath, check your .nix/config.nix"
        fi
    fi
}

my-cachedMake 'template-coq' 'template-coq/theories' 'MetaCoq.Template'
my-cachedMake 'pcuic' 'pcuic/theories' 'MetaCoq.PCUIC'
my-cachedMake 'safechecker' 'safechecker/theories' 'MetaCoq.SafeChecker'
my-cachedMake 'erasure' 'erasure/theories' 'MetaCoq.Erasure'

unset -f my-nix-build-with-target
unset -f my-cachedMake
