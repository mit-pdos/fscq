#!/bin/bash

# Take code from $repo and put a cleaned version in $code, in order to create a
# supplement $code.tar.gz to submit.
repo=".."
code="chl-fscq"

copy_committed() {
    path="$1"
    mkdir -p "$code/$path"
    for file in $(git ls-files "$repo/$path"); do
        cp $file "$code/$path/"
    done
}

mkdir -p "$code"
cp $repo/LICENSE $code/
cp ./README.md $code/README.md

mkdir -p "$code/src"
cp "$repo/src/"*.v "$code/src/"
rm $code/src/AByteFile.v

cp "$repo/src/Makefile" "$code/src/"
cp "$repo/src/README" "$code/src/"
cp "$repo/src/coqide.sh" "$code/src/coqide.sh"

copy_committed src/hslib/
copy_committed src/mllib/
copy_committed src/ocamlfuse/

tar -czvf "$code.tar.gz" "$code"
rm -r "$code"
