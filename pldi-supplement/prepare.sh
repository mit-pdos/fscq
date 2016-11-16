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

if [ -d "$code" ]; then
    rm -r "$code"
fi
mkdir -p "$code"
cp $repo/LICENSE $code/
cp ./README.md $code/README.md

mkdir -p "$code/src"
cp "$repo/src/"*.v "$code/src/"

rm $code/src/AByteFile.v
rm $code/src/ExampleBlockRecover.v
rm $code/src/ExampleChecksumLog.v
rm $code/src/ExampleChecksumLog.v
rm $code/src/NewExtract.v

cp "$repo/src/Makefile" "$code/src/"
cp "$repo/src/README" "$code/src/"
cp "$repo/src/coqide.sh" "$code/src/coqide.sh"

# Building the FSCQ executables
cp "$repo/src/fuse.hs" "$code/src/"
cp "$repo/src/mkfs.hs" "$code/src/"
cp "$repo/src/mlfuse.hs" "$code/src/"
cp "$repo/src/mlmkfs.hs" "$code/src/"
cp "$repo/src/fiximports.py" "$code/src/"

copy_committed src/hslib/
copy_committed src/mllib/
copy_committed src/ocamlfuse/

tar -czvf "$code.tar.gz" "$code"
rm -r "$code"
