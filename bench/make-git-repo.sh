#!/bin/sh

if [ $# -ne 1 ]; then
  echo "$0 /tmp/fscq-bench"
  exit 1
fi

REPO="$1"

rm -rf $REPO
git clone .. $REPO

# ( cd $REPO && git filter-branch --index-filter 'git rm -r --cached --ignore-unmatch doc wiki' )
( cd $REPO && rm -rf doc )
( cd $REPO && rm -rf wiki )
( cd $REPO && rm -rf .git )
( cd $REPO && git init )
( cd $REPO && git add . )
( cd $REPO && git commit -m re-initialize )
