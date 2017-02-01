#!/bin/sh -x

L=/run/lock/fscq-builder
lockfile -r 0 $L || exit 0

THISDIR=$(dirname $0)

# $THISDIR/run-one.sh /usr/local/bin master master-coq85
# $THISDIR/run-one.sh /usr/local/coq-v86/bin master master-coq86
$THISDIR/run-one.sh /usr/local/coq-trunk/bin master master-coqtrunk
$THISDIR/run-one.sh /usr/local/coq-v86/bin io-concur io-concur-coq86
# $THISDIR/run-one.sh /usr/local/coq-trunk/bin io-concur io-concur-coqtrunk
$THISDIR/run-one.sh /usr/local/coq-trunk/bin new-extract new-extract-coqtrunk

rm -f $L
