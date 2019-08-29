# FSCQ

FSCQ is a file system written and verified in the Coq proof assistant.

## Unmaintained research prototype

Warning: the FSCQ software is not maintained.  FSCQ's core is verified in
Coq, but FSCQ also includes components written in Haskell for interacting
with FUSE, and depends on FUSE and Haskell bindings for FUSE, none of
which are verified.  The unverified portions are likely to have bugs,
and we do not recommend that anyone use the FSCQ research prototype
in practice.

Although the overall software is not maintained, we would be interested
in hearing from others that discover issues with the verified portions
of FSCQ.

## Branches

There are several branches in this repository, corresponding to different
FSCQ-related projects.

- The `master` branch contains the source code for the DFSCQ file system,
roughly corresponding to the SOSP 2017 paper.

- The `security` branch contains the source code for the SFSCQ file
system and the DiskSec sealed block framework, roughly corresponding to
the OSDI 2018 paper.
