#!/bin/bash
# set COQIDE_JOBS to the number of coqtop processes that coqide
# should run in parallel; e.g., 8 on an 8-core system.
exec coqide -async-proofs-j ${COQIDE_JOBS:-1} -R . Fscq "$@"
