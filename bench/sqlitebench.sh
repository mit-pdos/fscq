#!/bin/bash

set -o xtrace

DIR=$1
DB=`realpath $DIR/sqlite.db`

time -p (python2 ./mini-sql.py | sqlite3 $DB)
