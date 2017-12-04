#!/bin/bash

if [ $# -eq 0 ]; then
  echo "Usage $0 dir tpcc_dir"
  exit 1
fi

DIR=$1/d
echo "dir is $DIR"
mkdir $DIR

CONFIG=`realpath $DIR/tpcc.config`
DB=`realpath $DIR/tpcc.db`
DBSRC=/tmp/tpcc.db
TPCC="$2/pytpcc/"

if [ ! -f $DBSRC ]; then
  # generate the database
  pushd .
  cd $TPCC
  cat > sqlite.config << END
# SqliteDriver Configuration File
# Created today

[sqlite]

# The path to the SQLite database
database             = $DBSRC
END

  echo "Generating database"
  python2 ./tpcc.py --warehouses 1 --no-execute --config sqlite.config sqlite
  rm sqlite.config
  popd
fi

cat > $CONFIG << END
# SqliteDriver Configuration File
# Created today

[sqlite]

# The path to the SQLite database
database             = $DB
END

cp /tmp/tpcc.db $DB
sync $DB
sync $DIR

cd $TPCC
time python2 ./tpcc.py --warehouses 1 --no-load --config $CONFIG sqlite
