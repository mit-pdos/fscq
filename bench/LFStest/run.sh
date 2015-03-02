#!/bin/sh

echo "=== bigfile ==="
rm ../../xv6/fs.img
(cd ../../xv6 && make fs.img)
../../xv6/xv6fs ../../xv6/fs.img -s /tmp/xv6fs
sleep 10
cat /tmp/xv6fs/stats
./largefile -f 1 -i 1 /tmp/xv6fs
sleep 3
echo "stats"
cat /tmp/xv6fs/stats
killall xv6fs
sleep 3

echo "=== smallfile ==="
rm ../../xv6/fs.img
(cd ../../xv6 && make fs.img)
../../xv6/xv6fs ../../xv6/fs.img -s /tmp/xv6fs
sleep 3
cat /tmp/xv6fs/stats
./smallfile 1 1024 /tmp/xv6fs
sleep 3
echo "stats"
cat /tmp/xv6fs/stats
killall xv6fs


