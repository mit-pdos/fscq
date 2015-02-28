Run:

./xv6fs -f -d -s /tmp/xv6fs

Some things that work:

ls -l /tmp/xv6fs/hello.txt
cat /tmp/xv6fs/hello.txt
echo hello > /tmp/xv6fs/x.txt
cat /tmp/xv6fs/x.txt

Unmount:

umount /tmp/xv6fs
