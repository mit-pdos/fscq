#!/usr/bin/python

# run this as:
#   python mini-sql.py | sqlite /mnt/fscq/sqlite.db

scale = 400

print "create table x (a int, b string);"
print "create index i on x (a);"
print "create index j on x (b);"

print "begin transaction;"
for i in range(0, 10 * scale):
    print "insert into x (a, b) values ({0}, '{1}');".format(
        i, "foo {0} bar {0} bench {0} mark {0}".format(i) * 10)
print "end transaction;"

for i in range(0, scale):
  print "select * from x where a = %d;" % (i * 3);

for i in range(0, scale):
  print "update x set b = 'bar%d' where a = %d;" % (i, (i * 4));

for i in range(0, scale):
  print "delete from x where b = 'foo%d';" % (i * 5);
