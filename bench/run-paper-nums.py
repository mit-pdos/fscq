#!/usr/bin/env python


devices = [
        ("hdd", "/dev/sdc1"),
        ("ssd-sam", "/dev/sdb1"),
        ("sdd-intel", "/dev/sdd2"),
        ("ram", "/dev/loop0"),
        ]

benches = [
    ("smallfile", "./smallfile /tmp/ft"),
    ("smallsync", "./smallsync /tmp/ft"),
    ("largefile", "./largefile /tmp/ft"),
    ("mailbench", "./mailbench.sh /home/alex/sv6 /tmp/ft"),
    ("app-bench", "./app-bench.sh /home/alex/xv6 /tmp/ft"),
    ("sqlite",    "./sqlitebench.sh /tmp/ft"),
]

benches = [x for x in benches if x[0] == "mailbench"]

import os
import sys

for d, dev in devices:
    for b, bench in benches:
        for i in range(1, 6):
            name = "{}-{}-{}".format(b, d, i)
            cmd = "perflock ./run-bench.sh {0} '{1}' '{2}' > {1}.log".format(dev, name, bench)
            print(cmd)
            status = os.system(cmd)
            if status != 0:
                print("failed:", cmd, file=sys.stderr)


