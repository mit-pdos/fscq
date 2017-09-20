#!/usr/bin/env python


devices = [
        ("hdd", "/dev/sdc1"),
        ("ssd-sam", "/dev/sdb1"),
        ("ssd-intel", "/dev/sdd2"),
        ("ram", "/dev/loop"),
        ]

benches = [
    # ("smallfile", "./smallfile /tmp/ft"),
    # ("smallsync", "./smallsync /tmp/ft"),
    ("largefile", "./largefile /tmp/ft"),
    # ("mailbench", "./mailbench.sh /home/kaashoek/sv6 /tmp/ft"),
    # ("app-bench", "./app-bench.sh /home/kaashoek/xv6 /tmp/ft"),
    # ("tpcc",    "./tpcc.sh /tmp/ft ~/py-tpcc/"),
]

import os
import sys

for d, dev in devices:
    for b, bench in benches:
        for i in range(1, 2):
            name = "{}-{}-{}".format(b, d, i)
            cmd = "perflock ./run-bench.sh {0} '{1}' '{2}' > {1}.log".format(dev, name, bench)
            print(cmd)
            status = os.system(cmd)
            if status != 0:
                print("failed:", cmd, file=sys.stderr)
