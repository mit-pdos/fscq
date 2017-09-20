#!/usr/bin/env python

dir = "/tmp/ft"

devices = [
        ("hdd", "/dev/sdc1"),
        ("ssd-sam", "/dev/sdb1"),
        ("ssd-intel", "/dev/sdd2"),
        ("ram", "/dev/loop"),
        ]

benches = [
    # ("smallfile", "./smallfile %s" % dir),
    # ("smallsync", "./smallsync %s" % dir),
    ("largefile", "./largefile %s" % dir),
    # ("mailbench", "./mailbench.sh /home/kaashoek/sv6 %s" % dir),
    # ("app-bench", "./app-bench.sh /home/kaashoek/xv6 %s" % dir),
    # ("tpcc",    "./tpcc.sh %s ~/py-tpcc/" % dir),
]

import os
import sys

for d, dev in devices:
    for b, bench in benches:
        for i in range(1, 2):
            name = "{}-{}-{}".format(b, d, i)
            cmd = "perflock ./run-bench.sh {0} '{1}' '{2}' '{3}' > {1}.log".format(dev, name, bench, dir)
            print(cmd)
            status = os.system(cmd)
            if status != 0:
                print("failed:", cmd, file=sys.stderr)
