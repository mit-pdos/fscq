#!/usr/bin/env python3

# Usage (for fish):
# ./parse-results.py --header > results.csv
# for i in (seq 1 30)
#   ./run-bench.sh /dev/sdg1 largefile './largefile /tmp/ft' /tmp/ft
#   ./run-bench.sh /dev/sdg1 smallfile './smallfile /tmp/ft' /tmp/ft
#   ./parse-results.py >> results.csv
# end

import argparse

import re
import sys

def get_throughput(fname):
    with open(fname) as f:
        for line in f:
            m = re.match("writefile .* throughput (?P<throughput>[0-9.]*) KB/s\n", line)
            if m:
                return float(m.group("throughput"))
    return None

def get_files(fname):
    with open(fname) as f:
        for line in f:
            m = re.match("(?P<files>[0-9]*) files per (?P<usec>[0-9]*) usec\n", line)
            if m:
                return int(m.group("files")) / (int(m.group("usec"))/1e6)
    return None

parser = argparse.ArgumentParser()
parser.add_argument("--header", action="store_true")

args = parser.parse_args()

if args.header:
    print("system,bench,perf")
    sys.exit(0)

for system in ["origfscq", "dfscq-twosync", "fscq"]:
    for bench in ["smallfile", "largefile"]:
        fname = "{}-{}.out".format(bench, system)
        tput = get_throughput(fname) if bench == "largefile" else get_files(fname)
        print("{},{},{}".format(system,bench,tput))
