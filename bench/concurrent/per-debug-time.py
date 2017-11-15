#!/usr/bin/env python3

import re
from statistics import mean, median, stdev
DEBUG_RE = re.compile(r"""debug: (?P<name>.*) (?P<time>[0-9.]*)$""")

def parse_line(line):
    m = DEBUG_RE.match(line.rstrip())
    if m is None:
        return None
    return {'name': m.group('name'),
            'time': float(m.group('time')) }

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("file", type=argparse.FileType(),
            help="(c)fscq output to parse")

    args = parser.parse_args()

    debug_timings = {}

    for line in args.file:
        d = parse_line(line)
        if d is None:
            continue
        if d["name"] not in debug_timings:
            debug_timings[d["name"]] = []
        debug_timings[d["name"]].append(d["time"])
    timings = [(k, v) for k, v in debug_timings.items()]
    timings.sort(key=lambda e: sum(e[1]), reverse=True)
    for name, times in timings:
        mu = mean(times)
        med = median(times)
        s = stdev(times) if len(times) > 1 else float('inf')
        print("{:30} {:6.0} {:6.0} x{:6} sigma={:.0}".format(name, mu, med, len(times), s))
