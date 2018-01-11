#!/usr/bin/env python3

import re
STRACE_RE = re.compile(r"""[0-9 ]*((?P<syscall>\w*)\(.*|<... (?P<syscall_resumed>.*) resumed>.*)<(?P<time>[0-9.]*)>$""")

def parse_line(line):
    m = STRACE_RE.match(line.rstrip())
    if m is None:
        return None
    return {'syscall': m.group('syscall') or m.group('syscall_resumed'),
            'time': float(m.group('time')) }

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("file", type=argparse.FileType(),
            help="strace output to parse")

    args = parser.parse_args()

    syscall_timings = {"<all>": 0}

    for line in args.file:
        d = parse_line(line)
        if d is None:
            continue
        if d["syscall"] not in syscall_timings:
            syscall_timings[d["syscall"]] = 0
        syscall_timings[d["syscall"]] += d["time"]
        syscall_timings["<all>"] += d["time"]
    timings = [(k, v) for k, v in syscall_timings.items()]
    timings.sort(key=lambda e: e[1], reverse=True)
    for syscall, time in timings:
        if time >= syscall_timings["<all>"]*.01:
            print("{:15} {:6.4f}s".format(syscall, time))
