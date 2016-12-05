#!/usr/bin/env python3

# Quick and dirty spec finder. Run as statistcs/specs.py. Produces
# statistics/specs/*.v containing specs from .v files (if there are any specs
# to be found), as well as counts in statistics/spec-counts.txt.

from __future__ import print_function

import re


def find_lines_between(pat1, pat2):
    file_matches = []
    for fname in files:
        regions = []
        with open(fname) as f:
            lines = f.readlines()
        region = None
        for line in lines:
            if pat1.search(line):
                region = []
            if region is not None:
                region.append(line)
            if pat2.search(line):
                if region is not None:
                    regions.append(region)
                region = None
        file_matches.append((fname, regions))
    return file_matches


def map_matches(file_matches, f):
    new_matches = []
    for fname, matches in file_matches:
        matches = list(f(matches))
        new_matches.append((fname, matches))
    return new_matches


def valid_theorem(region):
    for line in region:
        if re.search("PRE", line):
            return True
    return False


def filter_valid_thms(regions):
    for region in regions:
        if valid_theorem(region):
            yield region


if __name__ == "__main__":
    from os import path
    with open("statistics/files.txt") as f:
        files = [line.rstrip() for line in f]

    THM_BEGIN = re.compile("Theorem.*_ok :")
    THM_END = re.compile("\.$")
    file_specs = map_matches(find_lines_between(THM_BEGIN, THM_END),
                             filter_valid_thms)
    for fname, regions in file_specs:
        theorems = ["".join(region) for region in regions]
        if theorems:
            with open(path.join("statistics", "specs", fname), "w") as f:
                for thm in theorems:
                    f.write(thm)
                    f.write("\n")

    with open("statistics/spec-counts.txt", "w") as f:
        total_thms = 0
        for fname, regions in file_specs:
            num_thms = len(regions)
            if num_thms > 0:
                f.write("{}\t{}\n".format(fname, num_thms))
            total_thms += num_thms
        f.write("Total\t{}\n".format(total_thms))
