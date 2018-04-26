#!/usr/bin/env python3

import re

def relevant_file(path):
    return re.match(r""".*src/[^/]*\.v$""", path) is not None


def overwrite(fname, contents):
    """Overwrite fname with contents and return True if its contents
    changed."""
    if path.exists(fname):
        with open(fname) as f:
            if f.read() == contents:
                return False
    with open(fname, "w") as f:
        f.write(contents)
    return True


if __name__ == "__main__":
    import argparse
    import unidiff
    import os
    from os import path
    import shutil

    parser = argparse.ArgumentParser()
    parser.add_argument("-o", "--output",
                        default="diffs",
                        help="directory to output file patches to")
    parser.add_argument("-f", "--force",
                        action="store_true",
                        help="overwrite output directory first")
    parser.add_argument("diff")
    args = parser.parse_args()

    with open(args.diff, "r") as f:
        patches = unidiff.PatchSet(f)
    if path.exists(args.output) and args.force:
        shutil.rmtree(args.output)
    changed_files = []
    for p in patches:
        target_path = p.target_file
        d = path.dirname(target_path)
        fname = path.basename(target_path)
        if relevant_file(target_path):
            target_dir = path.join(args.output, d)
            if not path.exists(target_dir):
                os.makedirs(target_dir)
            changed = overwrite(path.join(target_dir, fname + ".diff"), str(p))
            if changed:
                changed_files.append(target_path)
    if changed_files:
        print("diff changed for:")
        for f in changed_files:
            print(f)
