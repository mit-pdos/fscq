#!/usr/bin/env python3

CATEGORIES = {
    "mechanical": [
        "Array",
        "BFile",
        "BFileCrash",
        "Balloc",
        "BlockPtr",
        "Compare",
        "GroupLog",
        "MemLog",
        "LogReplay",
        "Dir",
        "DirCache",
        "DiskSet",
        "AsyncFSRecover",
        "Idempotent",

        # rough categorization
        "DiskLog",
        "DiskLogHdr",
        "DiskLogPadded",
        "Log",
        "LogRecArray",
        "DirTree",
        "DirTreeDef",
        "DirTreeInodes",
        "DirTreeNames",
        "DirTreePred",
        "DirTreeRep",
        "DirTreeSafe",
        "DirSep",
        "DirSepCrash",
        "DirName",
        "FSLayout",
        "Hashmap",
        "MemMatch",
        "TreeCrash",


        ## formerly distinguished as spec/rep invariant changes
        "AsyncFS",
        "BFile.spec",
        "GroupLog.spec",
        "MemLog.spec",
        "SuperBlock",

        # rough categorization
        "FileRecArray",
    ],
    "core": [
        "AsyncDisk",
        "Blockmem",
        "Hoare",
        "Prog",
        "HoareWeak",
        "Instr",
        "Sec",
        "PredCrash",
        "Errno",

        # metatheory?
        "DiskSecVictim",
        "DiskSecDef",
        "DiskSecAttacker",

        # changes to FSCQ infrastructure
        "DestructPair",
        "SepAuto",
        "ProgAuto",
        "ProgLoop",
        "ProgList",
        "Pred",
        "MemPred",
        "ListPred",
        "GenSepN",
        "GenSepAuto",
        "Rec",
        "RecArrayUtils",
        "Word",
        "ProgMonad",
        "ListUtils",
    ],
    "fs security": [
        "AsyncFSPost",
        "AsyncFSProg",
        "AsyncRecArray",
        "CacheDef",
        "CacheLemmas",
        "CacheRangeSec",
        "CacheSec",
        "Inode", # implementation
        "ExtractHaskell",
    ],
    "other": [],
    "cp examples": [
        "CopyFile",
    ],
    "two exec example": [
        "TwoExecExample",
    ],
}

def add_ext(m):
    m_ext = {}
    for key, items in m.items():
        new_items = [i + ".v.diff" for i in items]
        m_ext[key] = new_items
    return m_ext

CATEGORIES = add_ext(CATEGORIES)

def reverse(m):
    r = {}
    for key, items in m.items():
        for item in items:
            r[item] = key
    return r

CATEGORIES_REV = reverse(CATEGORIES)

class FileChanges:
    def __init__(self, added, removed):
        self.added = added
        self.removed = removed

    @classmethod
    def from_file(cls, fname):
        added = 0
        removed = 0
        with open(fname) as f:
            for line in f:
                if line.startswith("+"):
                    added += 1
                if line.startswith("-"):
                    removed += 1
        return cls(added, removed)

    def __add__(self, other):
        return FileChanges(self.added + other.added, self.removed + other.removed)

    @property
    def total(self):
        return self.added + self.removed

if __name__ == "__main__":
    import argparse
    from os import path

    parser = argparse.ArgumentParser()
    parser.add_argument("diffs", nargs="+",
                        help="diff files to categorize")
    args = parser.parse_args()

    changes = {}
    for category in CATEGORIES.keys():
        changes[category] = FileChanges(0, 0)

    for fname in args.diffs:
        fc = FileChanges.from_file(fname)
        n = path.basename(fname)
        if n not in CATEGORIES_REV:
            c = "other"
            print("warning: no category for {} ({} lines)".format(n, fc.total))
        else:
            c = CATEGORIES_REV[n]
        changes[c] += fc

    for c, change in changes.items():
        if change.total > 0:
            print("{}: -{} +{}  total {}".format(c, change.removed, change.added, change.total))
