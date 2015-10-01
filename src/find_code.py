#!/usr/bin/env python3

from __future__ import print_function

import re
import collections
import sys

CODE_BEGIN = re.compile(r"""(Definition|Fixpoint|Function|Program Definition) (?P<name>\w*)""")
CODE_END = re.compile(r"""\.\s*$""")
LOOP_INIT = re.compile(r"\b(ForEach|For)\b")
LOOP_BEGIN = re.compile(r"Begin")

class Snippet:
    def __init__(self):
        self.fname = None
        self.name = None
        self.is_prog = False
        self.lines = []

    def append(self, line):
        self.lines.append(line)

class CodeBox:
    def __init__(self):
        self.snippets = []
        self._cur_snippet = Snippet()
        self.is_code = False
        self.is_loop_spec = False

    def add_line(self, line, fname):
        if self.is_code:
            if self.is_loop_spec:
                if LOOP_BEGIN.search(line):
                    self.is_loop_spec = False
                    self.add_line(line, fname)
                return
            else:
                if LOOP_INIT.search(line):
                    self.is_loop_spec = True
                    self.add_line(line, fname)
            self._cur_snippet.append(line)
            if CODE_END.search(line):
                self.snippets.append(self._cur_snippet)
                self._cur_snippet = Snippet()
                self.is_code = False
        else:
            begin = CODE_BEGIN.search(line)
            if begin:
                self._cur_snippet.name = begin.group("name")
                if re.search("rx", line):
                    self._cur_snippet.is_prog = True
                self._cur_snippet.fname = fname
                self.is_code = True
                self.add_line(line, fname)

    def index(self):
        snippets = collections.defaultdict(list)
        for snippet in self.snippets:
            snippets[snippet.name].append(snippet)
        return snippets

def dependencies(snippet, snippets):
    """
    Get the dependencies of a snippet from a collection of definitions.

    :param snippet: a Snippet
    :param snippets: a dict name -> [Snippet] of global definitions
    :return: a list of names that snippet depends on
    """
    deps = set([])
    for line in snippet.lines:
        for word in re.split("[ .]", line):
            if word in snippets:
                deps.add(word)
    return deps

def transitive_dependencies(selection_names, snippets):
    """
    Get all the dependent snippets for a set of names.

    :selection_names: a set of names
    :return: a set of snippets
    """
    old_size = len(selection_names)
    for name in list(selection_names):
        aliased_snippets = snippets[name]
        for snippet in aliased_snippets:
            selection_names.update(dependencies(snippet, snippets))
    if len(selection_names) == old_size:
        deps = []
        for name in selection_names:
            deps.extend(snippets[name])
        return deps
    return transitive_dependencies(selection_names, snippets)

def prog_dependencies(box):
    progs = set([])
    for snippet in box.snippets:
        if snippet.is_prog:
            progs.add(snippet.name)
    return transitive_dependencies(progs, box.index())

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
            formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("file", nargs="+")
    parser.add_argument("-o", "--output",
            help="file to output all discovered code to")

    args = parser.parse_args()

    import sys

    output = sys.stdout
    if args.output:
        output = open(args.output, "w")

    box = CodeBox()
    for fname in args.file:
        if fname == args.output:
            continue
        with open(fname) as f:
            for line in f:
                box.add_line(line, fname)

    file_snippets = collections.defaultdict(list)
    for snippet in prog_dependencies(box):
        file_snippets[snippet.fname].append(snippet)
    for fname, snippets in file_snippets.items():
        if snippets:
            output.write("(* File: {} *)\n".format(fname))
        for snippet in snippets:
            output.writelines(snippet.lines)
            output.write("\n")

    output.close()
