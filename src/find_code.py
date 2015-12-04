#!/usr/bin/env python3

from __future__ import print_function

import re
import collections
import sys

CODE_BEGIN = re.compile(r"""(Theorem|Lemma|Definition|Fixpoint|Function|Program Definition) (?P<name>\w*)""")
CODE_END = re.compile(r"""\.\s*$""")
LOOP_INIT = re.compile(r"\b(ForEach|For)\b")
LOOP_BEGIN = re.compile(r"Begin")

class Snippet:
    def __init__(self):
        self.fname = None
        self.name = None
        self.is_thm = False
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
                if re.search("(Theorem|Lemma)", line):
                    self._cur_snippet.is_thm = True
                elif re.search("rx", line):
                    self._cur_snippet.is_prog = True
                self._cur_snippet.fname = fname
                self.is_code = True
                self.add_line(line, fname)

    def index(self):
        snippets = collections.defaultdict(list)
        for snippet in self.snippets:
            snippets[snippet.name].append(snippet)
        return snippets

def any_non_thm(snippet_list):
    for snippet in snippet_list:
        if not snippet.is_thm:
            return True
    return False

def ok_thm_prog(snippet):
    if not snippet.is_thm:
        return None
    m = re.match("^(\w*)_ok", snippet.name)
    if m is None:
        return None
    return m.group(1)

def dependencies(snippet, snippets):
    """
    Get the dependencies of a snippet from a collection of definitions.

    There must be a dependency on a non-theorem.

    :param snippet: a Snippet
    :param snippets: a dict name -> [Snippet] of global definitions
    :return: a list of names that snippet depends on
    """
    deps = set([])
    for line in snippet.lines:
        for word in re.split("[ .]", line):
            if any_non_thm(snippets[word]) and word != ok_thm_prog(snippet):
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
    parser.add_argument("-m", "--main",
            help="file to start program dependency search from")
    parser.add_argument("-s", "--specs",
            action="store_true",
            help="get dependencies for all specs")

    ## Example usages:
    # How much functional code is required to implement FSCQ without any specs?
    # ./find_code.py -o code.v -m FS.v *.v
    #
    # How much code is required to specify FSCQ, from the perspective of the
    # TCB? This is a fair estimate since it includes all definitions that are
    # part of the specs.
    # ./find_code.py -o top-specs.v -m FS.v --specs *.v
    #
    # How much specification is required? This is one form of proof burden for
    # the developer, and also includes definitions required to write the specs.
    # ./find_code.py -o all-specs.v --specs *.v

    args = parser.parse_args()

    import sys

    box = CodeBox()
    for fname in args.file:
        if fname == args.output:
            continue
        with open(fname) as f:
            for line in f:
                box.add_line(line, fname)

    if args.main is None:
        main_box = box
    else:
        main_box = CodeBox()
        with open(args.main) as f:
            for line in f:
                main_box.add_line(line, fname)

    if args.specs:
        spec_filter = lambda s: s.is_thm
    else:
        spec_filter = lambda s: s.is_prog

    main_names = set([s.name for s in main_box.snippets if spec_filter(s)])

    file_snippets = collections.defaultdict(list)
    for snippet in transitive_dependencies(main_names, box.index()):
        file_snippets[snippet.fname].append(snippet)

    output = sys.stdout
    if args.output:
        output = open(args.output, "w")

    for fname, snippets in file_snippets.items():
        if snippets:
            output.write("(* File: {} *)\n".format(fname))
        for snippet in snippets:
            output.writelines(snippet.lines)
            output.write("\n")

    output.close()
