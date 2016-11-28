#!/usr/bin/python

import collections

f = open("checkproofs-errors.txt")

ignore_prefixes = [
  "make[1]: ",
  "make: ",
  "Makefile:",
  "Makefile.coq:",
  "Script started on ",
  "( cd coqbuild ",
  "\"coqc\"  -q  -R",
  "Script done on ",
]

errors = collections.defaultdict(list)
current_error = []

for l in f.readlines():
  if any(l.startswith(prefix) for prefix in ignore_prefixes):
    continue
  if l.startswith("File "):
    err_file = l.split(" ")[1].split(":")[0]
    current_error = []
    errors[err_file].append(current_error)
  current_error.append(l)

print "<h1>Total errors: %d</h1>" % sum(len(errors[fn]) for fn in errors)

for fn in errors:
  errlist = errors[fn]
  print "<hr><h2>Errors in %s (%d)</h2>" % (fn, len(errlist))
  for e in errlist:
    print '<blockquote><pre style="border: 2px solid black; background-color: yellow;">'
    for l in e: print l,
    print "</pre></blockquote>"
