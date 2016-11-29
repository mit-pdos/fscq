#!/usr/bin/python

import collections
import smtplib
import os
from email.mime.text import MIMEText

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

total_errors = sum(len(errors[fn]) for fn in errors)
print "<h1>Total errors: %d</h1>" % total_errors

for fn in errors:
  errlist = errors[fn]
  print "<hr><h2>Errors in %s (%d)</h2>" % (fn, len(errlist))
  for e in errlist:
    print '<blockquote><pre style="border: 2px solid black; background-color: yellow;">'
    for l in e: print l,
    print "</pre></blockquote>"

if total_errors > 0:
  msgbody = "Files with proof errors:\n\n"
  for fn in errors:
    msgbody += "  %s (%d errors)\n" % (fn, len(errors[fn]))
  msgbody += "\n"
  msgbody += "Detailed error output:\n\n"
  msgbody += "  http://coqdev.csail.mit.edu/runs/%s/checkproofs-errors.html" % os.path.basename(os.getcwd())
  msg = MIMEText(msgbody)
  msg['Subject'] = "%d FSCQ proof errors" % total_errors
  msg['From'] = "FSCQ builder <fscq-builder@coqdev.csail.mit.edu>"
  msg['To'] = "nickolai@csail.mit.edu,kaashoek@mit.edu,dmz@mit.edu,akonradi@mit.edu,tchajed@mit.edu,atalaymertileri@gmail.com"

  s = smtplib.SMTP('outgoing.csail.mit.edu')
  s.sendmail(msg['From'], msg['To'].split(','), msg.as_string())
  s.quit()
