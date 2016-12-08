#!/usr/bin/python3

import collections
import smtplib
import os
import sys
from email.mime.text import MIMEText

if len(sys.argv) > 1:
  build_name = ' ' + ' '.join(sys.argv[1:])
else:
  build_name = ''

email_list = 'nickolai@csail.mit.edu,kaashoek@mit.edu,dmz@mit.edu,akonradi@mit.edu,tchajed@mit.edu,atalaymertileri@gmail.com'

f = open("checkproofs-errors.txt", encoding="utf-8")

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

admits = collections.defaultdict(int)

for fn in os.listdir("fscq/src/coqbuild"):
  if not fn.endswith(".v"):
    continue
  with open("fscq/src/coqbuild/%s" % fn, encoding="utf-8") as f:
    for l in f.readlines():
      if 'Admitted' in l:
        admits[fn.replace(".v", "")] += 1

html = open("checkproofs-errors.html", "w", encoding="utf-8")
total_errors = sum(len(errors[fn]) for fn in errors)
total_admits = sum(admits[fn] for fn in admits)
html.write("<h1>Total: %d errors, %d admits</h1>\n" % (total_errors, total_admits))

for fn in sorted({**errors, **admits}):
  errlist = errors[fn]
  num_admits = admits[fn]
  html.write("<hr><h2>%s: %d errors, %d admits</h2>\n" % (fn, len(errlist), num_admits))
  for e in errlist:
    html.write('<blockquote><pre style="border: 2px solid black; background-color: yellow;">\n')
    for l in e: html.write(l)
    html.write("</pre></blockquote>\n")

html.close()

if total_errors > 0 or total_admits > 0:
  msgbody = "Files with proof errors or admits:\n\n"
  for fn in sorted({**errors, **admits}):
    msgbody += "  %s: %d errors, %d admits\n" % (fn, len(errors[fn]), admits[fn])
  msgbody += "\n"
  msgbody += "Detailed error output:\n\n"
  msgbody += "  http://coqdev.csail.mit.edu/runs/%s/checkproofs-errors.html" % os.path.basename(os.getcwd())
  msg = MIMEText(msgbody)
  msg['Subject'] = "FSCQ%s: %d proof errors, %d admits" % (build_name, total_errors, total_admits)
  msg['From'] = "FSCQ builder <fscq-builder@coqdev.csail.mit.edu>"
  msg['To'] = email_list

  s = smtplib.SMTP('outgoing.csail.mit.edu')
  s.sendmail(msg['From'], msg['To'].split(','), msg.as_string())
  s.quit()
