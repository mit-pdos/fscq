#!/usr/bin/python

import sys

def panic(s):
  print >> sys.stderr, s
  sys.exit(1)

in_proof = False

for l in sys.stdin.readlines():
  if not in_proof:
    print l,
  if in_proof and l.strip == 'Defined.':
    panic("Skipped a proof that ended up being Defined.")
  if in_proof and l.strip() in ('Qed.', 'Admitted.'):
    print "Admitted."
    in_proof = False
  if l.strip() == 'Proof.':
    in_proof = True

if in_proof:
  panic("Still in proof mode at the end of file!")
