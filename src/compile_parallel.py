#!/usr/bin/env python3

# Very dumb parallel Coq compiler, by Julian Bangert <bangert@mit.edu>
#
# Thanks to Nickolai for telling me about Show Proof, and Benjamin Barenblat
# for showing me refine

import argparse
import sys
import re
import concurrent.futures
import multiprocessing
import subprocess

debug = False
max_workers = multiprocessing.cpu_count()
coqtop = ("coqtop", "-R", "coqbuild", "Fscq")

def coq_remove_comments(str):
  # This is hairy because Coq has nested comments.
  # If this is a performance issue, add a proper parser for coq.
  out = ""
  comment = 0
  i = 0
  while i < len(str):
    if str[i:i+2] == "(*":
      comment += 1
      i += 1
    elif comment > 0 and str[i:i+2] == "*)":
      comment -= 1
      i += 1
    elif comment == 0:
      out += str[i]
    i += 1
  if comment > 0:
    panic("Unterminated comment")
  return out

def coqtop_simpl_proof(coqtop, term):
  # Takes a coq proof (up to, but not including Qed.) and returns an
  # explicit Coq term for the resulting proof.
  p = subprocess.Popen(coqtop, stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)

  if debug:
    print("Sending", file=sys.stderr)
    print("<<", term, ">>", file=sys.stderr)

  cin = term + \
        "\n" + \
        "Set Printing Depth 2000.\n" + \
        "Set Printing All.\n" + \
        "Inductive SYNC_FLAG := .\n" + \
        "Show Proof.\n"
  (cout, cerr) = p.communicate(cin.encode('utf-8'))

  proofterm = ""
  syncdone = False
  inproof = False
  problem = False
  for cl in cout.decode('utf-8', 'replace').splitlines():
    if inproof and cl == 'No more subgoals.':
      inproof = False
      syncdone = False
    if inproof:
      proofterm += cl + "\n"
    if syncdone and not inproof:
      if cl == 'No more subgoals.':
        inproof = True
      else:
        problem = True
    if cl == 'SYNC_FLAG_rec is defined':
      syncdone = True
  if inproof or syncdone or proofterm == "":
    problem = True

  if problem:
    print("Unable to complete the proof:", file=sys.stderr)
    print("Proof script sent to coqtop: <<" + cin + ">>", file=sys.stderr)
    print("Result from coqtop: <<" + cout.decode('utf-8', 'replace') + ">>", file=sys.stderr)
    panic("Proof worker unable to complete the proof.")
  else:
    return "refine (" + proofterm + ").\n" + "Qed.\n"

def queue_to_string(queue):
  val = ""
  for x in queue:
    if isinstance(x, str):
      val += x
    else: # future
      val += x.result()
  return val

def print_queue(queue):
  for x in queue:
    if isinstance(x, str):
      print(x, end="")
    else: # future
      print(x.result(), end="")

argparser = argparse.ArgumentParser()
argparser.add_argument('file')
args = argparser.parse_args()
contents = open(args.file).read()

prefix = ""
proof_query = ""
proof_term = ""
in_proof = False

lines = coq_remove_comments(contents).splitlines()

pure = []

executor = concurrent.futures.ThreadPoolExecutor(max_workers=max_workers)
for line_raw in lines:
  line = line_raw + "\n"

  if not in_proof:
    prefix += line
    pure.append(line)

  if in_proof:
    if line.strip() in ("Admitted.", "Abort."):
      ## Do not bother trying to construct proofs
      in_proof = False
      prefix += line
      pure.append(line)
    elif line.strip() in ("Qed.",):
      in_proof = False
      prefix += "Admitted.\n"
      pure.append(executor.submit(coqtop_simpl_proof, coqtop, proof_query))
    else:
      proof_query += line

  if line.strip() == "Proof.":
    if in_proof:
      panic("Nested proofs are not supported")
    proof_query = prefix
    in_proof = True

if in_proof:
  panic("Still in proof mode at the end of file!")

print_queue(pure)
