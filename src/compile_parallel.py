#!/usr/bin/env python3

# Very dumb parallel Coq compiler, by Julian Bangert <bangert@mit.edu>
#
# Thanks to Nickolai for telling me about Show Proof, and Benjamin Barenblat
# for showing me refine

import argparse
import sys
import pexpect
import re
import concurrent.futures
import multiprocessing

debug = False
max_workers = multiprocessing.cpu_count()

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
    elif str[i:i+2] == "*)":
      comment -= 1
      i += 1
    elif comment == 0:
      out += str[i]
    i += 1
  if comment > 0:
    panic("Unterminated comment")
  return out

def coqtop_simpl_proof(term):
  # Takes a coq proof (up to, but not including Qed.) and returns an
  # explicit Coq term for the resulting proof.
  prompt = "\<\/prompt\>"
  coqtop = pexpect.spawn('coqtop -emacs')

  if debug:
    print("Sending", file=sys.stderr)
    print("<<", term, ">>", file=sys.stderr)
    coqtop.logfile = sys.stderr.buffer

  coqtop.expect(prompt)

  coqtop.sendline(term)
  coqtop.expect("No more subgoals.")
  coqtop.expect(prompt)

  coqtop.sendline("Set Printing Depth 2000.")
  coqtop.expect("\<prompt\>")

  coqtop.sendline("Set Printing All.")
  coqtop.expect("\<prompt\>")

  coqtop.sendline("Show Proof.")
  coqtop.expect("Show Proof.")
  coqtop.expect("No more subgoals.")

  proofterm = coqtop.before.decode("utf-8")
  return " refine (" + proofterm + "). Qed. "

def queue_to_string(queue):
  val = ""
  for x in queue:
    if isinstance(x, str):
      val += x
    else: # future
      val += x.result()
  return val

argparser = argparse.ArgumentParser()
argparser.add_argument('file')
args = argparser.parse_args()
contents = open(args.file).read()

prefix = ""
proof_query = ""
proof_term = ""
proof_depth = 0


fragments = coq_remove_comments(contents).split(".")

pure = []
fragments.pop() # not removing this adds an extra dot

executor = concurrent.futures.ThreadPoolExecutor(max_workers=max_workers)
for frag_raw in fragments:
  frag = frag_raw.strip()
  frag_raw += "."
  if proof_depth <= 0:
    prefix += frag_raw
    pure.append(frag_raw)

  if frag == "Proof":
    if proof_depth != 0:
      panic("Nested proofs are not well tested")
    if proof_depth <= 0:
      # prefix += " Proof. "
      # pure += " Proof. "
      proof_query = prefix
    proof_depth += 1
  else:
    if frag in ('Qed', 'Admitted', 'Abort'):
      proof_depth = 0
      if frag in ('Admitted', 'Abort') :
        pure.append(frag_raw)
        prefix += frag_raw
      else:  # frag == 'Qed':
        prefix += ' Admitted. '
        pure.append(executor.submit(coqtop_simpl_proof, proof_query))
    else:
      proof_query += frag_raw

print(queue_to_string(pure))
# print ("Query", proof_query)
