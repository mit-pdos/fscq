#!/usr/bin/env python3

# Very dumb parallel Coq compiler, by Julian Bangert <bangert@mit.edu>
# Thanks to Nickolai for telling me about Show Proof, and Benjamin Barenblat for showing me refine
import argparse
import sys
import pexpect
import re

def coq_remove_comments(str):
    #This is hairy because Coq has nested comments
    # if this is a performance issue, add a proper parser for coq.
    out = ""
    comment = 0
    i = 0
    while(i < len(str)):
        if str[i:i+2] == "(*":
            comment+=1
            i+=1
        elif str[i:i+2] == "*)":
            comment-=1
            i+=1
        elif comment == 0:
            out += str[i]
        i+=1
    if comment > 0:
        panic("Unterminated comment")
    return out
def coqtop_simpl_proof(term):
    # Takes a coq proof (up to, but not including Qed.) and returns a
    # much simpler proof
    prompt = "\<\/prompt\>"
    coqtop = pexpect.spawn('coqtop -emacs')
    #print("Sending")
    #print(term)
    #coqtop.logfile = sys.stdout.buffer
    coqtop.expect(prompt)
    coqtop.sendline(term)
    coqtop.expect("No more subgoals.")
    #coqtop.logfile = sys.stdout.buffer
    coqtop.expect(prompt)
    #coqtop.logfile = None
    coqtop.sendline(" Set Printing Depth 2000.")
    coqtop.expect("\<prompt\>")
    coqtop.sendline(" Set Printing All.")
    coqtop.expect("\<prompt\>")
    coqtop.sendline(" Show Proof.")
    coqtop.expect("Show Proof.")
    coqtop.expect("\<prompt\>")
    #coqtop.logfile = None
    proofterm = coqtop.before.decode("utf-8")
    return " refine (" + proofterm + "). Qed. "
argparser = argparse.ArgumentParser()
argparser.add_argument('file')
args = argparser.parse_args()
contents = open(args.file).read()

prefix = ""
proof_query = ""
proof_term = ""
proof_depth = 0


fragments = coq_remove_comments(contents).split(".")

pure = "" 
# fragments.pop().strip() # not removing this adds an extra colon.
    
for frag_raw in fragments: #
    frag = frag_raw.strip()
    frag_raw += "."
    if  proof_depth <= 0:
        prefix += frag_raw
        pure += frag_raw
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
                pure += frag_raw
                prefix += frag_raw
            else: #  frag == 'Qed':
                prefix += ' Admitted. '
                pure += coqtop_simpl_proof(proof_query)
        else:
            proof_query += frag_raw




print(pure)
#print ("Query", proof_query)
