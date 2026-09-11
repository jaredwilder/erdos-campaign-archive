#!/usr/bin/env python3
"""CNF for: does a (12,5,2) covering of size <= 8 exist?
Independent of the C decider: different algorithm (CDCL), different encoding.

Vars 1..792 : one per 5-subset of a 12-set, "this block is used".
Clauses:
  (a) UNIT: block {0,1,2,3,4} is used.  WLOG by relabelling: any covering has
      SOME block; relabel its 5 points to 0..4.  Sound, and it is the SAME root
      reduction the C decider uses, stated here as a unit clause.
  (b) for each of the 66 pairs, the disjunction of blocks containing it.
  (c) at most 8 used, by a Sinz sequential counter.
UNSAT  =>  no covering of size <= 8  =>  C(12,5,2) >= 9.
"""
import itertools, json, hashlib, sys

N, K, MAXB = 12, 5, 8
blocks = list(itertools.combinations(range(N), K))
pairs = list(itertools.combinations(range(N), 2))
nb = len(blocks)
ROOT = blocks.index((0, 1, 2, 3, 4)) + 1

cl = [[ROOT]]
for p in pairs:
    lits = [i + 1 for i, b in enumerate(blocks) if p[0] in b and p[1] in b]
    assert lits
    cl.append(lits)

off = nb
def s(i, j): return off + (i - 1) * MAXB + j
nvar = off + (nb - 1) * MAXB
cl.append([-1, s(1, 1)])
for j in range(2, MAXB + 1):
    cl.append([-s(1, j)])
for i in range(2, nb):
    cl.append([-i, s(i, 1)])
    cl.append([-s(i - 1, 1), s(i, 1)])
    for j in range(2, MAXB + 1):
        cl.append([-i, -s(i - 1, j - 1), s(i, j)])
        cl.append([-s(i - 1, j), s(i, j)])
    cl.append([-i, -s(i - 1, MAXB)])
cl.append([-nb, -s(nb - 1, MAXB)])

path = sys.argv[1]
with open(path, "w") as f:
    f.write("p cnf %d %d\n" % (nvar, len(cl)))
    for c in cl:
        f.write(" ".join(map(str, c)) + " 0\n")
print(json.dumps({"file": path, "root_block_unit_var": ROOT, "vars": nvar,
                  "clauses": len(cl), "max_blocks": MAXB,
                  "sha256": hashlib.sha256(open(path, "rb").read()).hexdigest()}, indent=2))
