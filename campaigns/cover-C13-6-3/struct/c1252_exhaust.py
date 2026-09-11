#!/usr/bin/env python3
"""EXHAUSTIVE decision of C(12,5,2) <= 8, by canonical-uncovered-pair DFS.

A (12,5,2) covering is a family of 5-subsets of a 12-set meeting every pair.
Search: repeatedly take the LEXICOGRAPHICALLY LEAST uncovered pair {a,b}; any
cover must contain a block containing it; branch over exactly the C(10,3)=120
blocks that contain {a,b}.  This is complete (no cover is missed) and needs no
symmetry argument to be sound.

Pruning: with r blocks left, at most 10*r further pairs can be covered, so if
uncovered > 10*r the branch dies.

Additional SOUND symmetry reduction at the root only: relabelling points is a
bijection of coverings, so WLOG the first block is {0,1,2,3,4}.  The least
uncovered pair at the start is {0,1} and every block through it is equivalent
under a permutation fixing {0,1}? -- NOT true in general, so this reduction is
NOT applied.  We instead fix block 1 = {0,1,2,3,4}: the least uncovered pair of
the empty family is {0,1}; any cover has a block b through {0,1}; relabel the
other three points of b to 2,3,4 and the rest arbitrarily.  This is a genuine
relabelling, hence WLOG-sound.

Verdict:
  no cover of size <= 8 found  ->  C(12,5,2) >= 9    (UNSAT, exhaustive)
  a cover found                ->  printed, and re-verified from the definition
"""
import sys, itertools, json, time

import os
N, K, MAXB = 12, 5, int(os.environ.get("MAXB", 8))
PAIRS = list(itertools.combinations(range(N), 2))
PIDX = {p: i for i, p in enumerate(PAIRS)}
NP = len(PAIRS)
FULL = (1 << NP) - 1

BLOCKS = []
for b in itertools.combinations(range(N), K):
    m = 0
    for p in itertools.combinations(b, 2):
        m |= 1 << PIDX[p]
    BLOCKS.append((b, m))

# blocks through each pair
THRU = {p: [(b, m) for (b, m) in BLOCKS if p[0] in b and p[1] in b] for p in PAIRS}

nodes = 0
found = None

def dfs(covered, chosen, depth):
    global nodes, found
    if found is not None:
        return
    nodes += 1
    if covered == FULL:
        found = list(chosen)
        return
    rem = MAXB - depth
    if rem == 0:
        return
    # least uncovered pair
    for i, p in enumerate(PAIRS):
        if not (covered >> i) & 1:
            least = p
            break
    # prune: count uncovered
    unc = NP - bin(covered).count("1")
    if unc > 10 * rem:
        return
    for (b, m) in THRU[least]:
        chosen.append(b)
        dfs(covered | m, chosen, depth + 1)
        chosen.pop()
        if found is not None:
            return

def verify(sel):
    """Independent re-verification FROM THE DEFINITION. Shares no bitmask code."""
    need = set(itertools.combinations(range(N), 2))
    got = set()
    for b in sel:
        assert len(b) == K and len(set(b)) == K and all(0 <= v < N for v in b)
        for p in itertools.combinations(sorted(b), 2):
            got.add(p)
    return need <= got, sorted(need - got)

if __name__ == "__main__":
    t0 = time.time()
    # WLOG first block = {0,1,2,3,4}: the least uncovered pair is {0,1}; a cover
    # has some block through it; relabel its other 3 points to 2,3,4.
    b0 = (0, 1, 2, 3, 4)
    m0 = 0
    for p in itertools.combinations(b0, 2):
        m0 |= 1 << PIDX[p]
    dfs(m0, [b0], 1)
    dt = time.time() - t0
    out = {"n": N, "k": K, "t": 2, "max_blocks": MAXB,
           "candidate_blocks": len(BLOCKS), "pairs": NP,
           "root_block_fixed_wlog": list(b0),
           "search_nodes": nodes, "seconds": round(dt, 2)}
    if found is None:
        out["verdict"] = "NO_COVER_OF_SIZE_AT_MOST_8"
        out["conclusion"] = "C(12,5,2) >= 9"
    else:
        ok, missing = verify(found)
        out["verdict"] = "COVER_FOUND"
        out["cover"] = [list(b) for b in found]
        out["independent_verification_from_definition"] = ok
        out["uncovered_pairs_after_recheck"] = missing
        out["conclusion"] = "C(12,5,2) <= %d" % len(found)
    print(json.dumps(out, indent=2))
