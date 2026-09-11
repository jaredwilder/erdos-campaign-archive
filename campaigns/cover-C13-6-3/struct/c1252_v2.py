#!/usr/bin/env python3
"""C(12,5,2): exhaustive decision at MAXB, with degree-deficit pruning.

Search (complete): repeatedly take the lexicographically least UNCOVERED pair
{a,b}; every covering extending the current partial family contains a block
through {a,b}, so branch over exactly those C(10,3)=120 blocks.

Root reduction (relabelling, sound): any covering can be relabelled so that one
of its blocks is {0,1,2,3,4}; fix that as block one.

PRUNES, both proved in the docstring of the paper trail:
 P1  a block covers at most C(5,2)=10 new pairs, so uncovered <= 10*rem.
 P2  fix a point x and let u_x be the number of uncovered pairs at x.  A block
     containing x covers exactly 4 pairs at x; a block avoiding x covers none.
     So the number of remaining blocks CONTAINING x is at least ceil(u_x/4).
     Each remaining block contains exactly 5 points, so
         sum_x ceil(u_x / 4)  <=  5 * rem.
     Also  max_x ceil(u_x / 4) <= rem.

MODES
  decide   exhaustive: is there a covering of size <= MAXB?
  find     randomized greedy, to WITNESS that a covering of size MAXB exists
           (calibration of the model, verified from the definition).
"""
import sys, os, itertools, json, time, random

N, K = 12, 5
MAXB = int(os.environ.get("MAXB", 8))
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
THRU = {p: [(b, m) for (b, m) in BLOCKS if p[0] in b and p[1] in b] for p in PAIRS}
# pairs incident to each point, as a bitmask
AT = []
for x in range(N):
    m = 0
    for i, p in enumerate(PAIRS):
        if x in p:
            m |= 1 << i
    AT.append(m)

nodes = 0
found = None

def prune(covered, rem):
    unc_mask = FULL & ~covered
    unc = bin(unc_mask).count("1")
    if unc > 10 * rem:
        return True
    tot = 0
    for x in range(N):
        ux = bin(unc_mask & AT[x]).count("1")
        need = -(-ux // 4)
        if need > rem:
            return True
        tot += need
    if tot > 5 * rem:
        return True
    return False

def dfs(covered, chosen, depth):
    global nodes, found
    if found is not None:
        return
    nodes += 1
    if covered == FULL:
        found = list(chosen)
        return
    rem = MAXB - depth
    if rem == 0 or prune(covered, rem):
        return
    for i, p in enumerate(PAIRS):
        if not (covered >> i) & 1:
            least = p
            break
    for (b, m) in THRU[least]:
        chosen.append(b)
        dfs(covered | m, chosen, depth + 1)
        chosen.pop()
        if found is not None:
            return

def verify(sel):
    """Independent recheck FROM THE DEFINITION. No bitmasks, no shared tables."""
    need = set(itertools.combinations(range(N), 2))
    got = set()
    for b in sel:
        assert len(b) == K and len(set(b)) == K and all(0 <= v < N for v in b)
        for p in itertools.combinations(sorted(b), 2):
            got.add(p)
    return need <= got, sorted(need - got)

def greedy_find(budget, tries=200000, seed=12345):
    rng = random.Random(seed)
    for _ in range(tries):
        cov, sel = 0, []
        while cov != FULL and len(sel) < budget:
            for i, p in enumerate(PAIRS):
                if not (cov >> i) & 1:
                    least = p
                    break
            cands = THRU[least]
            best = max(bin((~cov) & m).count("1") for (_, m) in cands)
            pick = rng.choice([c for c in cands if bin((~cov) & c[1]).count("1") == best])
            sel.append(pick[0]); cov |= pick[1]
        if cov == FULL:
            return sel
    return None

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "decide"
    t0 = time.time()
    if mode == "find":
        sel = greedy_find(MAXB)
        out = {"mode": "find", "max_blocks": MAXB, "seconds": round(time.time() - t0, 2)}
        if sel is None:
            out["verdict"] = "GREEDY_FOUND_NONE"
        else:
            ok, missing = verify(sel)
            out["verdict"] = "COVER_FOUND"
            out["cover"] = [list(b) for b in sel]
            out["size"] = len(sel)
            out["independent_verification_from_definition"] = ok
            out["uncovered_after_recheck"] = missing
        print(json.dumps(out, indent=2))
    else:
        b0 = (0, 1, 2, 3, 4)
        m0 = 0
        for p in itertools.combinations(b0, 2):
            m0 |= 1 << PIDX[p]
        dfs(m0, [b0], 1)
        out = {"mode": "decide", "n": N, "k": K, "t": 2, "max_blocks": MAXB,
               "candidate_blocks": len(BLOCKS), "pairs": NP,
               "root_block_fixed_wlog": list(b0),
               "search_nodes": nodes, "seconds": round(time.time() - t0, 2)}
        if found is None:
            out["verdict"] = "EXHAUSTED_NO_COVER"
            out["conclusion"] = "C(12,5,2) > %d" % MAXB
        else:
            ok, missing = verify(found)
            out["verdict"] = "COVER_FOUND"
            out["cover"] = [list(b) for b in found]
            out["independent_verification_from_definition"] = ok
            out["uncovered_after_recheck"] = missing
            out["conclusion"] = "C(12,5,2) <= %d" % len(found)
        print(json.dumps(out, indent=2))
