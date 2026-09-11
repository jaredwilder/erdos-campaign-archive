"""Bounded known-answer gate: many POSITIVE targets, naive B <= 34 so it terminates."""
import sys, itertools
from fractions import Fraction
sys.path.insert(0, ".")
from search289 import Board, search_shard, shard_range
from verify289 import enumerate_all, check

TARGETS = [(n, d) for d in (2,3,4,5,6,7,8,9,10,11,12) for n in range(1, 2*d+1)]
fails = 0; pos = 0; tested = 0; mism = []
for B in (14, 20, 26, 34):
    board = Board(B)
    for (tnum, tden) in TARGETS:
        if Fraction(tnum, tden) > 3: continue
        for k in (1, 2, 3):
            sols = enumerate_all(k, B, Fraction(tnum, tden), cap=1)
            naive = len(sols) > 0
            fast = False; fw = None
            for a1 in shard_range(board, k, tnum, tden):
                o, p, n = search_shard(board, k, a1, 10**9, tnum, tden)
                if o == "WITNESS": fast = True; fw = p; break
                if o != "EXHAUSTED": print("UNEXPECTED", o); fails += 1
            tested += 1
            if naive: pos += 1
            if naive != fast:
                fails += 1; mism.append((tnum, tden, B, k, naive, fast, sols[:1]))
                print("MISMATCH", tnum, tden, B, k, naive, fast, sols[:1], flush=True)
            elif fast:
                ok, tot, errs = check(fw, Fraction(tnum, tden), verbose=False)
                if not ok: fails += 1; print("BAD WITNESS", fw, errs, flush=True)
print("triples tested:", tested)
print("triples with a real decomposition (non-vacuous arm):", pos)
print("mismatches:", fails)
print("GATE:", "PASS" if fails == 0 else "FAIL")
