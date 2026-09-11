#!/usr/bin/env python3
"""
INDEPENDENT verifier for a claimed 2-colouring of the triples of [N] with no
monochromatic n-set.  Does not trust the SAT solver: re-reads the model, rebuilds the
colouring from scratch, and checks every n-subset by brute force.

Usage:  python verify_witness.py <cadical.log> N n
Exit 0 and prints VERIFIED only if every n-subset of [N] contains both colours.
"""
import sys
from itertools import combinations


def main() -> int:
    log, N, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])

    sat = False
    lits = []
    with open(log) as f:
        for line in f:
            if line.startswith("s "):
                sat = line.split()[1] == "SATISFIABLE"
            elif line.startswith("v "):
                lits.extend(int(x) for x in line.split()[1:])
    if not sat:
        print("NOT SATISFIABLE in log")
        return 1
    lits = [x for x in lits if x != 0]

    triples = list(combinations(range(N), 3))
    if len(lits) != len(triples):
        print(f"FAIL: model has {len(lits)} literals, expected {len(triples)}")
        return 1

    colour = {}
    for idx, t in enumerate(triples):
        v = lits[idx]
        if abs(v) != idx + 1:
            print(f"FAIL: literal {v} out of order at index {idx}")
            return 1
        colour[t] = v > 0

    bad = 0
    for S in combinations(range(N), n):
        cs = {colour[t] for t in combinations(S, 3)}
        if len(cs) == 1:
            bad += 1
            if bad <= 3:
                print(f"MONOCHROMATIC {'RED' if cs.pop() else 'BLUE'} {n}-set: {S}")
    if bad:
        print(f"FAIL: {bad} monochromatic {n}-sets")
        return 1

    red = sum(1 for t in triples if colour[t])
    print(f"VERIFIED: 2-colouring of the {len(triples)} triples of [{N}] "
          f"({red} red / {len(triples) - red} blue) has NO monochromatic {n}-set.")
    print(f"          Checked all {len(list(combinations(range(N), n)))} {n}-subsets.")
    print(f"          Therefore r_3({n}) = R({n},{n};3) > {N}, i.e. >= {N + 1}.")
    # canonical serialisation of the witness
    bits = "".join("1" if colour[t] else "0" for t in triples)
    print(f"WITNESS (colex order on triples, 1=red): {bits}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
