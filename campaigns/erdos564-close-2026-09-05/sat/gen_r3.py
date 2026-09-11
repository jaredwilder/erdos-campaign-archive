#!/usr/bin/env python3
"""
DIMACS generator for the 3-uniform diagonal hypergraph Ramsey number r_3(n) = R(n,n;3).

A 2-colouring of the triples of [N] with no monochromatic n-set witnesses r_3(n) > N.
Variable x_{abc} (a<b<c) = TRUE means the triple {a,b,c} is RED.
For every n-subset S of [N] we forbid "all triples of S red" and "all triples of S blue".

Usage:  python gen_r3.py N n out.cnf
"""
import sys
from itertools import combinations


def main() -> int:
    if len(sys.argv) != 4:
        print(__doc__)
        return 2
    N, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]

    var = {}
    for i, t in enumerate(combinations(range(N), 3), start=1):
        var[t] = i
    nvars = len(var)

    clauses = []
    for S in combinations(range(N), n):
        lits = [var[t] for t in combinations(S, 3)]
        clauses.append([-v for v in lits])   # not all red
        clauses.append([v for v in lits])    # not all blue

    with open(out, "w") as f:
        f.write(f"c r_3({n}) > {N} ?  SAT => yes (witness colouring); UNSAT => r_3({n}) <= {N}\n")
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    print(f"wrote {out}: N={N} n={n} vars={nvars} clauses={len(clauses)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
