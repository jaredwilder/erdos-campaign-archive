#!/usr/bin/env python3
"""C(12,5,2) >= 9  --  CNF emitter + independent witness verifier.

Structural route for C(13,6,3).  If B is a 20-block 6-uniform cover of all
triples of a 13-set, then for each point x the derived family
    D_x = { b \ {x} : x in b in B }
is a family of r_x FIVE-subsets of the remaining 12 points which covers every
PAIR of those 12 points (a triple {x,y,z} needs a block, and that block
contains x,y,z, so {y,z} lies in some member of D_x).  Hence r_x >= C(12,5,2).

This file decides C(12,5,2) >= 9 by asking SAT whether EIGHT 5-subsets of a
12-set can cover all 66 pairs.  UNSAT  =>  C(12,5,2) >= 9  =>  r_x >= 9.

Encoding: one variable per candidate 5-subset (C(12,5) = 792), a clause per
pair (some chosen block contains it), and a cardinality bound "at most 8
chosen" via sequential (Sinz) counter.  At-most-8 alone is used; at-least is
unnecessary (a smaller cover extends to 8 by repetition-free padding? no --
so we use exactly the at-most bound, which is the correct direction: any
cover with <= 8 blocks satisfies it, so UNSAT kills all sizes <= 8).
"""
import sys, itertools, json, hashlib

N, K, T, MAXB = 12, 5, 2, 8

blocks = list(itertools.combinations(range(N), K))
pairs  = list(itertools.combinations(range(N), T))
nb = len(blocks)

def emit_cnf(path):
    clauses = []
    # coverage: every pair in some selected block
    for p in pairs:
        lits = [i + 1 for i, b in enumerate(blocks) if set(p) <= set(b)]
        assert lits
        clauses.append(lits)
    # Sinz sequential counter, at most MAXB of x_1..x_nb
    # s[i][j] , 1<=i<=nb-1, 1<=j<=MAXB   -> var offset
    off = nb
    def s(i, j):  # i in 1..nb-1, j in 1..MAXB
        return off + (i - 1) * MAXB + j
    nvar = off + (nb - 1) * MAXB
    clauses.append([-1, s(1, 1)])
    for j in range(2, MAXB + 1):
        clauses.append([-s(1, j)])
    for i in range(2, nb):
        clauses.append([-i, s(i, 1)])
        clauses.append([-s(i - 1, 1), s(i, 1)])
        for j in range(2, MAXB + 1):
            clauses.append([-i, -s(i - 1, j - 1), s(i, j)])
            clauses.append([-s(i - 1, j), s(i, j)])
        clauses.append([-i, -s(i - 1, MAXB)])
    clauses.append([-nb, -s(nb - 1, MAXB)])
    with open(path, "w") as f:
        f.write("p cnf %d %d\n" % (nvar, len(clauses)))
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    return nvar, len(clauses)

def verify_witness(sel):
    """Independent check, shares no code with the encoder: does this list of
    5-subsets cover every pair of range(12)?"""
    need = set(itertools.combinations(range(N), T))
    got = set()
    for b in sel:
        assert len(set(b)) == K
        for p in itertools.combinations(sorted(b), T):
            got.add(p)
    return need <= got, len(need - got)

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "cnf":
        path = sys.argv[2]
        nvar, ncl = emit_cnf(path)
        h = hashlib.sha256(open(path, "rb").read()).hexdigest()
        print(json.dumps({"file": path, "n": N, "k": K, "t": T, "max_blocks": MAXB,
                          "candidate_blocks": nb, "pairs": len(pairs),
                          "vars": nvar, "clauses": ncl, "sha256": h}, indent=2))
    elif cmd == "selfcheck":
        # sanity: the ambient counting bound, and a known 9-block cover check hook
        print("candidate blocks", nb, "pairs", len(pairs))
        print("pair slots at 8 blocks:", 8 * len(list(itertools.combinations(range(K), T))))
