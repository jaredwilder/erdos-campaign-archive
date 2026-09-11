#!/usr/bin/env python3
"""
residue_descent.py  --  deterministic, $0, no model in the loop.

TARGET: Erdos 1135 (Collatz), frozen Lean statement
    collatzStep n = if Even n then n / 2 else 3 * n + 1
    conjecture   : forall n > 0, exists m, collatzStep^[m] n = 1

WHAT THIS TOOL COMPUTES (and nothing else):
For each modulus 2^k and each residue r, iterate collatzStep SYMBOLICALLY on
    n = 2^k * j + r          (j a free natural number)
carrying the exact affine state  n_t = a*j + b.

The parity of a*j+b is determined for EVERY j iff a is even.  While it is
determined the symbolic iteration is exact and uniform in j; the moment a is
odd the class splits and the iteration stops.

A residue class is DESCENT-CERTIFIED at level k when, before that split, some
iterate satisfies
        a*j + b  <  2^k * j + r      for all admissible j
where admissible means n = 2^k*j + r > 1  (so j >= 1 for r in {0,1}, else j >= 0).

Output is the exact affine program per certified class -- that program is what
the Lean file formalises, one lemma per class, so every Lean lemma traces to a
row printed here.

NOTHING HERE IS A PROOF OF ANYTHING ABOUT COLLATZ.  A certified class is a
class whose descent is uniform-in-j and hence Lean-provable; an uncertified
class is a class this method does not reach.  Uncertified is NOT "no descent".
"""

import json
import sys
from fractions import Fraction

# ---------------------------------------------------------------- symbolic step

def sym_step(a, b):
    """One collatzStep on n = a*j + b.  Returns (a', b') or None if parity is
    not determined for all j (i.e. a is odd)."""
    if a % 2 == 1:
        return None                       # parity depends on j -> class splits
    if b % 2 == 0:
        return (a // 2, b // 2)           # Even -> n/2   (exact: a,b both even)
    return (3 * a, 3 * b + 1)             # Odd  -> 3n+1


def descends(a, b, mod, r, jmin):
    """True iff a*j + b < mod*j + r for every integer j >= jmin."""
    da = a - mod
    db = b - r
    if da > 0:
        return False                      # slope grows: fails for large j
    if da == 0:
        return db < 0
    # da < 0 : decreasing in j, worst case is j = jmin
    return da * jmin + db < 0


def jmin_for(mod, r):
    """Smallest j with n = mod*j + r > 1."""
    j = 0
    while mod * j + r <= 1:
        j += 1
    return j


def certify(k, r, max_steps=64):
    """Symbolically iterate class r mod 2^k.  Return the certificate dict."""
    mod = 1 << k
    jm = jmin_for(mod, r)
    a, b = mod, r
    trace = [(a, b)]
    for t in range(1, max_steps + 1):
        nxt = sym_step(a, b)
        if nxt is None:
            return {"k": k, "r": r, "mod": mod, "jmin": jm,
                    "status": "SPLIT", "steps": t - 1, "trace": trace}
        a, b = nxt
        trace.append((a, b))
        if descends(a, b, mod, r, jm):
            return {"k": k, "r": r, "mod": mod, "jmin": jm,
                    "status": "DESCENT", "steps": t,
                    "final_a": a, "final_b": b, "trace": trace}
    return {"k": k, "r": r, "mod": mod, "jmin": jm,
            "status": "BUDGET", "steps": max_steps, "trace": trace}


# ---------------------------------------------------------------- brute check

def collatz_step(n):
    return n // 2 if n % 2 == 0 else 3 * n + 1


def brute_check(cert, samples=200):
    """Independently re-run the CONCRETE map for many j in the class and check
    the symbolic affine program row by row.  Different code path from sym_step:
    this one never touches (a,b) arithmetic, it runs the integer map."""
    if cert["status"] != "DESCENT":
        return None
    mod, r, jm, steps = cert["mod"], cert["r"], cert["jmin"], cert["steps"]
    a, b = cert["final_a"], cert["final_b"]
    bad = []
    for j in range(jm, jm + samples):
        n = mod * j + r
        x = n
        for _ in range(steps):
            x = collatz_step(x)
        if x != a * j + b:
            bad.append(("affine_mismatch", j, x, a * j + b))
        if not x < n:
            bad.append(("no_descent", j, x, n))
    return {"samples": samples, "j_from": jm, "violations": bad}


# ---------------------------------------------------------------- main

def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    out = {"tool": "residue_descent.py",
           "map": "collatzStep n = if Even n then n/2 else 3n+1",
           "levels": []}
    covered_prev = set()          # residues mod 2^(k-1) already certified
    for k in range(1, kmax + 1):
        mod = 1 << k
        certs = [certify(k, r) for r in range(mod)]
        newly, inherited, open_r = [], [], []
        for c in certs:
            r = c["r"]
            if (r % (mod // 2)) in covered_prev and k > 1:
                inherited.append(r)
            elif c["status"] == "DESCENT":
                newly.append(r)
            else:
                open_r.append(r)
        covered = set(inherited) | set(newly)
        level = {
            "k": k, "modulus": mod,
            "newly_certified": newly,
            "inherited": inherited,
            "open_residues": open_r,
            "certified_count": len(covered),
            "open_count": len(open_r),
            "open_density": str(Fraction(len(open_r), mod)),
            "certificates": [c for c in certs if c["r"] in newly],
        }
        # independent brute-force re-check of every newly certified class
        checks = {}
        for c in certs:
            if c["r"] in newly:
                checks[str(c["r"])] = brute_check(c)
        level["brute_recheck"] = checks
        level["brute_violations_total"] = sum(
            len(v["violations"]) for v in checks.values())
        out["levels"].append(level)
        covered_prev = covered
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
