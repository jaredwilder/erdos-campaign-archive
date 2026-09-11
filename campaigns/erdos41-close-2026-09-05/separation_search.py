#!/usr/bin/env python3
"""Exhaustive extremal search separating the two candidate hypotheses of Erdos 41.

WEAK  (`NtupleCondition A 3`, the DeepMind formal-conjectures corpus encoding):
      all 3-element SUBSETS of A have distinct sums.
STRONG(`IsB3`, the prose condition of erdosproblems.com/41):
      all size-3 MULTISETS drawn from A have distinct sums (a true B_3 set).

For each n we compute  fw(n) = max |A|, A subset of [1,n], A weak
                and  fs(n) = max |A|, A subset of [1,n], A strong.
STRONG implies WEAK, so fs(n) <= fw(n).  Any n with fs(n) < fw(n) proves the
corpus encoding is NOT a faithful transcription of the problem statement.

Exhaustive DFS over increasing sequences with a remaining-elements bound.
Every reported extremal witness is INDEPENDENTLY re-verified from the raw
definition before it is printed.
"""
from __future__ import annotations
import itertools, json, sys, time


def verify_weak(A):
    """Re-verify from the definition: all 3-subsets have distinct sums."""
    sums = [sum(t) for t in itertools.combinations(sorted(A), 3)]
    return len(sums) == len(set(sums))


def verify_strong(A):
    """Re-verify from the definition: all size-3 multisets have distinct sums."""
    sums = [sum(t) for t in itertools.combinations_with_replacement(sorted(A), 3)]
    return len(sums) == len(set(sums))


def search(n, strong):
    """Exact max size of a WEAK (or STRONG) set inside [1,n]. Returns (size, witness)."""
    best = [0, []]
    A = []
    S3 = set()          # sums already used

    def new_sums(x):
        """Sums created by adding x, or None on collision."""
        out = []
        if strong:
            out.append(3 * x)
            for a in A:
                out.append(2 * x + a)
                out.append(x + 2 * a)
            for a, b in itertools.combinations(A, 2):
                out.append(x + a + b)
        else:
            for a, b in itertools.combinations(A, 2):
                out.append(x + a + b)
        if len(set(out)) != len(out):
            return None
        for s in out:
            if s in S3:
                return None
        return out

    def dfs(start):
        if len(A) > best[0]:
            best[0] = len(A)
            best[1] = list(A)
        for x in range(start, n + 1):
            # prune: even taking every remaining candidate cannot beat best
            if len(A) + (n - x + 1) <= best[0]:
                return
            ns = new_sums(x)
            if ns is None:
                continue
            A.append(x)
            S3.update(ns)
            dfs(x + 1)
            A.pop()
            S3.difference_update(ns)

    dfs(1)
    return best[0], best[1]


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 900.0
    t0 = time.time()
    rows = []
    for n in range(1, nmax + 1):
        if time.time() - t0 > budget:
            print(f"# TIME BUDGET REACHED at n={n}; stopping (no claim beyond n={n-1})")
            break
        fw, Aw = search(n, strong=False)
        fs, As = search(n, strong=True)
        # independent re-verification of both witnesses
        assert verify_weak(Aw), f"weak witness failed re-verification at n={n}: {Aw}"
        assert verify_strong(As), f"strong witness failed re-verification at n={n}: {As}"
        assert verify_weak(As), f"strong witness is not weak at n={n}: {As}"
        assert fs <= fw, f"MONOTONICITY VIOLATED at n={n}: fs={fs} > fw={fw}"
        rows.append({
            "n": n, "f_weak": fw, "f_strong": fs,
            "separates": fs < fw,
            "witness_weak": Aw, "witness_strong": As,
            "weak_choose3": (fw * (fw - 1) * (fw - 2)) // 6,
            "bound_3n_plus_1": 3 * n + 1,
        })
        print(f"n={n:3d}  f_weak={fw:2d}  f_strong={fs:2d}"
              f"{'   <-- SEPARATES' if fs < fw else ''}"
              f"   C(f_weak,3)={(fw*(fw-1)*(fw-2))//6:4d} <= 3n+1={3*n+1}")
    seps = [r["n"] for r in rows if r["separates"]]
    out = {
        "tool": "separation_search.py",
        "elapsed_sec": round(time.time() - t0, 2),
        "n_range": [1, rows[-1]["n"]] if rows else None,
        "separating_n": seps,
        "conclusion": ("WEAK and STRONG have different extremal sizes; the corpus "
                       "encoding is not a faithful transcription")
                      if seps else
                      ("no separation in the searched range; extremal sizes agree "
                       "for every n tested"),
        "rows": rows,
    }
    with open("receipts/separation-search.json", "w") as f:
        json.dump(out, f, indent=1)
    print("\n== separating n:", seps if seps else "NONE in range")
    print("== receipt: receipts/separation-search.json")


if __name__ == "__main__":
    main()
