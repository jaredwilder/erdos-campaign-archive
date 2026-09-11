"""
erdos1 CLOSE campaign -- exact f(n) search.

f(n) := min over sum-distinct A subset of [1,N], |A| = n, of max(A).
  "sum-distinct" == all 2^n subset sums pairwise distinct
  (Erdos problem 1 / erdosproblems.com/1, formal-conjectures Erdos1.IsSumDistinctSet).

Exhaustive branch-and-bound. Subset sums are carried as a Python int bitmask;
a prefix survives only if its own 2^k subset sums are already distinct
(sum-distinctness is hereditary on subsets, so this prune is exact).

Emits a JSON receipt. Every numeral in the MSL packet that cites this file
traces to the receipt this writes.
"""
import json
import sys
import time
import argparse


def popcount(x):
    return bin(x).count("1")


def feasible(n, N, deadline):
    """Is there a sum-distinct A subset [1,N] with |A| = n?  Returns A or None.

    TIMEOUT -> raises TimeoutError, never a silent False (a search that ran out
    of clock is UNDECIDED_RESOURCE, not a negative result).
    """
    best = [None]

    # suffix_max[r] = sum of the r largest usable values <= N
    def top_sum(r, hi):
        # r largest integers <= hi
        return sum(range(hi, hi - r, -1)) if r > 0 else 0

    def rec(k, last, sums, total):
        if time.time() > deadline:
            raise TimeoutError
        if k == n:
            best[0] = cur[:]
            return True
        r = n - k
        # every subset sum is distinct => 2^n distinct values in [0, total_final]
        # so the final total must be at least 2^n - 1.
        if total + top_sum(r, N) < (1 << n) - 1:
            return False
        for x in range(last + 1, N - r + 2):
            ns = sums | (sums << x)
            if popcount(ns) != (1 << (k + 1)):
                continue
            cur.append(x)
            if rec(k + 1, x, ns, total + x):
                return True
            cur.pop()
        return False

    cur = []
    if rec(0, 0, 1, 0):
        return best[0]
    return None


def f_of_n(n, budget_s):
    """Exact f(n) by upward scan on N.  Returns (value, witness, status)."""
    t0 = time.time()
    deadline = t0 + budget_s
    N = n  # A subset [1,N] with |A| = n forces N >= n
    while True:
        try:
            w = feasible(n, N, deadline)
        except TimeoutError:
            return None, None, "UNDECIDED_RESOURCE at N=%d after %.1fs" % (N, time.time() - t0)
        if w is not None:
            return N, w, "EXACT"
        N += 1


def verify(A):
    """Independent re-check of sum-distinctness, from the definition."""
    n = len(A)
    seen = set()
    for m in range(1 << n):
        s = 0
        for i in range(n):
            if m >> i & 1:
                s += A[i]
        if s in seen:
            return False
        seen.add(s)
    return len(seen) == (1 << n)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--budget", type=float, default=120.0, help="seconds per n")
    ap.add_argument("--out", default="receipts/f-of-n.json")
    a = ap.parse_args()

    rows = []
    for n in range(1, a.nmax + 1):
        t0 = time.time()
        v, w, status = f_of_n(n, a.budget)
        dt = time.time() - t0
        row = {
            "n": n,
            "f_n": v,
            "witness": w,
            "status": status,
            "verified_from_definition": (verify(w) if w else None),
            "two_pow_n": 1 << n,
            "ratio_f_over_2n": (v / (1 << n)) if v else None,
            "seconds": round(dt, 2),
        }
        rows.append(row)
        print(json.dumps(row), flush=True)
        if v is None:
            break

    # the doubling falsifier: is f(n+1) >= 2 f(n) ?
    doubling = []
    for i in range(len(rows) - 1):
        p, q = rows[i], rows[i + 1]
        if p["f_n"] and q["f_n"]:
            doubling.append({
                "n": p["n"],
                "f_n": p["f_n"],
                "f_n_plus_1": q["f_n"],
                "two_f_n": 2 * p["f_n"],
                "doubling_holds": q["f_n"] >= 2 * p["f_n"],
            })

    out = {
        "target": "erdos:1",
        "quantity": "f(n) = min max(A) over sum-distinct A subset [1,N] with |A|=n",
        "method": "exhaustive branch-and-bound, upward scan on N, exact integer arithmetic",
        "authority": "exhaustive enumeration over the declared domain",
        "rows": rows,
        "doubling_test": doubling,
        "python": sys.version.split()[0],
    }
    with open(a.out, "w") as fh:
        json.dump(out, fh, indent=1)
    print("WROTE", a.out)


if __name__ == "__main__":
    main()
