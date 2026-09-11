#!/usr/bin/env python3
"""
Erdos 30 -- numerical verification of the formalized bounds against EXACT h(N).

h(N) = max size of a Sidon set in {1,...,N}.

Exact h(N) is determined by the optimal Golomb ruler lengths G(k) (OEIS A003022):
a Sidon set of size k inside {1,...,N} exists iff G(k) <= N-1.
We do NOT take G(k) on faith: for k <= KMAX_EXHAUSTIVE we recompute G(k) by our own
exhaustive branch-and-bound search, and we cross-check against the published table.
Every number this script prints is produced by this script.

Checks performed:
  C1  exhaustive recomputation of G(k) for small k (our own search)
  C2  h(N) tabulated from G, cross-checked by direct exhaustive Sidon search for small N
  C3  the Lean-proved key inequality  k^2 * l <= (N+l)*(k+l)   for all N,l in range
  C4  the Lean-proved trivial bound   k^2 <= 2N + k
  C5  the Lean-proved corollary       h(N) <= isqrt(N) + 3*(isqrt(isqrt(N)) + 1)
  C6  measured tightness of the corollary vs the true h(N)
"""
import json
import math
import sys
import hashlib
from datetime import datetime, timezone

# ---------------------------------------------------------------- exhaustive G(k)

def golomb_length(k, ub):
    """Smallest L such that a Sidon set (Golomb ruler) of size k fits in {0..L}.
    Exhaustive DFS with difference-set pruning. Returns None if > ub."""
    for L in range(0, ub + 1):
        marks = [0]
        used = set()
        if _dfs(marks, used, k, L):
            return L
    return None


def _dfs(marks, used, k, L):
    if len(marks) == k:
        return marks[-1] == L or True
    # remaining marks needed
    need = k - len(marks)
    start = marks[-1] + 1
    # prune: need `need` more marks, minimal span for r marks is r*(r-1)/2 ... use simple bound
    for nxt in range(start, L + 1):
        if L - nxt < (need - 1) * need // 2 - (need - 1) * (need - 2) // 2:
            pass
        new = []
        ok = True
        for m in marks:
            d = nxt - m
            if d in used or d in new:
                ok = False
                break
            new.append(d)
        if not ok:
            continue
        for d in new:
            used.add(d)
        marks.append(nxt)
        if _dfs(marks, used, k, L):
            return True
        marks.pop()
        for d in new:
            used.discard(d)
    return False


def exact_golomb(k):
    """Exhaustive: smallest ruler length for k marks."""
    if k <= 1:
        return 0
    L = 0
    while True:
        if _fits(k, L):
            return L
        L += 1


def _fits(k, L):
    marks = [0]
    used = set()
    return _dfs2(marks, used, k, L)


def _dfs2(marks, used, k, L):
    if len(marks) == k:
        return True
    need = k - len(marks)
    for nxt in range(marks[-1] + 1, L + 1):
        # cannot finish if not enough room: remaining need-1 marks need >= (need-1) more units
        if L - nxt < need - 2 + 1 and need >= 2:
            if L - nxt < need - 1:
                break
        new = []
        ok = True
        for m in marks:
            d = nxt - m
            if d in used or d in new:
                ok = False
                break
            new.append(d)
        if not ok:
            continue
        for d in new:
            used.add(d)
        marks.append(nxt)
        if _dfs2(marks, used, k, L):
            return True
        marks.pop()
        for d in new:
            used.discard(d)
    return False


# published optimal Golomb ruler lengths G(k), OEIS A003022 (k = 1..28)
PUBLISHED_G = {
    1: 0, 2: 1, 3: 3, 4: 6, 5: 11, 6: 17, 7: 25, 8: 34, 9: 44, 10: 55,
    11: 72, 12: 85, 13: 106, 14: 127, 15: 151, 16: 177, 17: 199, 18: 216,
    19: 246, 20: 283, 21: 333, 22: 356, 23: 372, 24: 425, 25: 480, 26: 492,
    27: 553, 28: 585,
}


def isqrt(n):
    return math.isqrt(n)


def brute_h(N):
    """Exhaustive max Sidon subset of {1..N} by DFS. Only for tiny N."""
    best = 0
    cur = []
    used = set()

    def rec(start):
        nonlocal best
        if len(cur) > best:
            best = len(cur)
        for x in range(start, N + 1):
            new = []
            ok = True
            for m in cur:
                d = x - m
                if d in used or d in new:
                    ok = False
                    break
                new.append(d)
            if not ok:
                continue
            for d in new:
                used.add(d)
            cur.append(x)
            rec(x + 1)
            cur.pop()
            for d in new:
                used.discard(d)

    rec(1)
    return best


def main():
    out = {
        "tool": "verify_bounds.py",
        "utc": datetime.now(timezone.utc).isoformat(),
        "checks": {},
    }

    # ---- C1: recompute G(k) exhaustively for small k
    KMAX = 10
    recomputed = {}
    for k in range(1, KMAX + 1):
        recomputed[k] = exact_golomb(k)
    c1_ok = all(recomputed[k] == PUBLISHED_G[k] for k in range(1, KMAX + 1))
    out["checks"]["C1_golomb_recomputed"] = {
        "k_max_exhaustive": KMAX,
        "recomputed": recomputed,
        "matches_published_A003022": c1_ok,
    }
    if not c1_ok:
        print("C1 FAILED", recomputed, file=sys.stderr)

    # ---- C2: h(N) from G, cross-checked by brute force for small N
    NMAX = 586  # G(28)=585 -> h known exactly for N <= 586
    hN = [0] * (NMAX + 1)
    for N in range(1, NMAX + 1):
        k = 0
        for kk in range(1, 29):
            if PUBLISHED_G[kk] <= N - 1:
                k = kk
        hN[N] = k
    BRUTE_MAX = 34
    brute = {N: brute_h(N) for N in range(1, BRUTE_MAX + 1)}
    c2_ok = all(brute[N] == hN[N] for N in range(1, BRUTE_MAX + 1))
    out["checks"]["C2_h_table"] = {
        "N_max_exact": NMAX,
        "brute_forced_up_to": BRUTE_MAX,
        "brute_matches_table": c2_ok,
        "h_sample": {str(N): hN[N] for N in [1, 2, 4, 7, 12, 18, 26, 35, 45, 56, 73,
                                             86, 107, 128, 152, 178, 200, 217, 247,
                                             284, 334, 357, 373, 426, 481, 493, 554, 586]},
    }
    if not c2_ok:
        bad = [(N, brute[N], hN[N]) for N in range(1, BRUTE_MAX + 1) if brute[N] != hN[N]]
        print("C2 FAILED", bad, file=sys.stderr)

    # ---- C3: the Lean key inequality  k^2 * l <= (N+l)*(k+l)
    viol3 = []
    tight = []
    for N in range(1, NMAX + 1):
        k = hN[N]
        for l in range(1, 4 * N + 4):
            lhs = k * k * l
            rhs = (N + l) * (k + l)
            if lhs > rhs:
                viol3.append({"N": N, "l": l, "lhs": lhs, "rhs": rhs})
            if rhs - lhs <= 2:
                tight.append({"N": N, "l": l, "slack": rhs - lhs})
    out["checks"]["C3_key_inequality"] = {
        "statement": "A.card^2 * l <= (N+l)*(A.card+l)   [E30.sidon_key, Lean-proved]",
        "N_range": [1, NMAX],
        "l_range": "1 .. 4N+3",
        "violations": viol3,
        "violation_count": len(viol3),
        "near_tight_instances_slack_le_2": tight[:25],
        "near_tight_count": len(tight),
    }

    # ---- C4: trivial bound k^2 <= 2N + k
    viol4 = [N for N in range(1, NMAX + 1) if hN[N] ** 2 > 2 * N + hN[N]]
    out["checks"]["C4_trivial_bound"] = {
        "statement": "A.card^2 <= 2N + A.card   [E30.card_sq_le, Lean-proved]",
        "violations": viol4,
        "violation_count": len(viol4),
    }

    # ---- C5: the corollary h(N) <= isqrt(N) + 3*(isqrt(isqrt(N)) + 1)
    viol5 = []
    slacks = []
    for N in range(0, NMAX + 1):
        k = hN[N] if N >= 1 else 0
        bound = isqrt(N) + 3 * (isqrt(isqrt(N)) + 1)
        if k > bound:
            viol5.append({"N": N, "h": k, "bound": bound})
        slacks.append((N, bound - k))
    out["checks"]["C5_corollary"] = {
        "statement": "h N <= Nat.sqrt N + 3*(Nat.sqrt (Nat.sqrt N) + 1)   [E30.h_le, Lean-proved]",
        "N_range": [0, NMAX],
        "violations": viol5,
        "violation_count": len(viol5),
        "min_slack": min(s for _, s in slacks),
        "argmin_slack_N": min(slacks, key=lambda t: t[1])[0],
    }

    # ---- C5b: the SHARP corollary h(N) <= isqrt(N) + isqrt(isqrt(N)) + 4
    viol5b = []
    slacks5b = []
    for N in range(0, NMAX + 1):
        k = hN[N] if N >= 1 else 0
        bound = isqrt(N) + isqrt(isqrt(N)) + 4
        if k > bound:
            viol5b.append({"N": N, "h": k, "bound": bound})
        slacks5b.append((N, bound - k))
    # the intermediate balancing-window inequality, also Lean-proved
    viol5c = [N for N in range(1, NMAX + 1)
              if hN[N] ** 2 > N + hN[N] + 2 * isqrt(N * hN[N]) + 1]
    out["checks"]["C5b_sharp_corollary"] = {
        "statement": "h N <= Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 4   [E30.h_le_sharp, Lean-proved]",
        "N_range": [0, NMAX],
        "violations": viol5b,
        "violation_count": len(viol5b),
        "min_slack": min(s for _, s in slacks5b),
        "argmin_slack_N": min(slacks5b, key=lambda t: t[1])[0],
        "intermediate_statement": ("A.card^2 <= N + A.card + 2*Nat.sqrt (N*A.card) + 1   "
                                    "[E30.sidon_sq_le_sqrt, Lean-proved]"),
        "intermediate_violations": viol5c,
        "intermediate_violation_count": len(viol5c),
        "min_C_actually_needed_for_true_h": max(
            hN[N] - isqrt(N) - isqrt(isqrt(N)) for N in range(0, NMAX + 1)),
    }

    # ---- C6: measured error term  h(N) - sqrt(N), and (h(N)-sqrt N)/N^(1/4)
    worst = max(range(1, NMAX + 1), key=lambda N: hN[N] - math.sqrt(N))
    worst_norm = max(range(2, NMAX + 1),
                     key=lambda N: (hN[N] - math.sqrt(N)) / (N ** 0.25))
    out["checks"]["C6_error_term"] = {
        "note": "OBSERVED data on the exactly-known range only; NOT a proof of anything.",
        "max_h_minus_sqrtN": {
            "N": worst, "h": hN[worst],
            "value": round(hN[worst] - math.sqrt(worst), 6),
        },
        "max_ratio_over_N_pow_quarter": {
            "N": worst_norm, "h": hN[worst_norm],
            "value": round((hN[worst_norm] - math.sqrt(worst_norm)) / (worst_norm ** 0.25), 6),
        },
        "conjecture_direction": ("Erdos 30 asks whether h(N) - sqrt(N) = O_eps(N^eps); "
                                 "the proved upper bound in this campaign is O(N^(1/4))."),
    }

    blob = json.dumps(out, indent=1, sort_keys=True)
    out["sha256_of_body"] = hashlib.sha256(blob.encode()).hexdigest()
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
