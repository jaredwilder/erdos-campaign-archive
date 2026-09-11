#!/usr/bin/env python3
"""
Erdos Problem 28 (Erdos-Turan conjecture on additive bases) -- independent finite
verification of every finite claim the banked Lean rests on.

$0, deterministic, no network, no model in the loop.  Python stdlib only.

This script is the CROSSCHECK arm for the Lean development in ./lean:

  ARM 1  rep-as-cardinality  vs  rep-as-convolution     (two independent code paths)
  ARM 2  the parity fact: r_A(n) is EVEN at every ODD n, exhaustively over small A
  ARM 3  the parity floor: covering + odd  =>  r_A(n) >= 2, exhaustively
  ARM 4  the counting sandwich  cnt^2 >= N - M  and  cnt^2 <= B*(2N+1)
  ARM 5  the KILL: parityWitness is parity-admissible and bounded by 2
  ARM 6  a WINDOW SEARCH: the minimum achievable max_n r_A(n) over window-covering
         sets A subset [0,N].  EXHAUSTIVE over the declared window only.

  ARM 6 IS FINITE DATA AND IS NOT EXTRAPOLATED.  A window-covering set is not an
  additive basis of order 2, and the minimum over a window is an UPPER bound on
  nothing infinite.  It is recorded as a boundary-audit instance, never as a trend.

Usage:  python verify_finite_claims.py [--out receipts/receipt-finite-claims.json]
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
import sys
import time
from pathlib import Path

# --------------------------------------------------------------------------------------
# The two independent evaluators for r_A(n)
# --------------------------------------------------------------------------------------


def rep_card(A: frozenset[int], n: int) -> int:
    """r_A(n) as the CARDINALITY of the filtered antidiagonal -- the Lean `rep`."""
    return sum(1 for a in range(n + 1) if a in A and (n - a) in A)


def rep_conv(A: frozenset[int], n: int, cap: int) -> int:
    """r_A(n) as the CONVOLUTION (1_A * 1_A)(n) built from an indicator LIST.

    Deliberately a different code path: it materialises the indicator vector and does a
    dot product, rather than testing membership in a set.
    """
    ind = [1 if i in A else 0 for i in range(cap + 1)]
    return sum(
        ind[a] * ind[n - a] for a in range(n + 1) if a <= cap and 0 <= n - a <= cap
    )


def cnt(A: frozenset[int], N: int) -> int:
    """|A cap [0, N]| -- the Lean `cnt`."""
    return sum(1 for a in A if a <= N)


# --------------------------------------------------------------------------------------
# Arms
# --------------------------------------------------------------------------------------


def arm1_rep_agreement(cap: int = 12) -> dict:
    """rep_card == rep_conv on every subset of [0,cap] and every n in [0,2*cap]."""
    checks = 0
    for bits in range(1 << (cap + 1)):
        A = frozenset(i for i in range(cap + 1) if (bits >> i) & 1)
        for n in range(2 * cap + 1):
            if rep_card(A, n) != rep_conv(A, n, cap):
                return {
                    "arm": "rep_card == rep_conv",
                    "status": "FAIL",
                    "counterexample": {"A": sorted(A), "n": n},
                }
            checks += 1
    return {
        "arm": "rep_card == rep_conv",
        "status": "PASS",
        "domain": f"every A subset [0,{cap}], every n in [0,{2 * cap}]",
        "subsets": 1 << (cap + 1),
        "checks": checks,
        "independence_class": "DIFFERENT_KIND (set membership vs materialised indicator dot product)",
    }


def arm2_parity(cap: int = 12) -> dict:
    """r_A(n) is EVEN whenever n is ODD -- the swap involution has no fixed point there."""
    checks = 0
    for bits in range(1 << (cap + 1)):
        A = frozenset(i for i in range(cap + 1) if (bits >> i) & 1)
        for n in range(1, 2 * cap + 1, 2):
            r = rep_card(A, n)
            if r % 2 != 0:
                return {
                    "arm": "odd n => r_A(n) even",
                    "status": "FAIL",
                    "counterexample": {"A": sorted(A), "n": n, "r": r},
                }
            checks += 1
    return {
        "arm": "odd n => r_A(n) even",
        "status": "PASS",
        "domain": f"every A subset [0,{cap}], every odd n in [1,{2 * cap}]",
        "checks": checks,
    }


def arm3_parity_floor(cap: int = 12) -> dict:
    """r_A(n) >= 1 and n odd  =>  r_A(n) >= 2.  Exhaustive."""
    checks = 0
    witnesses = 0
    for bits in range(1 << (cap + 1)):
        A = frozenset(i for i in range(cap + 1) if (bits >> i) & 1)
        for n in range(1, 2 * cap + 1, 2):
            r = rep_card(A, n)
            if r >= 1:
                witnesses += 1
                if r < 2:
                    return {
                        "arm": "odd n and r_A(n) >= 1 => r_A(n) >= 2",
                        "status": "FAIL",
                        "counterexample": {"A": sorted(A), "n": n, "r": r},
                    }
            checks += 1
    return {
        "arm": "odd n and r_A(n) >= 1 => r_A(n) >= 2",
        "status": "PASS",
        "domain": f"every A subset [0,{cap}], every odd n in [1,{2 * cap}]",
        "checks": checks,
        "nonvacuous_instances": witnesses,
    }


def arm4_sandwich(cap: int = 12) -> dict:
    """For every A subset [0,cap] and every N <= cap:

        (lower)  |{n in [1,N] : r_A(n) >= 1}|  <=  cnt(A,N)^2
        (upper)  cnt(A,N)^2  <=  B * (2N + 1),  B = max_{m <= 2N} r_A(m)

    The lower arm is `basis_count` restricted to the window (M = 0 on the covered part);
    the upper arm is `cnt_sq_le_of_rep_le` with the window's own realised bound.
    """
    checks = 0
    for bits in range(1 << (cap + 1)):
        A = frozenset(i for i in range(cap + 1) if (bits >> i) & 1)
        for N in range(1, cap + 1):
            covered = sum(1 for n in range(1, N + 1) if rep_card(A, n) >= 1)
            c = cnt(A, N)
            B = max((rep_card(A, m) for m in range(0, 2 * N + 1)), default=0)
            if covered > c * c:
                return {
                    "arm": "counting sandwich",
                    "status": "FAIL",
                    "side": "lower",
                    "counterexample": {"A": sorted(A), "N": N},
                }
            if c * c > B * (2 * N + 1):
                return {
                    "arm": "counting sandwich",
                    "status": "FAIL",
                    "side": "upper",
                    "counterexample": {"A": sorted(A), "N": N, "B": B},
                }
            checks += 2
    return {
        "arm": "counting sandwich",
        "status": "PASS",
        "domain": f"every A subset [0,{cap}], every N in [1,{cap}]",
        "checks": checks,
    }


def arm5_kill() -> dict:
    """parityWitness n = 2 if n odd else 1 is parity-admissible, second-moment-admissible,
    and bounded by 2."""
    def w(n: int) -> int:
        return 2 if n % 2 == 1 else 1

    running = 0
    for n in range(0, 10001):
        if w(n) < 1:
            return {"arm": "parity kill", "status": "FAIL", "reason": "not positive", "n": n}
        if n % 2 == 1 and w(n) % 2 != 0:
            return {"arm": "parity kill", "status": "FAIL", "reason": "not even at odd", "n": n}
        if w(n) > 2:
            return {"arm": "parity kill", "status": "FAIL", "reason": "exceeds 2", "n": n}
        if running > 4 * n:
            return {
                "arm": "parity kill",
                "status": "FAIL",
                "reason": "second moment exceeds 4N",
                "n": n,
                "running": running,
            }
        running += w(n) ** 2
    return {
        "arm": "parity kill",
        "status": "PASS",
        "statement": (
            "the function n |-> (2 if n odd else 1) satisfies every constraint the parity "
            "route places on r_A (positive everywhere, even at every odd n), AND every "
            "linear second-moment bound (sum_{n<N} f(n)^2 <= 4N), while never exceeding 2; "
            "hence neither the parity route nor any moment estimate of that shape can prove "
            "limsup r_A >= 3"
        ),
        "domain": "n in [0, 10000] (the Lean theorems are universal)",
        "lean_theorems": [
            "Erdos28.parity_saturates_at_two",
            "Erdos28.parity_and_moment_saturate_at_two",
        ],
        "why_the_moment_axis": (
            "Ruzsa, A just basis, Monatsh. Math. 109 (1990) 145-151: there IS an additive "
            "basis of order 2 with sum_{n<=N} r_A(n)^2 = O(N). CITED, not formalised here."
        ),
    }


def arm6_window_search(nmax: int = 16) -> dict:
    """EXHAUSTIVE: min over window-covering A subset [0,N] of max_{1<=n<=N} r_A(n).

    A is 'window-covering at N' iff every n in [1,N] has r_A(n) >= 1.
    """
    table = []
    for N in range(2, nmax + 1):
        best = None
        best_A = None
        for bits in range(1 << (N + 1)):
            A = frozenset(i for i in range(N + 1) if (bits >> i) & 1)
            mx = 0
            ok = True
            for n in range(1, N + 1):
                r = rep_card(A, n)
                if r == 0:
                    ok = False
                    break
                if r > mx:
                    mx = r
                if best is not None and mx >= best:
                    ok = False
                    break
            if ok and (best is None or mx < best):
                best = mx
                best_A = sorted(A)
        table.append({"N": N, "min_max_rep": best, "witness_A": best_A})
    return {
        "arm": "window search",
        "status": "COMPLETE",
        "interpretation": "CANDIDATE_DATA",
        "globality": "CERTIFIED over the declared window (exhaustive over all 2^(N+1) subsets)",
        "search_space": f"every A subset [0,N], N in [2,{nmax}]",
        "restricted_to": "window-covering sets, not additive bases of order 2",
        "space_relation": "the window condition is NEITHER a subset nor a superset of the basis condition",
        "transport_to": "NONE",
        "quotients": "none needed: the quantity is an exact minimum over an exhaustively enumerated finite family",
        "extrapolation": "REFUSED -- a minimum over a finite window bounds nothing about the infinite problem",
        "table": table,
    }


# --------------------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    ap.add_argument("--cap", type=int, default=12)
    ap.add_argument("--nmax", type=int, default=16)
    args = ap.parse_args()

    t0 = time.time()
    arms = [
        arm1_rep_agreement(args.cap),
        arm2_parity(args.cap),
        arm3_parity_floor(args.cap),
        arm4_sandwich(args.cap),
        arm5_kill(),
        arm6_window_search(args.nmax),
    ]
    elapsed = time.time() - t0

    failed = [a for a in arms if a["status"] not in ("PASS", "COMPLETE")]
    src = Path(__file__).read_bytes()
    receipt = {
        "campaign": "erdos28-close-2026-09-05",
        "target": "erdos:28",
        "target_source": "https://www.erdosproblems.com/28",
        "instrument": {
            "kind": "EVALUATOR",
            "file": "verify_finite_claims.py",
            "sha256": hashlib.sha256(src).hexdigest(),
            "python": platform.python_version(),
            "platform": platform.platform(),
            "error_model": "EXACT (integer arithmetic only)",
            "preconditions": "none; every quantity is a finite cardinality over an enumerated family",
        },
        "wall_seconds": round(elapsed, 2),
        "verdict": "ALL_PASS" if not failed else "FAIL",
        "arms": arms,
        "claim_ceiling": (
            "These are EXHAUSTIVE checks over explicitly declared FINITE windows. They "
            "confirm the finite content of the banked Lean and refute nothing about the "
            "infinite problem. Erdos 28 remains UNRESOLVED."
        ),
    }

    out = json.dumps(receipt, indent=2)
    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(out, encoding="utf-8")
    print(out)
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
