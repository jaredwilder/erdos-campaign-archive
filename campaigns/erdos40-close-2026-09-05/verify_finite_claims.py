"""
Erdos 40 campaign -- independent brute-force verification of the finite claims the banked
Lean proofs rest on.  This script shares NO code with the Lean development; it enumerates
directly from the definitions.

It does NOT test Erdos 40 itself.  Per erdosproblems.com/40 the problem "cannot be resolved
with a finite computation".  What is tested here:

  C1  rep_P2_le_two          r_{P2}(n) <= 2 for every n in the tested range
  C2  P2_isSidon             the powers of two are a Sidon set (brute force over the range)
  C3  cnt_P2_ge              |P2 cap [1,N]| >= floor(log2 N) + 1
  C4  log_isBigO_cnt_P2      log N <= log(2) * |P2 cap [1,N]|   (the =O constant is log 2)
  C5  ceiling instantiation  sqrt(N) / (sqrt(N)/log N) == log N
  C6  basis_count            N - M <= (|A cap [1,N]| + 1)^2 for additive bases of order 2
  C7  sqrt_le_three_mul_cnt  sqrt(N) <= 3 |A cap [1,N]| for N >= 2M+4, same bases
  C8  rep_le_two_of_max_unique  the criterion agrees with a direct count on random sets

Usage:  python verify_finite_claims.py [--nmax 100000]
"""

import argparse
import json
import math
import random
import time


def rep(A_set, n):
    """Number of ORDERED pairs (a, b) in A x A with a + b = n."""
    return sum(1 for a in range(n + 1) if a in A_set and (n - a) in A_set)


def cnt(A_set, N):
    """|A cap [1, N]|."""
    return sum(1 for a in range(1, N + 1) if a in A_set)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=100000)
    args = ap.parse_args()
    NMAX = args.nmax
    t0 = time.time()

    results = {}
    violations = []
    cases = 0

    # ---- the witness set -------------------------------------------------
    P2 = set()
    k = 0
    while 2 ** k <= NMAX:
        P2.add(2 ** k)
        k += 1
    P2_max_exp = k - 1

    # ---- C1: r_{P2}(n) <= 2 ---------------------------------------------
    dist = {0: 0, 1: 0, 2: 0}
    worst = 0
    for n in range(0, NMAX + 1):
        r = sum(1 for a in P2 if a <= n and (n - a) in P2)
        worst = max(worst, r)
        dist[r] = dist.get(r, 0) + 1
        if r > 2:
            violations.append(f"C1 rep_P2({n}) = {r}")
        cases += 1
    results["C1_rep_P2_le_two"] = {
        "range": [0, NMAX],
        "max_observed_rep": worst,
        "distribution": {str(a): b for a, b in sorted(dist.items())},
        "pass": worst <= 2,
    }

    # ---- C2: P2 is a Sidon set (brute force over exponents) -------------
    sums = {}
    sidon_ok = True
    for i in range(P2_max_exp + 1):
        for j in range(i, P2_max_exp + 1):
            s = 2 ** i + 2 ** j
            if s in sums and sums[s] != (i, j):
                sidon_ok = False
                violations.append(f"C2 sidon collision at {s}: {sums[s]} and {(i, j)}")
            sums[s] = (i, j)
            cases += 1
    results["C2_P2_isSidon"] = {
        "unordered_pairs_tested": len(sums),
        "collisions": 0 if sidon_ok else len([v for v in violations if v.startswith("C2")]),
        "pass": sidon_ok,
    }

    # ---- C3 / C4: counting and the =O constant --------------------------
    log2 = math.log(2.0)
    c3_ok = c4_ok = True
    c4_worst_ratio = 0.0
    check_Ns = sorted(set(
        list(range(1, 2000))
        + [random.randint(1, NMAX) for _ in range(3000)]
        + [2 ** e for e in range(0, P2_max_exp + 1)]
        + [2 ** e - 1 for e in range(1, P2_max_exp + 1)]
        + [2 ** e + 1 for e in range(0, P2_max_exp)]
    ))
    check_Ns = [n for n in check_Ns if 1 <= n <= NMAX]
    for N in check_Ns:
        c = cnt(P2, N) if N < 4000 else sum(1 for a in P2 if 1 <= a <= N)
        lo = N.bit_length() - 1  # floor(log2 N)
        if not (lo + 1 <= c):
            c3_ok = False
            violations.append(f"C3 N={N}: floor(log2)+1={lo+1} > cnt={c}")
        lhs = math.log(N)
        rhs = log2 * c
        if lhs > rhs + 1e-12:
            c4_ok = False
            violations.append(f"C4 N={N}: log N={lhs} > log2*cnt={rhs}")
        if rhs > 0:
            c4_worst_ratio = max(c4_worst_ratio, lhs / rhs)
        cases += 1
    results["C3_cnt_P2_ge"] = {"N_values_tested": len(check_Ns), "pass": c3_ok}
    results["C4_log_isBigO_cnt_P2"] = {
        "N_values_tested": len(check_Ns),
        "constant_used": "log 2",
        "worst_ratio_logN_over_constant_times_cnt": c4_worst_ratio,
        "pass": c4_ok,
    }

    # ---- C5: the ceiling instantiation ----------------------------------
    c5_ok = True
    c5_worst = 0.0
    for N in check_Ns:
        if N < 2:
            continue
        g = math.sqrt(N) / math.log(N)
        thr = math.sqrt(N) / g
        c5_worst = max(c5_worst, abs(thr - math.log(N)))
        if abs(thr - math.log(N)) > 1e-9:
            c5_ok = False
            violations.append(f"C5 N={N}: threshold {thr} != log N {math.log(N)}")
        cases += 1
    results["C5_threshold_is_log"] = {
        "max_abs_error": c5_worst,
        "pass": c5_ok,
    }

    # ---- C6 / C7: the basis counting bound ------------------------------
    BN = 4000
    bases = {
        "all_naturals": set(range(0, BN + 1)),
        "evens_plus_one": set(range(0, BN + 1, 2)) | {1},
        "shifted_squares": None,   # filled below
        "greedy_basis": None,
        "random_dense_p05": None,
    }
    # a basis built from {0,1,...,k} u k*Z, which covers all large n
    kk = 40
    bases["shifted_squares"] = set(range(0, kk + 1)) | set(range(0, BN + 1, kk))
    # greedy: keep adding least element that covers the smallest uncovered n
    gb = {0, 1}
    covered = {0, 1, 2}
    n = 3
    while n <= BN:
        if n in covered:
            n += 1
            continue
        gb.add(n)
        for a in list(gb):
            covered.add(a + n)
        covered.add(2 * n)
        n += 1
    bases["greedy_basis"] = gb
    rnd = set(random.sample(range(0, BN + 1), int(0.05 * BN)))
    rnd |= {0, 1}
    bases["random_dense_p05"] = rnd

    c6_ok = c7_ok = True
    basis_report = {}
    for name, A in bases.items():
        AA = set()
        Al = sorted(A)
        for a in Al:
            for b in Al:
                s = a + b
                if s <= BN:
                    AA.add(s)
        missing = [n for n in range(0, BN + 1) if n not in AA]
        # M = the largest omitted value inside the tested window
        M = max(missing) if missing else 0
        # the window in which "N - M <= (cnt+1)^2" is a meaningful claim
        bad6 = bad7 = 0
        for N in range(M + 1, BN + 1):
            c = sum(1 for a in A if 1 <= a <= N)
            if N - M > (c + 1) * (c + 1):
                bad6 += 1
                c6_ok = False
                violations.append(f"C6 {name} N={N}: {N-M} > {(c+1)**2}")
            if N >= 2 * M + 4:
                if math.sqrt(N) > 3 * c + 1e-12:
                    bad7 += 1
                    c7_ok = False
                    violations.append(f"C7 {name} N={N}: sqrt={math.sqrt(N)} > 3c={3*c}")
            cases += 1
        basis_report[name] = {
            "M_largest_omitted_in_window": M,
            "window": [M + 1, BN],
            "C6_violations": bad6,
            "C7_violations": bad7,
        }
    results["C6_basis_count"] = {"bases": basis_report, "pass": c6_ok}
    results["C7_sqrt_le_three_cnt"] = {"pass": c7_ok}

    # ---- C8: max-unique criterion vs a direct count ---------------------
    c8_ok = True
    trials = 0
    for _ in range(200):
        size = random.randint(2, 14)
        A = set(random.sample(range(0, 300), size))
        for n in range(0, 320):
            # direct count
            r = sum(1 for a in A if a <= n and (n - a) in A)
            # criterion: is the larger element of every representation unique?
            bigs = set()
            for a in A:
                b = n - a
                if b in A and a <= b:
                    bigs.add(b)
            crit = len(bigs) <= 1
            if crit and r > 2:
                c8_ok = False
                violations.append(f"C8 criterion held but rep={r} at n={n}")
            trials += 1
            cases += 1
    results["C8_max_unique_criterion"] = {"trials": trials, "pass": c8_ok}

    wall = time.time() - t0
    receipt = {
        "campaign": "erdos40-close-2026-09-05",
        "target": "erdos:40",
        "target_source": "https://www.erdosproblems.com/40",
        "script": "verify_finite_claims.py",
        "nmax": NMAX,
        "cases_tested": cases,
        "violations": len(violations),
        "violations_sample": violations[:20],
        "verdict": "ALL PASS" if not violations else "VIOLATIONS FOUND",
        "wall_seconds": round(wall, 2),
        "checks": results,
        "transfer_caveat": (
            "Per the source page, Erdos 40 cannot be resolved by a finite computation. "
            "This run tests only the finite lemmas the banked Lean rests on; it is not "
            "evidence about the problem itself."
        ),
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
