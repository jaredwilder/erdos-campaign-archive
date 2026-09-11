#!/usr/bin/env python3
"""
Erdos 66 campaign -- independent brute-force verification of the FINITE claims that the
Lean file `Erdos66Core.lean` proves, plus an evidence-only asymptotic consistency probe.

Everything in PART 1 is an exact integer check by a method independent of the Lean proof
(direct enumeration of ordered pairs).  PART 2 is EVIDENCE ONLY -- a numerical probe on a
random model set; it proves nothing and is marked as such in the receipt.

Run:  nice -n 19 python3 verify_finite_identity.py
"""
import json, math, random, hashlib, sys, time, platform

random.seed(660066)

# ---------------------------------------------------------------- PART 1 (exact)

def rep_via_convolution(Aset, N):
    """r_A(n) for n <= N, computed the way `rep` is defined (a ranges over [0,n])."""
    out = [0] * (N + 1)
    for n in range(N + 1):
        c = 0
        for a in range(n + 1):
            if a in Aset and (n - a) in Aset:
                c += 1
        out[n] = c
    return out

def rep_via_pair_enumeration(Alist, N):
    """r_A(n) by enumerating ORDERED pairs -- an independent method."""
    out = [0] * (N + 1)
    for a in Alist:
        if a > N:
            continue
        for b in Alist:
            if a + b <= N:
                out[a + b] += 1
    return out

def cnt(Aset, x):
    return sum(1 for a in Aset if a <= x)

def check_set(Alist, N):
    """Returns dict of violations found (empty dict == all checks passed)."""
    Aset = set(Alist)
    v = {}
    r1 = rep_via_convolution(Aset, N)
    r2 = rep_via_pair_enumeration(Alist, N)
    if r1 != r2:
        v["rep_methods_disagree"] = True

    # sum_rep_eq :  sum_{n<=N} r_A(n)  ==  #{(a,b) in A^2 : a+b <= N}
    S = sum(r1)
    pairs_le = sum(1 for a in Alist if a <= N for b in Alist if a + b <= N)
    if S != pairs_le:
        v["sum_rep_eq"] = (S, pairs_le)

    # counting_sandwich :  cnt(N/2)^2 <= S <= cnt(N)^2      (N//2 = Nat division)
    lo = cnt(Aset, N // 2) ** 2
    hi = cnt(Aset, N) ** 2
    if not (lo <= S <= hi):
        v["counting_sandwich"] = (lo, S, hi)

    # rep_le_of_finite :  r_A(n) <= |A|^2      (and the sharper r_A(n) <= cnt(A,n))
    K = len(Alist)
    for n in range(N + 1):
        if r1[n] > K * K:
            v["rep_le_of_finite"] = n
            break
        if r1[n] > cnt(Aset, n):
            v["rep_le_cnt"] = n
            break

    # PARITY LAW (not in the Lean core; recorded as an exact finite observation only):
    #   r_A(n) is odd  <=>  n = a+a for some a in A
    for n in range(N + 1):
        expect_odd = ((n % 2 == 0) and (n // 2) in Aset)
        if (r1[n] % 2 == 1) != expect_odd:
            v["parity_law"] = n
            break
    return v

def run_part1():
    families, cases, viol = {}, 0, []

    # (a) uniformly random subsets at several densities
    for N in (0, 1, 2, 3, 7, 20, 61, 150, 400, 900):
        for p in (0.0, 0.05, 0.2, 0.5, 0.9, 1.0):
            for _ in range(6):
                A = [a for a in range(N + 1) if random.random() < p]
                v = check_set(A, N)
                cases += 1
                if v:
                    viol.append({"family": "random", "N": N, "p": p, "A": A, "viol": v})
        print(f"[progress] part1 random N={N} done, cases={cases}, viol={len(viol)}",
              file=sys.stderr, flush=True)
    families["random"] = cases

    # (b) structured sets: squares, primes, powers of two, an arithmetic progression,
    #     a greedy Sidon set, the empty set, {0}, and full intervals.
    def sieve(n):
        s = [True] * (n + 1)
        s[0] = s[1] = False
        for i in range(2, int(n ** 0.5) + 1):
            if s[i]:
                for j in range(i * i, n + 1, i):
                    s[j] = False
        return [i for i in range(n + 1) if s[i]]

    def greedy_sidon(n):
        A, sums = [], set()
        for x in range(n + 1):
            new = {x + a for a in A} | {2 * x}
            if not (new & sums):
                A.append(x); sums |= new
        return A

    before = cases
    for N in (0, 1, 5, 33, 120, 500):
        structured = [
            [k * k for k in range(int(N ** 0.5) + 1)],
            sieve(N) if N >= 2 else [],
            [2 ** k for k in range(N.bit_length() + 1) if 2 ** k <= N],
            [a for a in range(0, N + 1, 3)],
            greedy_sidon(min(N, 200)),
            [], [0], [N], list(range(N + 1)),
        ]
        for A in structured:
            A = sorted(set(a for a in A if a <= N))
            v = check_set(A, N)
            cases += 1
            if v:
                viol.append({"family": "structured", "N": N, "A": A, "viol": v})
        print(f"[progress] part1 structured N={N} done, cases={cases}, viol={len(viol)}",
              file=sys.stderr, flush=True)
    families["structured"] = cases - before
    return cases, viol, families

# ---------------------------------------------------------------- PART 2 (evidence only)

def run_part2(XMAX=400_000):
    """
    EVIDENCE ONLY.  Build the classical Erdos random model: put x in A independently with
    probability ~ K*sqrt(log x / x).  Measure
        c_hat(n) = r_A(n)/log n      and      g(N) = A(N)/sqrt(N log N).
    The elementary sandwich proved in Lean forces  sqrt(c) <= liminf g  and
    limsup g <= sqrt(2c);  the Stieltjes/Karamata computation predicts g -> 2*sqrt(c/pi).
    This probe only checks that the measured numbers sit where that predicts.
    """
    K = 1.0
    A = []
    for x in range(2, XMAX):
        p = K * math.sqrt(math.log(x) / x)
        if p >= 1.0 or random.random() < p:
            A.append(x)
    print(f"[progress] part2 model set built, |A|={len(A)}", file=sys.stderr, flush=True)

    # sample r_A(n) on a window near the top (full convolution over all of A is O(|A|^2))
    lo, hi = XMAX - 4000, XMAX - 1
    reps = {}
    for n in range(lo, hi + 1):
        reps[n] = 0
    for i, a in enumerate(A):
        if a > hi:
            break
        if i % 500 == 0:
            print(f"[progress] part2 convolution {i}/{len(A)}", file=sys.stderr, flush=True)
        for b in A:
            s = a + b
            if s > hi:
                break
            if s >= lo:
                reps[s] += 1
    ns = sorted(reps)
    c_hat = sum(reps[n] / math.log(n) for n in ns) / len(ns)
    N = hi
    AN = len(A)
    g = AN / math.sqrt(N * math.log(N))
    return {
        "note": "EVIDENCE ONLY -- a single random model set; proves nothing.",
        "XMAX": XMAX, "|A|": AN, "K": K,
        "window": [lo, hi],
        "c_hat_mean_rep_over_log": c_hat,
        "g_N_eq_A(N)/sqrt(N logN)": g,
        "elementary_lower_bound_sqrt_c": math.sqrt(c_hat),
        "karamata_prediction_2sqrt(c/pi)": 2 * math.sqrt(c_hat / math.pi),
        "elementary_upper_bound_sqrt_2c": math.sqrt(2 * c_hat),
        "g_inside_elementary_bracket": bool(
            math.sqrt(c_hat) * 0.97 <= g <= math.sqrt(2 * c_hat) * 1.03),
        "g_close_to_karamata": bool(
            abs(g - 2 * math.sqrt(c_hat / math.pi)) <= 0.08 * 2 * math.sqrt(c_hat / math.pi)),
    }

# ---------------------------------------------------------------- main

if __name__ == "__main__":
    t0 = time.time()
    cases, viol, families = run_part1()
    part2 = run_part2()
    src = open(__file__, "rb").read()
    out = {
        "tool": "verify_finite_identity.py",
        "sha256_of_this_script": hashlib.sha256(src).hexdigest(),
        "python": sys.version.split()[0],
        "host": platform.node(),
        "seed": 660066,
        "part1_exact": {
            "claim": "brute-force verification of rep-method agreement, sum_rep_eq, "
                     "counting_sandwich, rep_le_of_finite, rep_le_cnt, and the parity law",
            "cases_tested": cases,
            "by_family": families,
            "violations": viol,
            "violation_count": len(viol),
            "verdict": "ALL PASS" if not viol else "VIOLATIONS FOUND",
        },
        "part2_evidence_only": part2,
        "wall_seconds": round(time.time() - t0, 2),
    }
    print(json.dumps(out, indent=2))
