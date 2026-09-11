#!/usr/bin/env python3
"""cover_cube.py — cube-and-conquer for the C(13,6,3) close (companion to cover_sat.py).

THE CLOSE: La Jolla holds 20 <= C(13,6,3) <= 21.
  ALL cubes UNSAT (each drat-trim verified) + exhaustive split  =>  C(13,6,3) = 21.
  ANY cube SAT (decoded cover verify_cover'd from the definition)  =>  record C = 20.

SPLIT LAW: branch on ALL 2^K assignments of K fixed block variables — exhaustive BY
CONSTRUCTION; the aggregator still re-asserts the count and refuses a partial sweep.
Branch vars are the first K block indices after the WLOG block (deterministic).

VERDICT LAW (identical to the monolith lane): a cube's UNSAT counts only after
drat-trim verifies its proof (sha recorded, proof then deleted to protect disk);
a SAT decodes and re-verifies FROM THE DEFINITION; exit 137/143 = STOPPED_NO_VERDICT.

SELFCHECK (must be ALL GREEN before any box cycle): C(4,3,2) at b=2, K=2 -> 4 cubes all
UNSAT under the built-in DPLL (matches the known value 3 > 2); at b=3, K=2 -> some cube
SAT and its decoded cover verifies. Both directions of the cube semantics exercised.

Usage:
  python3 cover_cube.py --selfcheck
  python3 cover_cube.py --emit --K 8 --outdir cubes20            # flagship, 256 cubes
  python3 cover_cube.py --aggregate --outdir cubes20             # verdict, fail-closed
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover_sat  # the sealed encoder: encode(), dpll(), verify_cover(), blocks_of


def branch_vars(blocks, K: int) -> list[int]:
    """First K block DIMACS vars after the WLOG block {1..k}."""
    first = tuple(range(1, 6 + 1))
    wlog_idx = blocks.index(first) + 1
    out = []
    v = 1
    while len(out) < K:
        if v != wlog_idx:
            out.append(v)
        v += 1
    return out


def emit(v: int, k: int, t: int, b: int, K: int, outdir: str) -> dict:
    cnf, blocks = cover_sat.encode(v, k, t, b, wlog=True)
    base = cnf.dimacs()
    base_sha = hashlib.sha256(base.encode()).hexdigest()
    os.makedirs(outdir, exist_ok=True)
    bvars = branch_vars(blocks, K)
    n_cubes = 0
    for bits in itertools.product([1, -1], repeat=K):
        assum = [s * var for s, var in zip(bits, bvars)]
        cid = f"c{n_cubes:05d}"
        text = (f"p cnf {cnf.nvars} {len(cnf.clauses) + K}\n"
                + "".join(f"{a} 0\n" for a in assum)
                + base.split("\n", 1)[1])
        with open(os.path.join(outdir, f"{cid}.cnf"), "w") as f:
            f.write(text)
        with open(os.path.join(outdir, f"{cid}.cube"), "w") as f:
            f.write(" ".join(map(str, assum)) + " 0\n")
        n_cubes += 1
    manifest = {
        "question": f"exists <= {b}-block C({v},{k},{t}) cover",
        "base_cnf_sha256": base_sha, "vars": cnf.nvars, "base_clauses": len(cnf.clauses),
        "K": K, "branch_vars": bvars, "n_cubes": n_cubes,
        "exhaustive_by_construction": True,
        "verdict_law": ("ALL cubes UNSAT+drat-trim-verified => C=21; "
                        "ANY SAT decoded+verify_cover => C=20; partial sweep => NO VERDICT"),
    }
    with open(os.path.join(outdir, "manifest.json"), "w") as f:
        json.dump(manifest, f, indent=2)
    return manifest


def aggregate(outdir: str) -> dict:
    with open(os.path.join(outdir, "manifest.json")) as f:
        man = json.load(f)
    n = man["n_cubes"]
    counts = {"UNSAT_VERIFIED": 0, "UNSAT_UNVERIFIED": 0, "SAT": 0,
              "STOPPED_NO_VERDICT": 0, "MISSING": 0}
    sat_cubes, unverified = [], []
    for i in range(n):
        cid = f"c{i:05d}"
        ck = os.path.join(outdir, f"{cid}.json")
        if not os.path.exists(ck):
            counts["MISSING"] += 1
            continue
        row = json.load(open(ck))
        res = row.get("result")
        if res == "UNSAT" and row.get("drat_verified") is True:
            counts["UNSAT_VERIFIED"] += 1
        elif res == "UNSAT":
            counts["UNSAT_UNVERIFIED"] += 1
            unverified.append(cid)
        elif res == "SAT":
            counts["SAT"] += 1
            sat_cubes.append(cid)
        else:
            counts["STOPPED_NO_VERDICT"] += 1
    verdict = "NO_VERDICT_YET"
    if counts["SAT"] > 0:
        verdict = "SAT_CANDIDATE(decode+verify_cover required before any claim)"
    elif counts["UNSAT_VERIFIED"] == n:
        verdict = "ALL_CUBES_UNSAT_VERIFIED_EXHAUSTIVE => C(13,6,3) = 21"
    out = {"n_cubes": n, "counts": counts, "sat_cubes": sat_cubes,
           "unverified_unsat": unverified, "VERDICT": verdict}
    with open(os.path.join(outdir, "AGGREGATE.json"), "w") as f:
        json.dump(out, f, indent=2)
    return out


def selfcheck() -> int:
    import tempfile
    ok_all = True

    def arm(name, ok, detail):
        nonlocal ok_all
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}: {detail}")
        ok_all = ok_all and ok

    # C(4,3,2): b=2 UNSAT everywhere; b=3 SAT somewhere.  K=2 over the first two
    # non-WLOG blocks of the v=4 instance (WLOG block is {1,2,3}).
    for b, wantsat in ((2, False), (3, True)):
        cnf, blocks = cover_sat.encode(4, 3, 2, b, wlog=True)
        first = tuple(range(1, 4))
        wlog_idx = blocks.index(first) + 1
        bvars = [v for v in range(1, len(blocks) + 1) if v != wlog_idx][:2]
        results = []
        for bits in itertools.product([1, -1], repeat=2):
            cl = list(cnf.clauses) + [(s * v,) for s, v in zip(bits, bvars)]
            m = cover_sat.dpll(cl, cnf.nvars)
            if m is not None:
                cover = cover_sat.decode_model({l for l in m if l > 0}, blocks)
                okv, _ = cover_sat.verify_cover(4, 3, 2, cover)
                results.append("SAT_VERIFIED" if okv else "SAT_BROKEN")
            else:
                results.append("UNSAT")
        anysat = any(r.startswith("SAT") for r in results)
        allver = all(r != "SAT_BROKEN" for r in results)
        arm(f"C(4,3,2) b={b} cubes K=2", anysat == wantsat and allver,
            f"results={results} (want {'some SAT' if wantsat else 'all UNSAT'})")

    # exhaustiveness + determinism of the flagship emission (no solving)
    with tempfile.TemporaryDirectory() as td:
        man = emit(13, 6, 3, 20, 4, td)
        files = [f for f in os.listdir(td) if f.endswith(".cnf")]
        arm("flagship K=4 emission", man["n_cubes"] == 16 and len(files) == 16,
            f"{man['n_cubes']} cubes, base sha {man['base_cnf_sha256'][:16]}…")
        agg = aggregate(td)
        arm("aggregator fail-closed on empty sweep",
            agg["VERDICT"] == "NO_VERDICT_YET" and agg["counts"]["MISSING"] == 16,
            agg["VERDICT"])

    print("SELFCHECK " + ("ALL GREEN" if ok_all else "RED — do not ship"))
    return 0 if ok_all else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selfcheck", action="store_true")
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--aggregate", action="store_true")
    ap.add_argument("--K", type=int, default=8)
    ap.add_argument("--outdir", default="cubes20")
    args = ap.parse_args()
    if args.selfcheck:
        return selfcheck()
    if args.emit:
        print(json.dumps(emit(13, 6, 3, 20, args.K, args.outdir), indent=2))
        return 0
    if args.aggregate:
        print(json.dumps(aggregate(args.outdir), indent=2))
        return 0
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
