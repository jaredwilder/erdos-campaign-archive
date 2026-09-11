#!/usr/bin/env python3
"""cover_sat.py — CNF emitter for covering-design existence  C(v,k,t) with <= b blocks.

THE FLAGSHIP QUESTION (close-day 2026-09-05):  does a 20-block 6-uniform cover of all
286 triples on 13 points exist?  La Jolla records 20 <= C(13,6,3) <= 21, so EITHER
verdict is an exact close of an open repository gap:

    UNSAT (drat-trim verified)  ->  C(13,6,3) = 21 exactly
    SAT   (decoded + re-verified from the definition)  ->  a record 20-cover, C(13,6,3) = 20

The kernel frame is already sealed on the =20 case (Cover20Degree.verify.json: every pair
in >= 3 blocks, every point in >= 8 blocks, degree excess exactly 16).  This file is the
missing piece named by the 2026-09-05 scout pass: "the gap between the kernel lemma and a
box job is a CNF emitter that does not exist yet."

ENCODING (v1 — lean on purpose; validity first, speed devices second):
  vars   x_B for every k-subset B of {1..v}          (v=13,k=6 -> 1716 block vars)
  cover  for every t-subset T: OR{ x_B : T subset B }  (286 clauses of width C(v-k... ) = 120)
  card   Sinz sequential counter, AT MOST b            (adding blocks never uncovers, so
                                                        "<= b" is the right question: a
                                                        smaller cover implies a b-cover)
  wlog   unit clause x_{1..k} = TRUE.  SOUND: covers are closed under point relabeling,
         and any cover has some block; relabel that block onto {1..k}.  So an <=b cover
         exists  iff  an <=b cover containing {1..k} exists.  Disable with --no-wlog.

  NOT in v1: the kernel-frame pair/point cardinality floors as redundant clauses.  They
  are sound to add for THIS question (any <=20 cover completes to a =20 cover by adding
  unused blocks, and the kernel theorems then bind), but they cost 91 more totalizers;
  add as --frame in v2 only if the bare instance stalls the box.

VERDICT LAW (matches the 273 lane):
  - a cadical "UNSATISFIABLE" line counts ONLY after drat-trim verifies the DRAT proof;
    the receipt carries the sha256 of both the CNF and the proof file.
  - a SAT model is decoded to blocks and re-verified FROM THE DEFINITION by
    verify_cover(), which shares no code with the encoder's clause emission.
  - exit 137/143 is STOPPED_NO_VERDICT, never a timeout verdict.

SELFCHECK (must print ALL GREEN before a single box cycle is spent):
  arm 1  C(4,3,2): brute force says SAT@b=3 / UNSAT@b=2; the built-in DPLL on the
         emitted CNF must AGREE on both, and the decoded model must verify_cover().
  arm 2  C(7,3,2) negative: b=6 is UNSAT by counting (6 triples cover <= 18 < 21 pairs);
         DPLL on the emitted CNF must agree.
  arm 3  C(7,3,2) positive: the Fano plane's 7 lines are a perfect cover; the assignment
         (those 7 blocks true, counter chained accordingly) must satisfy EVERY clause.
  arm 4  wlog soundness probe: C(4,3,2)@b=3 stays SAT with wlog on.
  arm 5  flagship determinism: the v=13,k=6,t=3,b=20 CNF is emitted twice; byte-identical
         sha both times; stats printed (vars/clauses/bytes).
A skipped arm prints SKIPPED and fails the run.  A skip is a skip, never a pass.

Usage:
  python3 cover_sat.py --selfcheck
  python3 cover_sat.py --emit --v 13 --k 6 --t 3 --b 20 --out cnf/c13-6-3-b20.cnf
  python3 cover_sat.py --decode --v 13 --k 6 --t 3 --b 20 --cnf <f.cnf> --model <cadical.out>
  python3 cover_sat.py --check-cover --v 13 --k 6 --t 3 --blocks <blocks.json>
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import sys

# ---------------------------------------------------------------- combinatorial core


def blocks_of(v: int, k: int) -> list[tuple[int, ...]]:
    """All k-subsets of {1..v}, deterministic order (this order IS the var numbering)."""
    return list(itertools.combinations(range(1, v + 1), k))


def tsets_of(v: int, t: int) -> list[tuple[int, ...]]:
    return list(itertools.combinations(range(1, v + 1), t))


def verify_cover(v: int, k: int, t: int, cover: list[tuple[int, ...]]) -> tuple[bool, str]:
    """FROM THE DEFINITION.  Shares nothing with the encoder: no var numbering, no CNF."""
    for B in cover:
        if len(B) != k or len(set(B)) != k or not all(1 <= p <= v for p in B):
            return False, f"bad block {B}"
    covered = set()
    for B in cover:
        covered.update(itertools.combinations(sorted(B), t))
    missing = [T for T in itertools.combinations(range(1, v + 1), t) if T not in covered]
    if missing:
        return False, f"{len(missing)} uncovered {t}-sets, first {missing[0]}"
    return True, f"all {len(list(itertools.combinations(range(1, v+1), t)))} {t}-sets covered by {len(cover)} blocks"


# ---------------------------------------------------------------- CNF construction


class CNF:
    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: list[tuple[int, ...]] = []

    def new_var(self) -> int:
        self.nvars += 1
        return self.nvars

    def add(self, *lits: int) -> None:
        self.clauses.append(tuple(lits))

    def dimacs(self) -> str:
        out = [f"p cnf {self.nvars} {len(self.clauses)}"]
        out.extend(" ".join(map(str, c)) + " 0" for c in self.clauses)
        return "\n".join(out) + "\n"


def encode(v: int, k: int, t: int, b: int, wlog: bool = True) -> tuple[CNF, list[tuple[int, ...]]]:
    """Coverage + Sinz at-most-b (+ optional WLOG unit).  Returns (cnf, block list);
    block i (0-based) is DIMACS var i+1.  Auxiliary counter vars come after."""
    blocks = blocks_of(v, k)
    n = len(blocks)
    cnf = CNF()
    cnf.nvars = n  # x_1..x_n are the block vars

    # coverage: every t-set hit
    hit: dict[tuple[int, ...], list[int]] = {T: [] for T in tsets_of(v, t)}
    for i, B in enumerate(blocks):
        for T in itertools.combinations(B, t):
            hit[T].append(i + 1)
    for T, lits in hit.items():
        if not lits:
            raise SystemExit(f"UNSATISFIABLE BY CONSTRUCTION: {t}-set {T} in no block (k<t?)")
        cnf.add(*lits)

    # Sinz sequential at-most-b over x_1..x_n
    # s[i][j] true  =>  at least j of x_1..x_i are true   (i in 1..n, j in 1..b)
    s = [[0] * (b + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for j in range(1, b + 1):
            s[i][j] = cnf.new_var()
    for i in range(1, n + 1):
        cnf.add(-i, s[i][1])                       # x_i -> s_i,1
        if i > 1:
            for j in range(1, b + 1):
                cnf.add(-s[i - 1][j], s[i][j])     # counts propagate
            for j in range(2, b + 1):
                cnf.add(-i, -s[i - 1][j - 1], s[i][j])
            cnf.add(-i, -s[i - 1][b])              # overflow ban: never a (b+1)-th true
    # (no lower bound on purpose: fewer blocks is a strictly stronger cover)

    if wlog:
        first = tuple(range(1, k + 1))
        cnf.add(blocks.index(first) + 1)           # x_{1..k} = TRUE, soundness in header

    return cnf, blocks


def decode_model(model_lits: set[int], blocks: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    return [B for i, B in enumerate(blocks) if (i + 1) in model_lits]


# ---------------------------------------------------------------- tiny DPLL (selfcheck only)


def dpll(clauses: list[tuple[int, ...]], nvars: int) -> set[int] | None:
    """Unit-propagating DPLL.  Selfcheck arms only — the box uses cadical+DRAT."""
    assign: dict[int, bool] = {}

    def value(l: int):
        va = assign.get(abs(l))
        return None if va is None else (va if l > 0 else not va)

    def propagate(cl):
        changed = True
        while changed:
            changed = False
            for c in cl:
                unassigned, sat = [], False
                for l in c:
                    x = value(l)
                    if x is True:
                        sat = True
                        break
                    if x is None:
                        unassigned.append(l)
                if sat:
                    continue
                if not unassigned:
                    return False
                if len(unassigned) == 1:
                    l = unassigned[0]
                    assign[abs(l)] = l > 0
                    changed = True
        return True

    def solve():
        if not propagate(clauses):
            return False
        free = next((i for i in range(1, nvars + 1) if i not in assign), None)
        if free is None:
            return True
        snap = dict(assign)
        for val in (True, False):
            assign.clear()
            assign.update(snap)
            assign[free] = val
            if solve():
                return True
        assign.clear()
        assign.update(snap)
        return False

    if not solve():
        return None
    return {(+i if assign.get(i, False) else -i) for i in range(1, nvars + 1)}


def assignment_satisfies(cnf: CNF, true_vars: set[int]) -> tuple[bool, int]:
    """Check a FULL assignment (vars in true_vars true, all else false) against every clause."""
    for idx, c in enumerate(cnf.clauses):
        if not any((l > 0 and l in true_vars) or (l < 0 and -l not in true_vars) for l in c):
            return False, idx
    return True, -1


def chain_counter_assignment(blocks_true: list[int], n: int, b: int) -> set[int]:
    """The counter assignment forced by a given block set: s[i][j] = [count(x_1..x_i) >= j]."""
    true_vars = set(blocks_true)
    count = 0
    var = n
    s_val: dict[tuple[int, int], bool] = {}
    for i in range(1, n + 1):
        if i in true_vars:
            count += 1
        for j in range(1, b + 1):
            var += 1
            s_val[(i, j)] = count >= j
            if s_val[(i, j)]:
                true_vars.add(var)
    return true_vars


# ---------------------------------------------------------------- brute force (selfcheck only)


def brute_cover_exists(v: int, k: int, t: int, b: int) -> bool:
    bl = blocks_of(v, k)
    ts = set(tsets_of(v, t))
    for combo in itertools.combinations(range(len(bl)), b):
        covered = set()
        for i in combo:
            covered.update(itertools.combinations(bl[i], t))
        if ts <= covered:
            return True
    return False


# ---------------------------------------------------------------- selfcheck


FANO = [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6)]


def selfcheck() -> int:
    green = 0

    def arm(name: str, ok: bool, detail: str):
        nonlocal green
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}: {detail}")
        if not ok:
            print("SELFCHECK RED — do not emit for the box.")
            sys.exit(1)
        green += 1

    # arm 1: C(4,3,2) both directions, DPLL vs brute force, decoded model verified
    for b, want in ((3, True), (2, False)):
        brute = brute_cover_exists(4, 3, 2, b)
        cnf, blocks = encode(4, 3, 2, b, wlog=False)
        model = dpll(cnf.clauses, cnf.nvars)
        agree = (model is not None) == brute == want
        detail = f"b={b}: brute={brute} dpll={'SAT' if model else 'UNSAT'}"
        if model is not None:
            cover = decode_model({l for l in model if l > 0}, blocks)
            okv, msg = verify_cover(4, 3, 2, cover)
            agree = agree and okv and len(cover) <= b
            detail += f"; decoded {len(cover)} blocks, verify_cover: {msg}"
        arm(f"C(4,3,2) b={b}", agree, detail)

    # arm 2: C(7,3,2) b=6 UNSAT (counting: 6*3=18 < 21 pairs) — encoder must agree
    cnf, _ = encode(7, 3, 2, 6, wlog=False)
    model = dpll(cnf.clauses, cnf.nvars)
    arm("C(7,3,2) b=6 UNSAT", model is None,
        f"counting bound says UNSAT; dpll={'SAT' if model else 'UNSAT'} "
        f"({cnf.nvars} vars, {len(cnf.clauses)} clauses)")

    # arm 3: Fano positive control — the 7 lines satisfy every clause at b=7
    cnf, blocks = encode(7, 3, 2, 7, wlog=False)
    fano_vars = [blocks.index(B) + 1 for B in FANO]
    true_vars = chain_counter_assignment(fano_vars, len(blocks), 7)
    ok, bad = assignment_satisfies(cnf, true_vars)
    arm("Fano satisfies C(7,3,2) b=7", ok, f"7 lines checked against {len(cnf.clauses)} clauses"
        + ("" if ok else f"; first falsified clause #{bad}: {cnf.clauses[bad]}"))
    okv, msg = verify_cover(7, 3, 2, FANO)
    arm("Fano verify_cover", okv, msg)

    # arm 4: wlog soundness probe — C(4,3,2)@3 stays SAT with wlog on
    cnf, blocks = encode(4, 3, 2, 3, wlog=True)
    model = dpll(cnf.clauses, cnf.nvars)
    ok = model is not None
    if ok:
        cover = decode_model({l for l in model if l > 0}, blocks)
        okv, msg = verify_cover(4, 3, 2, cover)
        ok = okv and tuple(range(1, 4)) in cover
    arm("wlog keeps SAT and pins block {1,2,3}", ok, "relabeling argument, header §wlog")

    # arm 5: flagship determinism + stats
    a = encode(13, 6, 3, 20, wlog=True)[0].dimacs()
    bdim = encode(13, 6, 3, 20, wlog=True)[0].dimacs()
    sha_a = hashlib.sha256(a.encode()).hexdigest()
    ok = sha_a == hashlib.sha256(bdim.encode()).hexdigest()
    head = a.split("\n", 1)[0]
    arm("flagship C(13,6,3) b=20 deterministic", ok,
        f"{head}; {len(a)} bytes; sha256 {sha_a[:16]}…")

    print(f"SELFCHECK ALL GREEN — {green}/{green} arms.")
    return 0


# ---------------------------------------------------------------- CLI


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--selfcheck", action="store_true")
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--decode", action="store_true")
    ap.add_argument("--check-cover", action="store_true")
    ap.add_argument("--v", type=int, default=13)
    ap.add_argument("--k", type=int, default=6)
    ap.add_argument("--t", type=int, default=3)
    ap.add_argument("--b", type=int, default=20)
    ap.add_argument("--no-wlog", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--cnf")
    ap.add_argument("--model", help="solver output file holding 'v ...' model lines")
    ap.add_argument("--blocks", help="JSON file: list of point lists")
    args = ap.parse_args()

    if args.selfcheck:
        return selfcheck()

    if args.emit:
        cnf, blocks = encode(args.v, args.k, args.t, args.b, wlog=not args.no_wlog)
        text = cnf.dimacs()
        sha = hashlib.sha256(text.encode()).hexdigest()
        out = args.out or f"c{args.v}-{args.k}-{args.t}-b{args.b}.cnf"
        os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
        with open(out, "w") as f:
            f.write(text)
        receipt = {
            "tool": "cover_sat.py", "question": f"exists <= {args.b}-block C({args.v},{args.k},{args.t}) cover",
            "vars": cnf.nvars, "clauses": len(cnf.clauses), "bytes": len(text),
            "block_vars": len(blocks), "wlog": not args.no_wlog, "sha256": sha,
            "verdict_law": "UNSAT counts only after drat-trim verifies; SAT counts only after verify_cover() on the decoded blocks",
        }
        with open(out + ".receipt.json", "w") as f:
            json.dump(receipt, f, indent=2)
        print(json.dumps(receipt, indent=2))
        return 0

    if args.decode:
        blocks = blocks_of(args.v, args.k)
        lits: set[int] = set()
        with open(args.model) as f:
            for line in f:
                if line.startswith("v"):
                    lits.update(int(x) for x in line.split()[1:] if x != "0")
        cover = decode_model({l for l in lits if l > 0}, blocks)
        ok, msg = verify_cover(args.v, args.k, args.t, cover)
        print(json.dumps({"blocks": [list(B) for B in cover], "count": len(cover),
                          "verified_from_definition": ok, "detail": msg}, indent=2))
        return 0 if ok else 1

    if args.check_cover:
        with open(args.blocks) as f:
            cover = [tuple(sorted(B)) for B in json.load(f)]
        ok, msg = verify_cover(args.v, args.k, args.t, cover)
        print(json.dumps({"count": len(cover), "verified_from_definition": ok, "detail": msg}))
        return 0 if ok else 1

    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
