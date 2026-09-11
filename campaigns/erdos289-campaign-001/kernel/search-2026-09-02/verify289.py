"""
Erdos 289 -- INDEPENDENT verifier + naive enumerator.  Fresh code path.

Nothing here shares a line, a table or an idea with search289.py:
  * search289.py works in the integer ring after clearing by lcm(2..B) and
    prunes with prefix/gap/lcm-divisibility tables.
  * this file works directly in Q with fractions.Fraction and prunes with
    nothing but "the running sum already exceeds the target".

Modes
  --check  '[[2,3],[7,8]]'      verify one candidate decomposition exactly
  --enum   --k K --B B          enumerate EVERY decomposition (naive, small B)
"""
import argparse
import json
from fractions import Fraction


def block_sum(a, b):
    s = Fraction(0)
    for n in range(a, b + 1):
        s += Fraction(1, n)
    return s


def check(blocks, target=Fraction(1), verbose=True):
    """Exact structural + arithmetic verification of one decomposition."""
    errs = []
    bs = [tuple(x) for x in blocks]
    if len(set(bs)) != len(bs):
        errs.append("blocks not pairwise distinct")
    srt = sorted(bs)
    if srt != bs:
        if verbose:
            print("note: blocks were not given sorted; verifying sorted order")
    for (a, b) in srt:
        if a < 2:
            errs.append("block [%d,%d] starts below 2" % (a, b))
        if b - a + 1 < 2:
            errs.append("block [%d,%d] has length < 2" % (a, b))
    for i in range(1, len(srt)):
        pa, pb = srt[i - 1]
        na, nb = srt[i]
        if na < pb + 2:
            errs.append(
                "blocks [%d,%d] and [%d,%d] overlap or are ADJACENT (need next.a >= prev.b+2)"
                % (pa, pb, na, nb)
            )
    total = Fraction(0)
    for (a, b) in srt:
        total += block_sum(a, b)
    if total != target:
        errs.append("sum is %s, not %s" % (total, target))
    ok = not errs
    if verbose:
        print("blocks   :", srt)
        print("k        :", len(srt))
        print("exact sum:", total)
        print("target   :", target)
        for e in errs:
            print("ERROR    :", e)
        print("VERDICT  :", "VERIFIED" if ok else "REJECTED")
    return ok, total, errs


def enumerate_all(k, B, target=Fraction(1), cap=None):
    """Every k-block decomposition with all elements in [2,B].  Naive."""
    out = []

    def rec(s, rem, j, acc):
        if j == 0:
            if rem == 0:
                out.append(list(acc))
            return
        for a in range(s, B):
            cur = Fraction(0)
            for b in range(a, B + 1):
                cur += Fraction(1, b)
                if b == a:
                    continue  # length >= 2 required
                if cur > rem:
                    break
                acc.append((a, b))
                rec(b + 2, rem - cur, j - 1, acc)
                acc.pop()
                if cap and len(out) >= cap:
                    return

    rec(2, target, k, [])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", default=None, help="JSON list of [a,b] blocks")
    ap.add_argument("--enum", action="store_true")
    ap.add_argument("--k", type=int, default=None)
    ap.add_argument("--B", type=int, default=None)
    ap.add_argument("--tnum", type=int, default=1)
    ap.add_argument("--tden", type=int, default=1)
    args = ap.parse_args()
    target = Fraction(args.tnum, args.tden)
    if args.check:
        blocks = json.loads(args.check)
        ok, total, errs = check(blocks, target)
        raise SystemExit(0 if ok else 1)
    if args.enum:
        sols = enumerate_all(args.k, args.B, target)
        print("k=%d B=%d target=%s -> %d decompositions" % (args.k, args.B, target, len(sols)))
        for s in sols[:20]:
            print("   ", s)
        raise SystemExit(0)
    ap.error("choose --check or --enum")


if __name__ == "__main__":
    main()
